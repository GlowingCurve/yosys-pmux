#include "passes/opt/pmux_decoder.h"

YOSYS_NAMESPACE_BEGIN
namespace {

bool comparison_type(IdString type)
{
	return type.in(ID($eq), ID($ne), ID($logic_not));
}

int comparison_width(const PmuxNetlist &netlist, Cell *cell)
{
	int width = GetSize(netlist.port(cell, ID::A));
	if (cell->type != ID($logic_not))
		width = std::max(width, GetSize(netlist.port(cell, ID::B)));
	return width;
}

enum class Constraints { Exact, Relational, Undefined };

Constraints comparison_cube(const PmuxNetlist &netlist, Cell *cell, int width, PmuxDecoder::Cube &cube)
{
	auto a = netlist.extended(cell, ID::A, width);
	auto b = cell->type == ID($logic_not) ? SigSpec(State::S0, width) : netlist.extended(cell, ID::B, width);
	auto constraints = Constraints::Exact;
	for (int i = 0; i < width; ++i) {
		auto x = a[i], y = b[i];
		if ((!x.wire && x.data > State::S1) || (!y.wire && y.data > State::S1)) {
			constraints = Constraints::Undefined;
			continue;
		}
		if (x == y)
			continue;
		if (x.wire && y.wire) {
			if (constraints == Constraints::Exact)
				constraints = Constraints::Relational;
			continue;
		}
		if (!x.wire)
			std::swap(x, y);
		bool value = y == State::S1;
		if (x.wire) {
			auto binding = cube.bits.insert(std::make_pair(x, value));
			if (binding.second || binding.first->second == value)
				continue;
		}
		cube.dead = true;
		cube.bits.clear();
		return Constraints::Exact;
	}
	return constraints;
}

bool spend(int &budget, int work)
{
	log_assert(budget >= 0 && work >= 0);
	budget -= work;
	return budget >= 0;
}

} // namespace

PmuxDecoder::PmuxDecoder(const PmuxNetlist &netlist) : netlist(netlist), cache_revision(netlist.revision())
{
}

bool PmuxDecoder::decode(SigBit bit, Cube &cube, bool allow_inequalities, bool allow_literal) const
{
	bit = netlist.sigmap()(bit);
	Cube decoded;
	if (!bit.wire) {
		if (bit.data > State::S1)
			return false;
		decoded.dead = bit == State::S0;
	} else {
		auto source = netlist.source(bit);
		if (!source)
			return false;
		auto cell = source->cell;
		if (!cell || !comparison_type(cell->type)) {
			if (!allow_literal)
				return false;
			decoded.bits[bit] = true;
		} else {
			if (cell->type == ID($ne) && !allow_inequalities)
				return false;
			log_assert(source->port == ID::Y);
			decoded.cell = cell;
			if (source->offset > 0) {
				decoded.dead = true;
			} else {
				int width = comparison_width(netlist, cell);
				decoded.inverted = cell->type == ID($ne);
				if (width > 256 || comparison_cube(netlist, cell, width, decoded) != Constraints::Exact)
					return false;
			}
		}
	}
	cube = std::move(decoded);
	return true;
}

bool PmuxDecoder::table(Cell *cell, Table &result) const
{
	log_assert(cell);
	if (cell->type != ID($pmux))
		return false;
	const auto &select = netlist.port(cell, ID::S);
	if (GetSize(select) < 2 || GetSize(select) > 16)
		return false;
	std::vector<Cube> cubes(GetSize(select));
	for (int i = 0; i < GetSize(select); ++i)
		if (!decode(select[i], cubes[i]))
			return false;
	return table(cell, cubes, result);
}

bool PmuxDecoder::table(Cell *cell, const std::vector<Cube> &cubes, Table &result) const
{
	log_assert(cell && cell->type == ID($pmux));
	int branches = GetSize(netlist.port(cell, ID::S));
	log_assert(GetSize(cubes) == branches);
	if (branches < 2 || branches > 16)
		return false;
	int width = GetSize(cubes.front().bits);
	for (const auto &cube : cubes)
		if (cube.dead || cube.inverted || GetSize(cube.bits) != width)
			return false;

	Table decoded;
	std::vector<SigBit> controls;
	for (const auto &literal : cubes.front().bits) {
		bool common = true;
		for (const auto &cube : cubes) {
			auto found = cube.bits.find(literal.first);
			if (found == cube.bits.end())
				return false;
			common &= found->second == literal.second;
		}
		if (common)
			decoded.prefix.push_back(literal);
		else
			controls.push_back(literal.first);
	}
	int address_width = GetSize(controls);
	if (address_width < 1 || address_width > 4)
		return false;
	int codes = 1 << address_width;
	if (branches != codes && branches != codes - 1)
		return false;
	std::sort(controls.begin(), controls.end());
	decoded.control = SigSpec(controls);
	decoded.branch_for_code.assign(codes, -1);

	const auto &fallback = netlist.port(cell, ID::A);
	const auto &data = netlist.port(cell, ID::B);
	int row_width = GetSize(fallback);
	log_assert(GetSize(data) == int64_t(row_width) * branches);
	decoded.data.assign(codes, fallback);
	decoded.region.insert(cell);
	for (int i = 0; i < branches; ++i) {
		const auto &cube = cubes[i];
		int code = 0;
		for (int j = 0; j < address_width; ++j)
			if (cube.bits.at(controls[j]))
				code |= 1 << j;
		if (decoded.branch_for_code[code] != -1)
			return false;
		decoded.branch_for_code[code] = i;
		decoded.data[code] = data.extract(i * row_width, row_width);
		if (cube.cell)
			decoded.region.insert(cube.cell);
	}
	decoded.cell = cell;
	decoded.cubes = cubes;
	result = std::move(decoded);
	return true;
}

bool PmuxDecoder::infer(SigBit bit, bool value, dict<SigBit, State> &facts, Assumptions &pending, int &budget) const
{
	if (!spend(budget, 1))
		return false;
	State state = value ? State::S1 : State::S0;
	if (!bit.wire)
		return bit == state;
	auto source = netlist.source(bit);
	if (!source)
		return true;
	auto binding = facts.insert(std::make_pair(bit, state));
	if (!binding.second)
		return binding.first->second == state;
	auto cell = source->cell;
	if (!cell || source->port != ID::Y)
		return true;

	IdString type = cell->type;
	int offset = source->offset;
	if (comparison_type(type)) {
		if (offset > 0)
			return !value;
		int width = comparison_width(netlist, cell);
		if (!spend(budget, width))
			return false;
		Cube cube;
		auto constraints = comparison_cube(netlist, cell, width, cube);
		bool equal = value != (type == ID($ne));
		if (cube.dead)
			return !equal;
		if (equal) {
			if (constraints == Constraints::Undefined)
				return false;
			for (const auto &literal : cube.bits)
				pending.push_back(literal);
		} else if (constraints == Constraints::Exact) {
			if (cube.bits.empty())
				return false;
			if (GetSize(cube.bits) == 1) {
				const auto &literal = *cube.bits.begin();
				pending.emplace_back(literal.first, !literal.second);
			}
		}
		return true;
	}
	if (type == ID($not)) {
		pending.emplace_back(netlist.operand(cell, ID::A, offset), !value);
		return true;
	}

	auto reduce = [&pending](const SigSpec &inputs, bool conjunction, bool output) {
		if (output == conjunction) {
			for (auto input : inputs)
				pending.emplace_back(input, output);
			return true;
		}
		SigBit remaining;
		State controlling = output ? State::S1 : State::S0;
		for (auto input : inputs) {
			if (input == controlling)
				return true;
			if (!input.wire)
				continue;
			if (remaining.wire && remaining != input)
				return true;
			remaining = input;
		}
		if (!remaining.wire)
			return false;
		pending.emplace_back(remaining, output);
		return true;
	};
	if (type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool))) {
		if (offset > 0)
			return !value;
		const auto &a = netlist.port(cell, ID::A);
		return spend(budget, GetSize(a)) && reduce(a, type == ID($reduce_and), value);
	}
	if (type.in(ID($logic_and), ID($logic_or))) {
		if (offset > 0)
			return !value;
		const auto &a = netlist.port(cell, ID::A);
		const auto &b = netlist.port(cell, ID::B);
		if (!spend(budget, GetSize(a) + GetSize(b)))
			return false;
		bool conjunction = type == ID($logic_and);
		if (GetSize(a) == 1 && GetSize(b) == 1)
			return reduce(SigSpec({a[0], b[0]}), conjunction, value);
		if (value == conjunction)
			return reduce(a, false, value) && reduce(b, false, value);
		return true;
	}
	if (type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
		auto a = netlist.operand(cell, ID::A, offset), b = netlist.operand(cell, ID::B, offset);
		if (type.in(ID($and), ID($or)))
			return reduce(SigSpec({a, b}), type == ID($and), value);
		if (!a.wire)
			std::swap(a, b);
		bool inverted = type == ID($xnor);
		if (b.wire)
			return a != b || value == inverted;
		if (b.data > State::S1)
			return false;
		pending.emplace_back(a, value ^ (b == State::S1) ^ inverted);
	}
	return true;
}

bool PmuxDecoder::condition(SigBit bit, bool value, dict<SigBit, State> &facts, int &budget)
{
	log_assert(facts.empty());
	if (budget < 0)
		return false;
	if (cache_revision != netlist.revision()) {
		condition_cache.clear();
		cached_facts = 0;
		cache_revision = netlist.revision();
	}
	bit = netlist.sigmap()(bit);
	auto key = std::make_pair(bit, value);
	auto cached = condition_cache.find(key);
	if (cached != condition_cache.end()) {
		if (!spend(budget, 1 + GetSize(cached->second.facts)) || !cached->second.possible)
			return false;
		facts = cached->second.facts;
		return true;
	}

	Assumptions pending = {{bit, value}};
	bool possible = true;
	while (possible && !pending.empty()) {
		auto assumption = pending.back();
		pending.pop_back();
		possible = infer(assumption.first, assumption.second, facts, pending, budget);
	}
	if (!possible)
		facts.clear();
	if (budget >= 0 && GetSize(condition_cache) < 64 && cached_facts + GetSize(facts) <= 4096) {
		condition_cache.insert({key, {facts, possible}});
		cached_facts += GetSize(facts);
	}
	return possible;
}

YOSYS_NAMESPACE_END
