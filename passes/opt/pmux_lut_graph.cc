#include "passes/opt/pmux_lut_graph.h"

YOSYS_NAMESPACE_BEGIN

namespace {

int assignment_value(const std::vector<int> &inputs, int assignment, int id)
{
	if (id < 2) return id;
	auto pos = std::lower_bound(inputs.begin(), inputs.end(), id);
	log_assert(pos != inputs.end() && *pos == id);
	return (assignment >> (pos-inputs.begin())) & 1;
}

void configure_intel_lut(Cell *cell, SigSpec inputs, SigBit output, const Const &table)
{
	int width = GetSize(inputs);
	log_assert(width >= 1 && width <= 4 && GetSize(table) == (1 << width));
	Const mask;
	for (int i = 0; i < (1 << (4-width)); i++) mask.append(table);
	inputs.extend_u0(4);
	cell->setParam(ID(lut_mask), mask);
	cell->setParam(ID(sum_lutc_input), Const("datac"));
	cell->setPort(ID(dataa), inputs[0]);
	cell->setPort(ID(datab), inputs[1]);
	cell->setPort(ID(datac), inputs[2]);
	cell->setPort(ID(datad), inputs[3]);
	cell->setPort(ID(cin), State::S0);
	cell->setPort(ID(combout), output);
}

}

PmuxLutGraph::PmuxLutGraph(Expansion expansion, int node_limit) : expansion(expansion), node_limit(node_limit)
{
	log_assert(node_limit >= 2);
}

int PmuxLutGraph::append(Node node)
{
	if (node_count() == node_limit) {
		overflow = true;
		return 0;
	}
	int id = node_count();
	nodes.push_back(std::move(node));
	return id;
}

int PmuxLutGraph::leaf(SigBit bit)
{
	if (bit == State::S0 || bit == State::S1) return bit == State::S1;
	auto found = leaves.find(bit);
	if (found != leaves.end()) return found->second;
	int id = append({bit, {}, 0, true});
	if (id != 0) leaves.emplace(bit, id);
	return id;
}

std::vector<int> PmuxLutGraph::bits(const SigSpec &value)
{
	std::vector<int> result;
	result.reserve(value.size());
	for (auto bit : value) result.push_back(leaf(bit));
	return result;
}

const PmuxLutGraph::Node &PmuxLutGraph::node(int id) const
{
	log_assert(id >= 0 && id < node_count());
	return nodes[id];
}

PmuxLutGraph::Function PmuxLutGraph::normalize(const std::vector<int> &args, uint16_t mask) const
{
	log_assert(GetSize(args) <= 4);
	std::vector<int> inputs;
	for (int arg : args) {
		log_assert(arg >= 0 && arg < node_count());
		if (arg > 1) inputs.push_back(arg);
	}
	std::sort(inputs.begin(), inputs.end());
	inputs.erase(std::unique(inputs.begin(), inputs.end()), inputs.end());
	uint16_t table = 0;
	for (int assignment = 0; assignment < (1 << GetSize(inputs)); assignment++) {
		int original = 0;
		for (int i = 0; i < GetSize(args); i++)
			original |= assignment_value(inputs, assignment, args[i]) << i;
		table |= ((mask >> original) & 1u) << assignment;
	}
	for (int i = GetSize(inputs)-1; i >= 0; i--) {
		int variable = 1 << i;
		uint16_t low = 0, high = 0;
		for (int assignment = 0; assignment < (1 << (GetSize(inputs)-1)); assignment++) {
			int original = (assignment & (variable-1)) | ((assignment & ~(variable-1)) << 1);
			low |= ((table >> original) & 1u) << assignment;
			high |= ((table >> (original | variable)) & 1u) << assignment;
		}
		if (low == high) {
			inputs.erase(inputs.begin()+i);
			table = low;
		}
	}
	return {std::move(inputs), table};
}

int PmuxLutGraph::find(const Function &function) const
{
	const auto &[inputs, mask] = function;
	if (inputs.empty()) return mask;
	if (GetSize(inputs) == 1 && mask == 2) return inputs.front();
	auto found = functions.find(function);
	return found == functions.end() ? -1 : found->second;
}

int PmuxLutGraph::intern(Function function)
{
	int existing = find(function);
	if (existing >= 0) return existing;
	int id = append({{}, function.first, function.second, false});
	if (id != 0) functions.emplace(std::move(function), id);
	return id;
}

int PmuxLutGraph::lut(const std::vector<int> &args, uint16_t mask)
{
	return intern(normalize(args, mask));
}

bool PmuxLutGraph::expand(const Function &function, unsigned selected, Function &result) const
{
	const auto &[args, mask] = function;
	std::vector<int> inputs;
	for (int i = 0; i < GetSize(args); i++) {
		if (selected & (1u << i)) {
			const auto &child = node(args[i]);
			log_assert(!child.leaf);
			inputs.insert(inputs.end(), child.inputs.begin(), child.inputs.end());
		} else {
			inputs.push_back(args[i]);
		}
	}
	std::sort(inputs.begin(), inputs.end());
	inputs.erase(std::unique(inputs.begin(), inputs.end()), inputs.end());
	if (GetSize(inputs) > 4) return false;
	uint16_t table = 0;
	for (int assignment = 0; assignment < (1 << GetSize(inputs)); assignment++) {
		int original = 0;
		for (int i = 0; i < GetSize(args); i++) {
			int value;
			if (selected & (1u << i)) {
				const auto &child = node(args[i]);
				int index = 0;
				for (int j = 0; j < GetSize(child.inputs); j++)
					index |= assignment_value(inputs, assignment, child.inputs[j]) << j;
				value = (child.mask >> index) & 1;
			} else {
				value = assignment_value(inputs, assignment, args[i]);
			}
			original |= value << i;
		}
		table |= ((mask >> original) & 1u) << assignment;
	}
	result = normalize(inputs, table);
	return true;
}

int PmuxLutGraph::candidate_cost(const Function &function) const
{
	int existing = find(function);
	return existing >= 0 ? cost({existing}) : 1 + cost(function.first);
}

int PmuxLutGraph::gate(const std::vector<int> &args, uint16_t mask)
{
	Function base = normalize(args, mask);
	if (expansion == Expansion::None) return intern(std::move(base));
	unsigned expandable = 0;
	for (int i = 0; i < GetSize(base.first); i++)
		if (!node(base.first[i]).leaf) expandable |= 1u << i;
	if (expandable == 0) return intern(std::move(base));
	Function candidate;
	if (expansion == Expansion::All) {
		if (expand(base, expandable, candidate)) return intern(std::move(candidate));
		return intern(std::move(base));
	}
	Function best = base;
	int best_cost = candidate_cost(best);
	for (unsigned selected = 1; selected <= expandable; selected++) {
		if ((selected & expandable) != selected || !expand(base, selected, candidate)) continue;
		int cost = candidate_cost(candidate);
		if (cost < best_cost) {
			best_cost = cost;
			best = std::move(candidate);
		}
	}
	return intern(std::move(best));
}

int PmuxLutGraph::invert(int id)
{
	const auto &source = node(id);
	if (source.leaf) return lut({id}, 1);
	unsigned all_rows = (1u << (1 << GetSize(source.inputs)))-1;
	return lut(source.inputs, source.mask ^ all_rows);
}

int PmuxLutGraph::mux(int low, int high, int select)
{
	return gate({low, high, select}, 0xca);
}

int PmuxLutGraph::select(const std::vector<int> &values, const std::vector<int> &control, int level, size_t prefix)
{
	if (level == GetSize(control)) return values[prefix];
	int high = select(values, control, level+1, prefix | (size_t(1) << level));
	int low = select(values, control, level+1, prefix);
	return mux(low, high, control[level]);
}

int PmuxLutGraph::select(const std::vector<int> &values, const std::vector<int> &control)
{
	log_assert(control.size() < std::numeric_limits<size_t>::digits);
	log_assert(values.size() == (size_t(1) << control.size()));
	return select(values, control, 0, 0);
}

int PmuxLutGraph::reduce(std::vector<int> values, bool conjunction)
{
	if (values.empty()) return conjunction;
	while (GetSize(values) > 1) {
		std::vector<int> next;
		for (int i = 0; i < GetSize(values); i += 4) {
			std::vector<int> group(values.begin()+i, values.begin()+std::min(i+4, GetSize(values)));
			uint16_t mask = conjunction ? 1u << ((1 << GetSize(group))-1) : 0xfffe;
			next.push_back(gate(group, mask));
		}
		values.swap(next);
	}
	return values.front();
}

std::vector<int> PmuxLutGraph::add(const std::vector<int> &a, const std::vector<int> &b, int carry)
{
	log_assert(a.size() == b.size());
	std::vector<int> result;
	result.reserve(a.size());
	for (int i = 0; i < GetSize(a); i++) {
		result.push_back(gate({a[i], b[i], carry}, 0x96));
		if (i+1 < GetSize(a)) carry = gate({a[i], b[i], carry}, 0xe8);
	}
	return result;
}

std::vector<int> PmuxLutGraph::sum3(const std::vector<int> &a, const std::vector<int> &b, const std::vector<int> &c)
{
	log_assert(a.size() == b.size() && a.size() == c.size());
	std::vector<int> sum, carry(a.size(), 0);
	sum.reserve(a.size());
	for (int i = 0; i < GetSize(a); i++) {
		sum.push_back(gate({a[i], b[i], c[i]}, 0x96));
		if (i+1 < GetSize(a)) carry[i+1] = gate({a[i], b[i], c[i]}, 0xe8);
	}
	return add(sum, carry);
}

pool<int> PmuxLutGraph::live(const std::vector<int> &roots) const
{
	pool<int> used;
	auto pending = roots;
	while (!pending.empty()) {
		int id = pending.back();
		pending.pop_back();
		if (used.insert(id).second) {
			const auto &inputs = node(id).inputs;
			pending.insert(pending.end(), inputs.begin(), inputs.end());
		}
	}
	return used;
}

pool<SigBit> PmuxLutGraph::referenced(const std::vector<int> &roots) const
{
	pool<SigBit> result;
	cost(roots, result);
	return result;
}

int PmuxLutGraph::cost(const std::vector<int> &roots) const
{
	auto used = live(roots);
	return std::count_if(used.begin(), used.end(), [&](int id) { return !node(id).leaf; });
}

int PmuxLutGraph::cost(const std::vector<int> &roots, pool<SigBit> &referenced) const
{
	int result = 0;
	for (int id : live(roots)) {
		const auto &entry = node(id);
		if (entry.leaf) referenced.insert(entry.bit);
		else result++;
	}
	return result;
}

int PmuxLutGraph::incremental_cost(const std::vector<int> &roots, const pool<int> &covered) const
{
	auto used = live(roots);
	return std::count_if(used.begin(), used.end(), [&](int id) { return !node(id).leaf && !covered.count(id); });
}

SigSpec PmuxLutGraph::emit(Module *module, IdString celltype, const std::vector<int> &roots) const
{
	log_assert(module && !overflow);
	auto used = live(roots);
	std::vector<SigBit> signals(nodes.size());
	for (int id = 0; id < node_count(); id++) {
		if (!used.count(id)) continue;
		const auto &entry = node(id);
		if (entry.leaf) {
			signals[id] = entry.bit;
			continue;
		}
		SigSpec inputs;
		for (int input : entry.inputs) inputs.append(signals[input]);
		Const table(entry.mask, 1 << GetSize(inputs));
		SigBit output(module->addWire(NEW_ID));
		if (celltype.empty()) module->addLut(NEW_ID, inputs, output, table);
		else configure_intel_lut(module->addCell(NEW_ID, celltype), inputs, output, table);
		signals[id] = output;
	}
	SigSpec result;
	for (int id : roots) result.append(signals[id]);
	return result;
}

void PmuxLutGraph::map_intel_lut(Cell *cell, IdString celltype)
{
	log_assert(cell && cell->module && cell->type == ID($lut) && !celltype.empty());
	if (cell->parameters.size() != 2 || !cell->hasParam(ID::WIDTH) || !cell->hasParam(ID::LUT))
		log_error("Invalid LUT parameters for %s.%s.\n", log_id(cell->module), log_id(cell));
	const auto &width_parameter = cell->getParam(ID::WIDTH);
	if (!width_parameter.is_fully_def() || !width_parameter.convertible_to_int())
		log_error("Invalid LUT width for %s.%s.\n", log_id(cell->module), log_id(cell));
	int width = width_parameter.as_int();
	if (width < 1 || width > 4)
		log_error("Unsupported LUT width %d for %s.%s.\n", width, log_id(cell->module), log_id(cell));
	if (cell->connections().size() != 2 || !cell->hasPort(ID::A) || !cell->hasPort(ID::Y) ||
		GetSize(cell->getPort(ID::A)) != width || GetSize(cell->getPort(ID::Y)) != 1)
		log_error("Invalid LUT ports for %s.%s.\n", log_id(cell->module), log_id(cell));
	SigSpec inputs = cell->getPort(ID::A);
	SigBit output = cell->getPort(ID::Y).as_bit();
	Const table = cell->getParam(ID::LUT).extract(0, 1 << width);
	cell->unsetPort(ID::A);
	cell->unsetPort(ID::Y);
	cell->parameters.clear();
	if (width == 1 && table == Const(1, 2)) {
		cell->type = ID($not);
		cell->setParam(ID::A_SIGNED, false);
		cell->setParam(ID::A_WIDTH, 1);
		cell->setParam(ID::Y_WIDTH, 1);
		cell->setPort(ID::A, inputs);
		cell->setPort(ID::Y, output);
	} else {
		cell->type = celltype;
		configure_intel_lut(cell, inputs, output, table);
	}
}

YOSYS_NAMESPACE_END
