// opt_pmuxarith 共享 PMUX 分支中的加减、比较及常量除模运算，并生成四输入 LUT 网络。
// 在操作数选择、进位和余数计算之间共享节点，减少重复算术与选择逻辑。
#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "kernel/utils.h"
#include "passes/opt/pmux_lut_graph.h"
#include "passes/opt/pmux_netlist.h"
#include <array>
#include <functional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxArithWorker {
	Module *module;
	PmuxNetlist netlist;
	IdString luttype;
	int budget = 20000;
	PmuxArithWorker(Module *module, Design *design, IdString luttype) :
		module(module), netlist(module, design), luttype(luttype) {}
	SigSpec without_zero_extension(SigSpec value) const
	{
		while (!value.empty() && value.back() == State::S0)
			value.remove(GetSize(value)-1);
		return value;
	}
	Cell *root(const SigSpec &value) const {
		if (value.empty()) return nullptr;
		auto cell = netlist.driver(value[0]);
		if (!cell || !netlist.editable(cell)) return nullptr;
		const auto &y = netlist.port(cell, ID::Y);
		int n = std::min(GetSize(y),GetSize(value));
		if (value.extract(0,n) != y.extract(0,n)) return nullptr;
		for (int i = n; i < GetSize(value); i++) if (value[i] != State::S0) return nullptr;
		return cell;
	}
	int old_cost(Cell *cell) const {
		int width = GetSize(cell->getPort(ID::Y));
		if (cell->type.in(ID($add),ID($sub))) return std::max(0,2*width-1);
		if (cell->type == ID($pmux)) return width * GetSize(cell->getPort(ID::S));
		if (cell->type.in(ID($div),ID($mod))) return width*width;
		if (cell->type.in(ID($eq),ID($ne),ID($lt),ID($gt))) return std::max(GetSize(cell->getPort(ID::A)),GetSize(cell->getPort(ID::B)));
		return width;
	}
	bool commit_outputs(const std::vector<Cell *> &roots, const pool<Cell *> &region,
			const PmuxLutGraph &network, const std::vector<int> &outputs)
	{
		pool<SigBit> leaves;
		int cost = network.cost(outputs, leaves);
		pool<SigBit> targets;
		int width = 0;
		for (auto cell : roots) {
			log_assert(netlist.editable(cell));
			const auto &y = netlist.port(cell, ID::Y);
			targets.insert(y.begin(), y.end());
			width += GetSize(y);
		}
		log_assert(width == GetSize(outputs) && width == GetSize(targets));
		if (!netlist.independent(leaves, targets, budget)) return false;
		auto removed = netlist.private_cells(region, {roots.begin(), roots.end()}, targets, leaves);
		for (auto cell : roots)
			log_assert(removed.count(cell));
		int old = 0, operators = 0;
		dict<SigSpec, int> divcost;
		for (auto cell : removed) {
			if (cell->type.in(ID($add), ID($sub), ID($div), ID($mod), ID($lt), ID($gt)) ||
				(cell->type == ID($eq) && !netlist.port(cell, ID::A).is_fully_const() && !netlist.port(cell, ID::B).is_fully_const()))
				operators++;
			if (cell->type.in(ID($div), ID($mod))) {
				auto input = without_zero_extension(netlist.port(cell, ID::A));
				auto &cost = divcost[input];
				cost = std::max(cost, GetSize(input)*GetSize(input));
			} else {
				old += old_cost(cell);
			}
		}
		for (auto &item : divcost)
			old += item.second;
		if (operators < 2 || cost >= old) return false;
		int before = module->cells_size();
		auto emitted = network.emit(module, luttype, outputs);
		int emitted_cells = module->cells_size() - before;
		log_assert(emitted_cells == cost);
		log_debug("PMUX arithmetic commit: reference=%d candidate=%d removed=%d emitted=%d.\n",
			old, cost, GetSize(removed), emitted_cells);
		int offset = 0;
		for (auto cell : roots) {
			auto port = cell->getPort(ID::Y);
			module->connect(port, emitted.extract(offset, GetSize(port)));
			offset += GetSize(port);
		}
		for (auto cell : removed) module->remove(cell);
		return true;
	}
	bool control_operator(IdString type) const
	{
		return type.in(ID($eq), ID($logic_not), ID($not), ID($and), ID($or), ID($xor), ID($reduce_or), ID($reduce_bool));
	}
	bool control_support(SigBit bit, pool<SigBit> &support, pool<Cell *> &region, int depth = 0) {
		if (!bit.wire) return bit == State::S0 || bit == State::S1;
		if (--budget <= 0 || depth > 8) return false;
		auto cell = netlist.driver(bit);
		if (cell && control_operator(cell->type) && netlist.editable(cell)) {
			region.insert(cell);
			for (auto &port : cell->connections()) if (netlist.cell_input(cell->type, port.first)) {
				if (GetSize(port.second)>4) return false;
				for (auto in : netlist.port(cell, port.first)) if (!control_support(in,support,region,depth+1)) return false;
			}
			return true;
		}
		support.insert(bit);
		return GetSize(support) <= 2;
	}
	bool eval(SigBit bit, const dict<SigBit,bool> &values, bool &result, int depth = 0) {
		if (!bit.wire) {
			if (bit != State::S0 && bit != State::S1) return false;
			result = bit == State::S1;
			return true;
		}
		auto found = values.find(bit);
		if (found != values.end()) {
			result = found->second;
			return true;
		}
		if (depth > 8 || --budget <= 0) return false;
		auto source = netlist.source(bit);
		if (!source || !source->cell || source->port != ID::Y || !control_operator(source->cell->type)) return false;
		auto cell = source->cell;
		Const a, b;
		for (auto in : netlist.port(cell, ID::A)) {
			bool value;
			if (!eval(in, values, value, depth+1)) return false;
			a.append(value ? State::S1 : State::S0);
		}
		if (cell->hasPort(ID::B)) for (auto in : netlist.port(cell, ID::B)) {
			bool value;
			if (!eval(in, values, value, depth+1)) return false;
			b.append(value ? State::S1 : State::S0);
		}
		auto y = CellTypes::eval(cell, a, b);
		log_assert(source->offset >= 0 && source->offset < GetSize(y));
		result = y[source->offset] == State::S1;
		return true;
	}
	bool selected_branch(const SigSpec &s, const SigSpec &a, const SigSpec &b, int width,
			const dict<SigBit, bool> &values, SigSpec &branch)
	{
		int active = -1;
		for (int j = 0; j < GetSize(s); j++) {
			bool value;
			if (!eval(s[j], values, value)) return false;
			if (value) {
				if (active >= 0) return false;
				active = j;
			}
		}
		branch = active < 0 ? a : b.extract(active*width, width);
		return true;
	}
	struct ChoiceInfo {
		bool ready = false, valid = false;
		int work = 0;
		std::vector<SigSpec> branches;
		SigSpec control;
		pool<Cell *> region;
	};
	bool choice(Cell *pmux, std::vector<SigSpec> &branches, SigSpec &control, pool<Cell *> &region) {
		pool<SigBit> support;
		const auto &s = netlist.port(pmux, ID::S);
		if (s.empty() || GetSize(s)>4) return false;
		for (auto bit:s) if (!control_support(bit,support,region)) return false;
		if (support.empty() || GetSize(support)>2) return false;
		std::vector<SigBit> sorted(support.begin(), support.end());
		std::sort(sorted.begin(), sorted.end());
		control = SigSpec(sorted);
		const auto &a = netlist.port(pmux, ID::A), &b = netlist.port(pmux, ID::B);
		for (int code = 0; code < (1 << GetSize(control)); code++) {
			dict<SigBit, bool> values;
			for (int j = 0; j < GetSize(control); j++)
				values[control[j]] = (code >> j) & 1;
			SigSpec branch;
			if (!selected_branch(s, a, b, GetSize(a), values, branch)) return false;
			if (branch.is_fully_undef()) branch = b.extract(0, GetSize(a));
			for (auto bit : branch)
				if (!bit.wire && bit != State::S0 && bit != State::S1) return false;
			branches.push_back(branch);
		}
		return true;
	}
	bool choice(Cell *pmux, ChoiceInfo &info) {
		// 预算不足时执行原遍历，保留首次耗尽位置。
		if (info.ready && budget > info.work) {
			budget -= info.work;
			return info.valid;
		}
		int before = budget;
		ChoiceInfo next;
		next.valid = choice(pmux, next.branches, next.control, next.region);
		next.work = before - budget;
		next.ready = true;
		info = std::move(next);
		return info.valid;
	}
	using Polynomial = dict<SigSpec,Const>;
	bool comparisons(SigBit bit, pool<Cell *> &predicates, pool<Cell *> &region, int depth=0) {
		if (!bit.wire) return bit==State::S0 || bit==State::S1;
		if (--budget <= 0 || depth > 6) return false;
		auto cell = netlist.driver(bit);
		if (!cell || !netlist.editable(cell)) return false;
		region.insert(cell);
		if (cell->type.in(ID($lt), ID($gt), ID($eq)) && !cell->getPort(ID::A).is_fully_const() && !cell->getPort(ID::B).is_fully_const()) {
			predicates.insert(cell);
			return GetSize(predicates) <= 3;
		}
		if(!cell->type.in(ID($eq),ID($not),ID($logic_not),ID($and),ID($or),ID($xor)))return false;
		for (auto &port : cell->connections()) if (netlist.cell_input(cell->type, port.first))
			for (auto in : netlist.port(cell, port.first))
				if (!comparisons(in, predicates, region, depth+1)) return false;
		return true;
	}
	bool equal_branch(SigSpec value, const SigSpec &a, const SigSpec &b, pool<Cell *> &region) {
		if(value==a || value==b)return true;
		auto cell = root(value);
		if (!cell || !cell->type.in(ID($or), ID($and))) return false;
		auto x = netlist.extended(cell, ID::A, GetSize(value)), y = netlist.extended(cell, ID::B, GetSize(value));
		// 外部零扩展必须保留相等操作数的全部有效位。
		for(int i=GetSize(cell->getPort(ID::Y));i<GetSize(value);i++)
			if(x[i]!=State::S0||y[i]!=State::S0)return false;
		if ((x == a || x == b) && (y == a || y == b)) {
			region.insert(cell);
			return true;
		}
		return false;
	}
	bool minimum_maximum(Cell *pmux) {
		int width = GetSize(pmux->getPort(ID::Y));
		if (width < 2 || width > 32) return false;
		pool<Cell *> predicates, region;
		const auto &s = netlist.port(pmux, ID::S);
		if (GetSize(s) > 4) return false;
		for (auto bit : s)
			if (!comparisons(bit, predicates, region)) return false;
		if (GetSize(predicates) != 3) return false;
		SigSpec a, b;
		bool sign = false, first = true;
		dict<Cell *, int> relation;
		for (auto cell : predicates) {
			if (GetSize(cell->getPort(ID::Y)) != 1) return false;
			int w = std::max(GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::B)));
			auto x = netlist.extended(cell, ID::A, w), y = netlist.extended(cell, ID::B, w);
			bool signed_order = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
			if (w != width) return false;
			if (first) {
				a = x;
				b = y;
				sign = signed_order;
				first = false;
			}
			for (auto bit : x)
				if (!bit.wire && bit != State::S0 && bit != State::S1) return false;
			for (auto bit : y)
				if (!bit.wire && bit != State::S0 && bit != State::S1) return false;
			if (signed_order != sign) return false;
			int r = 1;
			if (cell->type == ID($lt)) r = 0;
			if (cell->type == ID($gt)) r = 2;
			if (x == b && y == a)
				r = 2-r;
			else if (x != a || y != b)
				return false;
			relation[cell] = r;
		}
		pool<int> kinds;
		for (auto &entry : relation)
			kinds.insert(entry.second);
		if (GetSize(kinds) != 3) return false;
		std::vector<SigSpec> branch;
		const auto &av = netlist.port(pmux, ID::A), &bv = netlist.port(pmux, ID::B);
		for (int state = 0; state < 3; state++) {
			dict<SigBit, bool> values;
			for (auto &entry : relation)
				values[netlist.port(entry.first, ID::Y)[0]] = entry.second == state;
			SigSpec selected;
			if (!selected_branch(s, av, bv, width, values, selected)) return false;
			branch.push_back(selected);
		}
		bool minimum = branch[0] == a && branch[2] == b;
		bool maximum = branch[0] == b && branch[2] == a;
		if ((!minimum && !maximum) || !equal_branch(branch[1], a, b, region)) return false;
		PmuxLutGraph net(PmuxLutGraph::Expansion::All);
		auto ab = net.bits(a), bb = net.bits(b);
		int less = 0;
		for (int i = 0; i < width; i++) {
			int x = ab[i], y = bb[i];
			if (sign && i == width-1) {
				x = net.gate({x}, 1);
				y = net.gate({y}, 1);
			}
			// 低位递推比较，高位不同的时候覆盖低位结果。
			less = net.gate({x, y, less}, 0xd4);
		}
		std::vector<int> output;
		for (int i = 0; i < width; i++)
			output.push_back(net.mux(minimum ? bb[i] : ab[i], minimum ? ab[i] : bb[i], less));
		return commit_outputs({pmux}, region, net, output);
	}
	std::pair<std::vector<int>, std::vector<int>> divmod3(PmuxLutGraph &net, const SigSpec &input, int width) {
		log_assert(width >= 2 && GetSize(input) >= width);
		auto x = net.bits(input);
		std::vector<int> quotient(width, 0), remainder(2, 0);
		for(int high=width-1;high>=0;){
			int group=(high==width-1&&(width&1))?1:2,low=high-group+1;
			std::vector<int> args{remainder[0], remainder[1], x[low], group == 2 ? x[high] : 0};
			unsigned tables[4] = {0, 0, 0, 0};
			for(int code=0;code<16;code++){
				int r=code&3,u=(code>>2)&3,t=(r<<group)+(u&((1<<group)-1));
				Const q=const_div(Const(t,4),Const(3,4),false,false,2),m=const_mod(Const(t,4),Const(3,4),false,false,2);
				for (int j = 0; j < 2; j++) {
					tables[j] |= (q[j] == State::S1) << code;
					tables[j+2] |= (m[j] == State::S1) << code;
				}
			}
			quotient[low] = net.gate(args, tables[0]);
			if (group == 2)
				quotient[high] = net.gate(args, tables[1]);
			remainder = {net.gate(args, tables[2]), net.gate(args, tables[3])};
			high -= group;
		}
		remainder.resize(width, 0);
		return {quotient, remainder};
	}
	bool unsigned_div3(Cell *cell) const {
		if(!cell->type.in(ID($div),ID($mod))||!netlist.editable(cell))return false;
		if(cell->getParam(ID::A_SIGNED).as_bool()||cell->getParam(ID::B_SIGNED).as_bool())return false;
		for(auto bit:netlist.port(cell, ID::A))if(!bit.wire&&bit!=State::S0&&bit!=State::S1)return false;
		const auto &divisor = netlist.port(cell, ID::B);
		return GetSize(divisor)>=2&&divisor.is_fully_def()&&divisor.is_fully_const()&&divisor.as_const()==Const(3,GetSize(divisor));
	}
	bool shared_divisions() {
		dict<SigSpec,std::vector<Cell *>> groups;
		for(auto cell:module->cells())if(unsigned_div3(cell)&&GetSize(cell->getPort(ID::Y))<=32){
			auto input = without_zero_extension(netlist.port(cell, ID::A));
			if(GetSize(input)>=2&&GetSize(input)<=16)groups[input].push_back(cell);
		}
		int attempts=0;
		for(auto &group:groups){
			if(++attempts>16)return false;
			bool have_div = false, have_mod = false;
			for (auto cell : group.second) {
				have_div |= cell->type == ID($div);
				have_mod |= cell->type == ID($mod);
			}
			if (!have_div || !have_mod) continue;
			PmuxLutGraph net(PmuxLutGraph::Expansion::All);
			auto qr = divmod3(net, group.first, GetSize(group.first));
			std::vector<int> outputs;
			for (auto cell : group.second) {
				auto values = cell->type == ID($div) ? qr.first : qr.second;
				values.resize(GetSize(cell->getPort(ID::Y)), 0);
				outputs.insert(outputs.end(), values.begin(), values.end());
			}
			if(commit_outputs(group.second,{},net,outputs))return true;
		}
		return false;
	}
	bool selected_divmod(Cell *pmux, ChoiceInfo &info) {
		int width = GetSize(pmux->getPort(ID::Y));
		if (width < 3 || width > 16) return false;
		if (!choice(pmux, info)) return false;
		const auto &branches = info.branches;
		const auto &control = info.control;
		auto region = info.region;
		SigSpec input;
		dict<Cell *, bool> division;
		std::vector<Cell *> roots;
		for (auto branch : branches) {
			auto cell = root(branch);
			roots.push_back(cell);
			if (!cell || !cell->type.in(ID($div), ID($mod))) continue;
			if(!unsigned_div3(cell))return false;
			auto x = netlist.extended(cell, ID::A, width);
			if (input.empty())
				input = x;
			else if (input != x)
				return false;
			if(GetSize(cell->getPort(ID::A))>width)return false;
			division[cell] = cell->type == ID($div);
			region.insert(cell);
		}
		if(GetSize(division)<2)return false;
		bool have_div = false, have_mod = false;
		for (auto &item : division) {
			have_div |= item.second;
			have_mod |= !item.second;
		}
		if (!have_div || !have_mod) return false;
		PmuxLutGraph net(PmuxLutGraph::Expansion::All);
		auto qr = divmod3(net, input, width);
		auto cb = net.bits(control);
		std::vector<std::vector<int>> values;
		for(int j=0;j<GetSize(branches);j++){
			if(division.count(roots[j])){
				auto v=division.at(roots[j])?qr.first:qr.second;
				int yw = GetSize(roots[j]->getPort(ID::Y));
				for (int i = yw; i < width; i++)
					v[i] = 0;
				values.push_back(v);
			}else values.push_back(net.bits(branches[j]));
		}
		std::vector<int> output;
		for (int i = 0; i < width; i++) {
			std::vector<int> column;
			for (auto &value : values)
				column.push_back(value[i]);
			output.push_back(net.select(column, cb));
		}
		return commit_outputs({pmux}, region, net, output);
	}
	bool expression(SigSpec value, int width, Polynomial &terms, pool<Cell *> &region, bool negative = false, int depth = 0)
	{
		if (--budget <= 0 || depth > 8 || GetSize(terms) > 12) return false;
		auto cell = root(value);
		if (cell && cell->type.in(ID($add), ID($sub))) {
			int yw = GetSize(cell->getPort(ID::Y));
			bool safe = yw >= width;
			if (!safe && !cell->getParam(ID::A_SIGNED).as_bool() && !cell->getParam(ID::B_SIGNED).as_bool() && cell->type == ID($add)) {
				auto a = without_zero_extension(netlist.port(cell, ID::A));
				auto b = without_zero_extension(netlist.port(cell, ID::B));
				safe = std::max(GetSize(a), GetSize(b))+1 <= yw;
			}
			if (safe) {
				region.insert(cell);
				return expression(netlist.extended(cell, ID::A, width), width, terms, region, negative, depth+1) &&
					expression(netlist.extended(cell, ID::B, width), width, terms, region, negative ^ (cell->type == ID($sub)), depth+1);
			}
		}
		int shift = 0;
		while (shift < GetSize(value) && value[shift] == State::S0)
			shift++;
		if (shift == GetSize(value)) return true;
		value.remove(0, shift);
		value = without_zero_extension(std::move(value));
		for (auto bit : value)
			if (!bit.wire && bit != State::S0 && bit != State::S1) return false;
		Const coefficient = const_shl(Const(1, width), Const(shift, 32), false, false, width);
		if (negative) coefficient = const_neg(coefficient, {}, false, false, width);
		if (!terms.count(value)) terms[value] = Const(0, width);
		terms[value] = const_add(terms.at(value), coefficient, false, false, width);
		return true;
	}
	// 返回 false 表示预算耗尽；准入失败时保留原多项式。
	bool normalize_constant_offsets(std::vector<Polynomial> &polynomials, int width) {
		if ((budget -= GetSize(polynomials)) <= 0) return false;
		for (auto &polynomial : polynomials)
			if (GetSize(polynomial) > 12) return true;
		Const zero(0, width), one(1, width), minus_one(State::S1, width);
		std::vector<Const> offsets(polynomials.size(), zero);
		std::vector<Polynomial> normalized(polynomials.size());
		pool<SigSpec> variables, constants;
		for (int i = 0; i < GetSize(polynomials); i++) {
			for (auto &term : polynomials[i]) {
				if ((budget -= width) <= 0) return false;
				log_assert(GetSize(term.second) == width && term.second.is_fully_def());
				if (!term.second.as_bool()) continue;
				if (term.first.is_fully_const()) {
					log_assert(term.first.is_fully_def());
					if ((budget -= 2*width) <= 0) return false;
					auto product = const_mul(term.second, term.first.as_const(), false, false, width);
					offsets[i] = const_add(offsets[i], product, false, false, width);
					constants.insert(term.first);
				} else {
					if (term.second != one && term.second != minus_one) return true;
					variables.insert(term.first);
					normalized[i][term.first] = term.second;
				}
			}
		}
		if (constants.empty() || variables.empty() || GetSize(variables) > 2) return true;
		if ((budget -= 5*width*GetSize(polynomials)) <= 0) return false;
		Const base = zero;
		for (int i = 0; i < GetSize(normalized); i++) {
			bool negative = false;
			for (auto &term : normalized[i]) negative |= term.second == minus_one;
			if (!negative || offsets[i] == zero) continue;
			if (base != zero && base != offsets[i]) return true;
			base = offsets[i];
		}
		for (auto &offset : offsets) if (base == zero && offset != zero) {
			auto opposite = const_neg(offset, {}, false, false, width);
			base = const_lt(opposite, offset, false, false, 1).as_bool() ? opposite : offset;
			break;
		}
		if (base != zero && GetSize(variables) != 1) return true;
		auto opposite = const_neg(base, {}, false, false, width);
		for (int i = 0; i < GetSize(normalized); i++) {
			int negative = 0;
			for (auto &term : normalized[i]) negative += term.second == minus_one;
			if (offsets[i] != zero) {
				Const coefficient;
				if (offsets[i] == base) coefficient = one;
				else if (offsets[i] == opposite) coefficient = minus_one;
				else return true;
				negative += coefficient == minus_one;
				normalized[i][SigSpec(base)] = coefficient;
			}
			if (negative > 1) return true;
		}
		polynomials.swap(normalized);
		log_debug("PMUX arithmetic constant offsets: width=%d constant_bases=%d->%d K=%s.\n",
			width, GetSize(constants), base != zero, log_signal(SigSpec(base)));
		for (int i = 0; i < GetSize(offsets); i++)
			log_debug("PMUX arithmetic offset branch=%d value=%s.\n", i, log_signal(SigSpec(offsets[i])));
		return true;
	}
	bool scaled_base(Cell *pmux, const std::vector<Polynomial> &polynomials, SigSpec base,
			const SigSpec &control, const pool<Cell *> &region, int width)
	{
		std::vector<Const> coefficients;
		for (auto &polynomial : polynomials)
			coefficients.push_back(polynomial.count(base) ? polynomial.at(base) : Const(0, width));
		std::vector<int> shifts;
		for (int j = 0; j < GetSize(control); j++) {
			auto delta = const_sub(coefficients[1 << j], coefficients[0], false, false, width);
			int position = -1;
			for (int k = 0; k < width; k++) if (delta[k] == State::S1) {
				if (position >= 0) return false;
				position = k;
			}
			shifts.push_back(position);
		}
		int initial = -1;
		for (int k = 0; k < width; k++) if (coefficients[0][k] == State::S1) {
			if (initial >= 0) return false;
			initial = k;
		}
		for (int code = 0; code < GetSize(polynomials); code++) {
			auto expected = coefficients[0];
			for (int j = 0; j < GetSize(control); j++)
				if (((code >> j) & 1) && shifts[j] >= 0)
					expected = const_add(expected, const_shl(Const(1, width), Const(shifts[j], 32), false, false, width), false, false, width);
			if (expected != coefficients[code]) return false;
		}
		PmuxLutGraph net(PmuxLutGraph::Expansion::All);
		auto cb = net.bits(control);
		base.extend_u0(width);
		auto x = net.bits(base);
		std::vector<int> sum(width, 0);
		if (initial >= 0)
			for (int i = initial; i < width; i++) sum[i] = x[i-initial];
		for (int j = 0; j < GetSize(control); j++) if (shifts[j] >= 0) {
			std::vector<int> term(width, 0);
			for (int i = shifts[j]; i < width; i++)
				term[i] = net.gate({x[i-shifts[j]], cb[j]}, 8);
			sum = net.add(sum, term);
		}
		return commit_outputs({pmux}, region, net, sum);
	}
	bool signed_bases(Cell *pmux, const std::vector<Polynomial> &polynomials, std::vector<SigSpec> bases,
			const SigSpec &control, const pool<Cell *> &region, int width)
	{
		std::vector<std::array<int, 2>> signs;
		for (auto &polynomial : polynomials) {
			std::array<int, 2> sign{};
			int negative = 0;
			for (int j = 0; j < 2; j++) {
				auto term = polynomial.find(bases[j]);
				if (term == polynomial.end()) continue;
				if (term->second == Const(1, width)) {
					sign[j] = 1;
				} else if (term->second == Const(State::S1, width)) {
					sign[j] = -1;
					negative++;
				} else if (term->second.as_bool()) {
					return false;
				}
			}
			if (negative > 1) return false;
			signs.push_back(sign);
		}
		log_debug("PMUX arithmetic two-base emitter %s: bases=%s, %s.\n",
			log_id(pmux), log_signal(bases[0]), log_signal(bases[1]));
		PmuxLutGraph net(PmuxLutGraph::Expansion::All);
		auto cb = net.bits(control);
		std::vector<int> operands[2];
		for (int j = 0; j < 2; j++) {
			bases[j].extend_u0(width);
			for (int i = 0; i < width; i++) {
				std::vector<int> values;
				int data = net.leaf(bases[j][i]);
				for (auto &sign : signs) {
					if (sign[j] == 0) values.push_back(0);
					else if (sign[j] > 0) values.push_back(data);
					else values.push_back(net.gate({data}, 1));
				}
				operands[j].push_back(net.select(values, cb));
			}
		}
		// 负项按逐位取反和一次进位表示；每个分支最多包含一个负项。
		std::vector<int> carries;
		for (auto &sign : signs)
			carries.push_back((sign[0] < 0) + (sign[1] < 0));
		return commit_outputs({pmux}, region, net, net.add(operands[0], operands[1], net.select(carries, cb)));
	}
	bool three_term_sums(Cell *pmux, const std::vector<Polynomial> &polynomials, std::vector<SigSpec> bases,
			const SigSpec &control, const pool<Cell *> &region, int width)
	{
		// 编号采用原始 SigSpec 的排序；扩展位宽后仍保留各自编号。
		dict<SigSpec, int> indices;
		for (int i = 0; i < GetSize(bases); i++) indices[bases[i]] = i;
		std::vector<std::array<int, 3>> terms;
		for (auto &polynomial : polynomials) {
			std::vector<int> values;
			for (auto &term : polynomial) {
				if (!term.second.as_bool()) continue;
				int count = term.second.as_int();
				if (count < 1 || count > 3) return false;
				for (int j = 0; j < count; j++)
					values.push_back(indices.at(term.first));
			}
			if (GetSize(values) != 3) return false;
			std::sort(values.begin(), values.end());
			terms.push_back({values[0], values[1], values[2]});
		}
		if (terms.size() > 4) return false;
		for (auto &base : bases) base.extend_u0(width);
		PmuxLutGraph best(PmuxLutGraph::Expansion::All);
		std::vector<int> bestout;
		int bestcost = INT_MAX;
		auto ordered = terms;
		std::function<void(int)> enumerate = [&](int branch) {
			if (budget <= 0) return;
			if (branch < GetSize(terms)) {
				auto permutation = terms[branch];
				do {
					ordered[branch] = permutation;
					enumerate(branch+1);
				} while (std::next_permutation(permutation.begin(), permutation.end()));
				return;
			}
			budget -= 2*width;
			PmuxLutGraph net(PmuxLutGraph::Expansion::All);
			auto cb = net.bits(control);
			std::vector<int> operands[3];
			for (int column = 0; column < 3; column++) {
				for (int i = 0; i < width; i++) {
					std::vector<int> values;
					for (auto &row : ordered)
						values.push_back(net.leaf(bases[row[column]][i]));
					operands[column].push_back(net.select(values, cb));
				}
			}
			auto output = net.sum3(operands[0], operands[1], operands[2]);
			int cost = net.cost(output);
			if (cost < bestcost) {
				bestcost = cost;
				best = std::move(net);
				bestout = std::move(output);
			}
		};
		// 三项整体换位不改变求和，固定第一个分支的排列。
		enumerate(1);
		return !bestout.empty() && commit_outputs({pmux}, region, best, bestout);
	}
	bool arithmetic(Cell *pmux, ChoiceInfo &info)
	{
		int width = GetSize(pmux->getPort(ID::Y));
		if (width < 2 || width > 32) return false;
		if (!choice(pmux, info)) return false;
		const auto &branches = info.branches;
		const auto &control = info.control;
		auto region = info.region;
		std::vector<Polynomial> polynomials;
		for (auto branch : branches) {
			Polynomial polynomial;
			if (!expression(branch, width, polynomial, region)) return false;
			polynomials.push_back(std::move(polynomial));
		}
		if (!normalize_constant_offsets(polynomials, width)) return false;
		pool<SigSpec> bases;
		for (auto &polynomial : polynomials)
			for (auto &term : polynomial)
				if (term.second.as_bool()) bases.insert(term.first);
		if (GetSize(bases) == 1)
			return scaled_base(pmux, polynomials, *bases.begin(), control, region, width);
		std::vector<SigSpec> sorted(bases.begin(), bases.end());
		std::sort(sorted.begin(), sorted.end());
		if (GetSize(bases) == 2)
			return signed_bases(pmux, polynomials, std::move(sorted), control, region, width);
		return three_term_sums(pmux, polynomials, std::move(sorted), control, region, width);
	}
};

struct OptPmuxArithPass : Pass {
	OptPmuxArithPass():Pass("opt_pmuxarith","share bounded arithmetic across PMUX choices"){}
	void help() override {
		log("    opt_pmuxarith [-lut4 <celltype>] [selection]\n\n");
		log("Share controlled arithmetic and emit single-output four-input LUTs.\n");
		log("-lut4 emits Intel lcell_comb ports and lut_mask parameters.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		IdString luttype;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] != "-lut4") break;
			if (argidx+1 >= args.size())
				log_cmd_error("Missing cell type for -lut4.\n");
			luttype = RTLIL::escape_id(args[++argidx]);
		}
		extra_args(args,argidx,design);
		for(auto module:design->selected_modules()){
			std::vector<IdString> candidates;
			int divisions = 0;
			for(auto cell:module->selected_cells()){
				if(cell->get_bool_attribute(ID::keep))continue;
				if(cell->type==ID($pmux)&&GetSize(cell->getPort(ID::Y))>=2&&GetSize(cell->getPort(ID::Y))<=32&&GetSize(cell->getPort(ID::S))<=4)candidates.push_back(cell->name);
				if(cell->type.in(ID($div),ID($mod))&&GetSize(cell->getPort(ID::A))<=16)divisions++;
			}
			int count = 0, remaining = 20000;
			std::unique_ptr<PmuxArithWorker> worker;
			auto prepare = [&]() {
				if (!worker)
					worker = std::make_unique<PmuxArithWorker>(module, design, luttype);
				worker->budget = remaining;
			};
			for(auto name:candidates){
				if (++count > 64 || remaining <= 0) break;
				auto cell = module->cell(name);
				if (!cell) continue;
				prepare();
				bool changed = false;
				if (worker->netlist.editable(cell)) {
					PmuxArithWorker::ChoiceInfo choice;
					changed = worker->minimum_maximum(cell) || worker->selected_divmod(cell, choice) || worker->arithmetic(cell, choice);
				}
				remaining = worker->budget;
				if (changed) worker.reset();
			}
			if(divisions>=2)for(int attempt=0;attempt<8&&remaining>0;attempt++){
				prepare();
				bool changed = worker->shared_divisions();
				remaining = worker->budget;
				if (!changed) break;
				worker.reset();
			}
		}
	}
} OptPmuxArithPass;

PRIVATE_NAMESPACE_END
