// opt_pmuxarith 共享 PMUX 分支中的加减、比较及常量除模运算，并生成四输入 LUT 网络。
// 在操作数选择、进位和余数计算之间共享节点，减少重复算术与选择逻辑。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
#include "passes/opt/pmux_celltypes.h"
#include <array>
#include <functional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ArithNetwork {
	struct Node {
		SigBit bit;
		std::vector<int> inputs;
		unsigned table = 0;
		bool leaf = false;
	};
	std::vector<Node> nodes;
	dict<SigBit, int> leaves;
	std::map<std::pair<std::vector<int>, unsigned>, int> cache;
	ArithNetwork() {
		leaf(State::S0);
		leaf(State::S1);
	}
	int leaf(SigBit bit) {
		auto found = leaves.find(bit);
		if (found != leaves.end())
			return found->second;
		int id = GetSize(nodes);
		nodes.push_back({bit, {}, 0, true});
		leaves[bit] = id;
		return id;
	}
	int lut(const std::vector<int> &args, unsigned table) {
		log_assert(GetSize(args) <= 4);
		std::vector<int> inputs;
		for (int arg : args) {
			log_assert(arg >= 0 && arg < GetSize(nodes));
			if (arg > 1 && std::find(inputs.begin(), inputs.end(), arg) == inputs.end())
				inputs.push_back(arg);
		}
		std::sort(inputs.begin(), inputs.end());
		unsigned reduced = 0;
		for (int value = 0; value < (1 << GetSize(inputs)); value++) {
			int old = 0;
			for (int i = 0; i < GetSize(args); i++) {
				int v = args[i] == 1;
				if (args[i] > 1) v = (value >> (std::lower_bound(inputs.begin(), inputs.end(), args[i]) - inputs.begin())) & 1;
				old |= v << i;
			}
			reduced |= ((table >> old) & 1) << value;
		}
		for (int i = GetSize(inputs)-1; i >= 0; i--) {
			bool depends = false;
			for (int j = 0; j < (1 << GetSize(inputs)); j++) if (((reduced >> j) & 1) != ((reduced >> (j ^ (1 << i))) & 1)) depends = true;
			if (!depends) {
				unsigned smaller = 0;
				for (int j = 0; j < (1 << (GetSize(inputs)-1)); j++) smaller |= ((reduced >> ((j & ((1 << i)-1)) | ((j >> i) << (i+1)))) & 1) << j;
				inputs.erase(inputs.begin()+i);
				reduced = smaller;
			}
		}
		if (inputs.empty()) return reduced & 1;
		if (GetSize(inputs) == 1 && reduced == 2) return inputs[0];
		log_assert(GetSize(inputs) <= 4);
		auto key = std::make_pair(inputs, reduced);
		auto found = cache.find(key);
		if (found != cache.end())
			return found->second;
		int id = GetSize(nodes);
		nodes.push_back({{}, inputs, reduced, false});
		cache[key] = id;
		return id;
	}
	int gate(const std::vector<int> &args, unsigned table) {
		log_assert(GetSize(args) <= 4);
		std::vector<int> expanded;
		for (int id : args) {
			auto in = nodes[id].leaf ? std::vector<int>{id} : nodes[id].inputs;
			for (int v : in) if (v > 1 && std::find(expanded.begin(), expanded.end(), v) == expanded.end()) expanded.push_back(v);
		}
		if (GetSize(expanded) > 4) return lut(args, table);
		unsigned merged = 0;
		for (int value = 0; value < (1 << GetSize(expanded)); value++) {
			auto eval = [&](int id) {
				if (id < 2) return id;
				auto pos = std::find(expanded.begin(), expanded.end(), id);
				if (nodes[id].leaf) return (value >> (pos-expanded.begin())) & 1;
				int index = 0;
				for (int i = 0; i < GetSize(nodes[id].inputs); i++) {
					int arg = nodes[id].inputs[i];
					index |= ((value >> (std::find(expanded.begin(), expanded.end(), arg)-expanded.begin())) & 1) << i;
				}
				return int((nodes[id].table >> index) & 1);
			};
			int index = 0;
			for (int i = 0; i < GetSize(args); i++) index |= eval(args[i]) << i;
			merged |= ((table >> index) & 1) << value;
		}
		return lut(expanded, merged);
	}
	int mux(int a, int b, int s) { return gate({a,b,s}, 0xca); }
	std::vector<int> bits(const SigSpec &value) {
		std::vector<int> result;
		for (auto bit : value)
			result.push_back(leaf(bit));
		return result;
	}
	std::vector<int> add(const std::vector<int> &a, const std::vector<int> &b, int carry = 0) {
		log_assert(a.size() == b.size());
		std::vector<int> result;
		for (int i = 0; i < GetSize(a); i++) {
			result.push_back(gate({a[i],b[i],carry}, 0x96));
			if (i+1 < GetSize(a)) carry = gate({a[i],b[i],carry}, 0xe8);
		}
		return result;
	}
	std::vector<int> sum3(const std::vector<int> &a, const std::vector<int> &b, const std::vector<int> &c) {
		log_assert(a.size() == b.size() && a.size() == c.size());
		std::vector<int> sum, carry(a.size(), 0);
		for (int i = 0; i < GetSize(a); i++) {
			sum.push_back(gate({a[i],b[i],c[i]}, 0x96));
			if (i+1 < GetSize(a)) carry[i+1] = gate({a[i],b[i],c[i]}, 0xe8);
		}
		return add(sum, carry);
	}
	int select(const std::vector<int> &values, const std::vector<int> &control, int level = 0, int prefix = 0) {
		if (level == GetSize(control)) return values[prefix];
		return mux(select(values, control, level+1, prefix), select(values, control, level+1, prefix | (1 << level)), control[level]);
	}
	pool<int> live(const std::vector<int> &outputs) const {
		pool<int> seen;
		std::function<void(int)> visit = [&](int id) {
			log_assert(id >= 0 && id < GetSize(nodes));
			if (seen.insert(id).second)
				for (int arg : nodes[id].inputs) visit(arg);
		};
		for (int id : outputs) visit(id);
		return seen;
	}
	int cost(const std::vector<int> &outputs) const {
		int count = 0;
		for (int id : live(outputs))
			count += !nodes[id].leaf;
		return count;
	}
	SigSpec emit(Module *module, IdString celltype, const std::vector<int> &outputs) const {
		auto used = live(outputs);
		std::vector<SigBit> signals(nodes.size());
		for (int id = 0; id < GetSize(nodes); id++) if (used.count(id)) {
			auto &node = nodes[id];
			if (node.leaf) {
				signals[id] = node.bit;
				continue;
			}
			auto wire = module->addWire(NEW_ID);
			signals[id] = SigBit(wire);
			auto cell = module->addCell(NEW_ID, celltype.empty() ? ID($lut) : celltype);
			SigSpec inputs;
			for (int arg : node.inputs)
				inputs.append(signals[arg]);
			unsigned mask = 0;
			for (int i = 0; i < 16; i++)
				mask |= ((node.table >> (i & ((1 << inputs.size())-1))) & 1) << i;
			inputs.extend_u0(4);
			if (celltype.empty()) {
				cell->setParam(ID::WIDTH, 4);
				cell->setParam(ID::LUT, Const(mask,16));
				cell->setPort(ID::A, inputs);
				cell->setPort(ID::Y, wire);
			} else {
				cell->setParam(ID(lut_mask), Const(mask,16));
				cell->setParam(ID(sum_lutc_input), Const("datac"));
				cell->setPort(ID(dataa), inputs[0]);
				cell->setPort(ID(datab), inputs[1]);
				cell->setPort(ID(datac), inputs[2]);
				cell->setPort(ID(datad), inputs[3]);
				cell->setPort(ID(combout), wire);
				cell->setPort(ID(cin), State::S0);
			}
		}
		SigSpec result;
		for (int id : outputs)
			result.append(signals[id]);
		return result;
	}
};

struct PmuxArithWorker {
	Module *module;
	SigMap sigmap;
	PmuxCellTypes types;
	IdString luttype;
	dict<SigBit, Cell *> drivers;
	dict<SigBit, std::vector<Cell *>> users;
	pool<SigBit> protected_bits, kept_bits, input_bits, multiple_drivers;
	pool<Cell *> selected;
	int budget = 20000;
	PmuxArithWorker(Module *m, Design *d, IdString luttype) : module(m), sigmap(m), types(m,d), luttype(luttype) {
		for (auto wire : m->wires()) {
			bool keep = wire->get_bool_attribute(ID::keep);
			if (!wire->port_input && !wire->port_output && !keep) continue;
			for (auto bit : sigmap(wire)) {
				if (wire->port_input) {
					drivers[bit] = nullptr;
					input_bits.insert(bit);
				}
				if (wire->port_output || keep) protected_bits.insert(bit);
				if (keep) kept_bits.insert(bit);
			}
		}
		for (auto cell : m->cells()) {
			if (d->selected(m,cell)) selected.insert(cell);
			bool keep = cell->get_bool_attribute(ID::keep);
			for (auto &port : cell->connections()) {
				auto direction = types.cell_port_dir(cell->type, port.first);
				bool output = direction == RTLIL::PD_OUTPUT || direction == RTLIL::PD_INOUT;
				bool input = direction == RTLIL::PD_INPUT || direction == RTLIL::PD_INOUT;
				for (auto bit : sigmap(port.second)) {
					if (output) {
						if (drivers.count(bit)) {
							drivers[bit] = nullptr;
							multiple_drivers.insert(bit);
						} else {
							drivers[bit] = cell;
						}
					}
					if (input || !output) {
						auto &list = users[bit];
						if (list.empty() || list.back() != cell) list.push_back(cell);
					}
					if (keep || (!input && !output)) kept_bits.insert(bit);
				}
			}
		}
	}
	bool editable(Cell *cell) const {
		if (!selected.count(cell) || cell->get_bool_attribute(ID::keep) || !cell->hasPort(ID::Y)) return false;
		for (auto bit : sigmap(cell->getPort(ID::Y))) if (kept_bits.count(bit) || !drivers.count(bit) || drivers.at(bit) != cell) return false;
		return true;
	}
	SigSpec extended(Cell *cell, IdString port, int width) const {
		auto s = sigmap(cell->getPort(port));
		bool sign = cell->getParam(ID::A_SIGNED).as_bool() && (!cell->hasParam(ID::B_SIGNED) || cell->getParam(ID::B_SIGNED).as_bool());
		s.extend_u0(width, sign);
		return s;
	}
	SigSpec without_zero_extension(SigSpec value) const
	{
		while (!value.empty() && value.back() == State::S0)
			value.remove(GetSize(value)-1);
		return value;
	}
	Cell *root(const SigSpec &value) const {
		if (value.empty() || !drivers.count(value[0])) return nullptr;
		auto cell = drivers.at(value[0]);
		if (!cell || !editable(cell)) return nullptr;
		auto y = sigmap(cell->getPort(ID::Y));
		int n = std::min(GetSize(y),GetSize(value));
		if (value.extract(0,n) != y.extract(0,n)) return nullptr;
		for (int i = n; i < GetSize(value); i++) if (value[i] != State::S0) return nullptr;
		return cell;
	}
	bool independent(const pool<SigBit> &leaves, const SigSpec &output) {
		pool<SigBit> target(output.begin(),output.end()), done, active;
		std::function<bool(SigBit)> visit = [&](SigBit bit) {
			if (!bit.wire) return true;
			if (target.count(bit) || active.count(bit) || multiple_drivers.count(bit) || --budget <= 0) return false;
			if (done.count(bit)) return true;
			if (!drivers.count(bit)) return false;
			auto cell = drivers.at(bit);
			if (!cell) {
				// 输入端口作为组合分析的边界。
				return input_bits.count(bit) != 0;
			}
			active.insert(bit);
			if (!types.cell_known(cell->type)) return false;
			for (auto &port : cell->connections()) if (types.cell_input(cell->type,port.first))
				for (auto in : sigmap(port.second)) if (!visit(in)) return false;
			active.erase(bit);
			done.insert(bit);
			return true;
		};
		for (auto bit : leaves) if (!visit(bit)) return false;
		return true;
	}
	int old_cost(Cell *cell) const {
		int width = GetSize(cell->getPort(ID::Y));
		if (cell->type.in(ID($add),ID($sub))) return std::max(0,2*width-1);
		if (cell->type == ID($pmux)) return width * GetSize(cell->getPort(ID::S));
		if (cell->type.in(ID($div),ID($mod))) return width*width;
		if (cell->type.in(ID($eq),ID($ne),ID($lt),ID($gt))) return std::max(GetSize(cell->getPort(ID::A)),GetSize(cell->getPort(ID::B)));
		return width;
	}
	bool commit_outputs(const std::vector<Cell *> &roots, pool<Cell *> region, ArithNetwork &network, const std::vector<int> &outputs) {
		pool<SigBit> leaves;
		for (int id : network.live(outputs)) if (network.nodes[id].leaf && network.nodes[id].bit.wire) leaves.insert(network.nodes[id].bit);
		SigSpec y;
		pool<Cell *> replaced;
		for (auto cell : roots) {
			y.append(sigmap(cell->getPort(ID::Y)));
			region.insert(cell);
			replaced.insert(cell);
		}
		log_assert(GetSize(y) == GetSize(outputs));
		if (!independent(leaves,y)) return false;
		bool changed;
		do {
			changed = false;
			for (auto cell : std::vector<Cell *>(region.begin(),region.end())) if (!replaced.count(cell)) {
				bool retain = !editable(cell);
				for (auto bit : sigmap(cell->getPort(ID::Y))) {
					if (protected_bits.count(bit) || leaves.count(bit)) retain = true;
					for (auto user : reversed(users[bit])) if (!region.count(user)) retain = true;
				}
				if (retain) {
					region.erase(cell);
					changed = true;
				}
			}
		} while (changed);
		int old = 0;
		dict<SigSpec, int> divcost;
		for (auto cell : region) {
			if (cell->type.in(ID($div), ID($mod))) {
				auto input = without_zero_extension(sigmap(cell->getPort(ID::A)));
				auto &cost = divcost[input];
				cost = std::max(cost, GetSize(input)*GetSize(input));
			} else {
				old += old_cost(cell);
			}
		}
		for (auto &item : divcost)
			old += item.second;
		int cost = network.cost(outputs);
		if (cost >= old) return false;
		int before = module->cells_size();
		auto emitted = network.emit(module, luttype, outputs);
		int emitted_cells = module->cells_size() - before;
		log_assert(emitted_cells == cost);
		log_debug("PMUX arithmetic commit: reference=%d candidate=%d removed=%d emitted=%d.\n",
			old, cost, GetSize(region), emitted_cells);
		int offset = 0;
		for (auto cell : roots) {
			auto port = cell->getPort(ID::Y);
			module->connect(port, emitted.extract(offset, GetSize(port)));
			offset += GetSize(port);
		}
		for (auto cell : region) module->remove(cell);
		return true;
	}
	bool commit(Cell *pmux, const pool<Cell *> &region, ArithNetwork &network, const std::vector<int> &outputs) {
		return commit_outputs({pmux}, region, network, outputs);
	}
	bool control_support(SigBit bit, pool<SigBit> &support, pool<Cell *> &region, int depth = 0) {
		if (!bit.wire) return bit == State::S0 || bit == State::S1;
		if (--budget <= 0 || depth > 8) return false;
		auto cell = drivers.count(bit) ? drivers.at(bit) : nullptr;
		if (cell && editable(cell) && cell->type.in(ID($eq),ID($logic_not),ID($not),ID($and),ID($or),ID($xor),ID($reduce_or),ID($reduce_bool))) {
			region.insert(cell);
			for (auto &port : cell->connections()) if (types.cell_input(cell->type,port.first)) {
				if (GetSize(port.second)>4) return false;
				for (auto in : sigmap(port.second)) if (!control_support(in,support,region,depth+1)) return false;
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
		if (depth>8 || --budget<=0 || !drivers.count(bit) || !drivers.at(bit)) return false;
		auto cell = drivers.at(bit);
		Const a, b;
		for (auto in : sigmap(cell->getPort(ID::A))) {
			bool value;
			if (!eval(in, values, value, depth+1)) return false;
			a.append(value ? State::S1 : State::S0);
		}
		if (cell->hasPort(ID::B)) for (auto in : sigmap(cell->getPort(ID::B))) {
			bool value;
			if (!eval(in, values, value, depth+1)) return false;
			b.append(value ? State::S1 : State::S0);
		}
		Const y;
		int yw = GetSize(cell->getPort(ID::Y));
		bool sa = cell->hasParam(ID::A_SIGNED) && cell->getParam(ID::A_SIGNED).as_bool();
		bool sb = cell->hasParam(ID::B_SIGNED) && cell->getParam(ID::B_SIGNED).as_bool();
		if (cell->type == ID($eq)) y=const_eq(a,b,sa,sb,yw);
		else if (cell->type == ID($logic_not)) y=const_logic_not(a,{},sa,false,yw);
		else if (cell->type == ID($not)) y=const_not(a,{},sa,false,yw);
		else if (cell->type == ID($and)) y=const_and(a,b,sa,sb,yw);
		else if (cell->type == ID($or)) y=const_or(a,b,sa,sb,yw);
		else if (cell->type == ID($xor)) y=const_xor(a,b,sa,sb,yw);
		else if (cell->type.in(ID($reduce_or),ID($reduce_bool))) y=const_reduce_or(a,{},false,false,yw);
		else return false;
		auto signal = sigmap(cell->getPort(ID::Y));
		for (int i = 0; i < GetSize(signal); i++) if (signal[i] == bit) {
			result = y[i] == State::S1;
			return true;
		}
		return false;
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
		auto s = sigmap(pmux->getPort(ID::S));
		if (s.empty() || GetSize(s)>4) return false;
		for (auto bit:s) if (!control_support(bit,support,region)) return false;
		if (support.empty() || GetSize(support)>2) return false;
		std::vector<SigBit> sorted(support.begin(), support.end());
		std::sort(sorted.begin(), sorted.end());
		control = SigSpec(sorted);
		auto a = sigmap(pmux->getPort(ID::A)), b = sigmap(pmux->getPort(ID::B));
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
		if (--budget<=0 || depth>6 || !drivers.count(bit) || !drivers.at(bit)) return false;
		auto cell = drivers.at(bit);
		if (!editable(cell)) return false;
		region.insert(cell);
		if (cell->type.in(ID($lt), ID($gt), ID($eq)) && !cell->getPort(ID::A).is_fully_const() && !cell->getPort(ID::B).is_fully_const()) {
			predicates.insert(cell);
			return GetSize(predicates) <= 3;
		}
		if(!cell->type.in(ID($eq),ID($not),ID($logic_not),ID($and),ID($or),ID($xor)))return false;
		for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first))
			for (auto in : sigmap(port.second))
				if (!comparisons(in, predicates, region, depth+1)) return false;
		return true;
	}
	bool equal_branch(SigSpec value, const SigSpec &a, const SigSpec &b, pool<Cell *> &region) {
		if(value==a || value==b)return true;
		auto cell = root(value);
		if (!cell || !cell->type.in(ID($or), ID($and))) return false;
		auto x=extended(cell,ID::A,GetSize(value)),y=extended(cell,ID::B,GetSize(value));
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
		auto s = sigmap(pmux->getPort(ID::S));
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
			auto x = extended(cell, ID::A, w), y = extended(cell, ID::B, w);
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
		auto av = sigmap(pmux->getPort(ID::A)), bv = sigmap(pmux->getPort(ID::B));
		for (int state = 0; state < 3; state++) {
			dict<SigBit, bool> values;
			for (auto &entry : relation)
				values[sigmap(entry.first->getPort(ID::Y))[0]] = entry.second == state;
			SigSpec selected;
			if (!selected_branch(s, av, bv, width, values, selected)) return false;
			branch.push_back(selected);
		}
		bool minimum = branch[0] == a && branch[2] == b;
		bool maximum = branch[0] == b && branch[2] == a;
		if ((!minimum && !maximum) || !equal_branch(branch[1], a, b, region)) return false;
		ArithNetwork net;
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
		return commit(pmux, region, net, output);
	}
	std::pair<std::vector<int>, std::vector<int>> divmod3(ArithNetwork &net, const SigSpec &input, int width) {
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
		if(!cell->type.in(ID($div),ID($mod))||!editable(cell))return false;
		if(cell->getParam(ID::A_SIGNED).as_bool()||cell->getParam(ID::B_SIGNED).as_bool())return false;
		for(auto bit:sigmap(cell->getPort(ID::A)))if(!bit.wire&&bit!=State::S0&&bit!=State::S1)return false;
		auto divisor=sigmap(cell->getPort(ID::B));
		return GetSize(divisor)>=2&&divisor.is_fully_def()&&divisor.is_fully_const()&&divisor.as_const()==Const(3,GetSize(divisor));
	}
	bool shared_divisions() {
		dict<SigSpec,std::vector<Cell *>> groups;
		for(auto cell:module->cells())if(unsigned_div3(cell)&&GetSize(cell->getPort(ID::Y))<=32){
			auto input = without_zero_extension(sigmap(cell->getPort(ID::A)));
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
			ArithNetwork net;
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
			auto x = extended(cell, ID::A, width);
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
		ArithNetwork net;
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
		return commit(pmux,region,net,output);
	}
	bool expression(SigSpec value, int width, Polynomial &terms, pool<Cell *> &region, bool negative = false, int depth = 0)
	{
		if (--budget <= 0 || depth > 8 || GetSize(terms) > 12) return false;
		auto cell = root(value);
		if (cell && cell->type.in(ID($add), ID($sub))) {
			int yw = GetSize(cell->getPort(ID::Y));
			bool safe = yw >= width;
			if (!safe && !cell->getParam(ID::A_SIGNED).as_bool() && !cell->getParam(ID::B_SIGNED).as_bool() && cell->type == ID($add)) {
				auto a = without_zero_extension(sigmap(cell->getPort(ID::A)));
				auto b = without_zero_extension(sigmap(cell->getPort(ID::B)));
				safe = std::max(GetSize(a), GetSize(b))+1 <= yw;
			}
			if (safe) {
				region.insert(cell);
				return expression(extended(cell, ID::A, width), width, terms, region, negative, depth+1) &&
					expression(extended(cell, ID::B, width), width, terms, region, negative ^ (cell->type == ID($sub)), depth+1);
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
		ArithNetwork net;
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
		return commit(pmux, region, net, sum);
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
		ArithNetwork net;
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
		return commit(pmux, region, net, net.add(operands[0], operands[1], net.select(carries, cb)));
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
		ArithNetwork best;
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
			ArithNetwork net;
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
		return !bestout.empty() && commit(pmux, region, best, bestout);
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
				if (worker->editable(cell)) {
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
