// opt_pmuxrel 共享互补字段、交换字段和关联布尔输出；合并重复的选择与四输入逻辑节点。
// tables 模式用 32 位并行求值分解五位地址表，将输出使能并入共享 LUT 网络。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/pmux_celltypes.h"
#include <algorithm>
#include <cstdint>
#include <functional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// 规划期间建立四输入网络，按节点成本选择生成的单元。
struct RelationGraph {
	struct Node {
		SigBit bit;
		std::vector<int> inputs;
		unsigned mask;
		bool leaf;
	};
	std::vector<Node> nodes;
	dict<SigBit, int> leaves;
	std::map<std::pair<std::vector<int>, unsigned>, int> cache;
	bool overflow = false;
	RelationGraph() {
		leaf(State::S0);
		leaf(State::S1);
	}
	int leaf(SigBit bit) {
		auto found = leaves.find(bit);
		if (found != leaves.end()) return found->second;
		int id = GetSize(nodes);
		nodes.push_back({bit, {}, 0, true});
		leaves[bit] = id;
		return id;
	}
	pool<int> live(const std::vector<int> &roots) const {
		pool<int> seen;
		std::function<void(int)> visit = [&](int id) {
			if (seen.insert(id).second) for (int input : nodes[id].inputs) visit(input);
		};
		for (int id : roots) visit(id);
		return seen;
	}
	int cost(const std::vector<int> &roots) const {
		int result = 0;
		for (int id : live(roots))
			result += !nodes[id].leaf;
		return result;
	}
	int lut(const std::vector<int> &args, unsigned mask) {
		log_assert(GetSize(args) <= 4);
		std::vector<int> inputs;
		for (int id : args) {
			log_assert(id >= 0 && id < GetSize(nodes));
			if (id > 1 && std::find(inputs.begin(), inputs.end(), id) == inputs.end())
				inputs.push_back(id);
		}
		std::sort(inputs.begin(), inputs.end());
		unsigned table = 0;
		for (int value = 0; value < (1 << GetSize(inputs)); value++) {
			int old = 0;
			for (int j = 0; j < GetSize(args); j++) {
				int bit = args[j] == 1;
				if (args[j] > 1) bit = (value >> (std::lower_bound(inputs.begin(), inputs.end(), args[j])-inputs.begin())) & 1;
				old |= bit << j;
			}
			table |= ((mask >> old) & 1) << value;
		}
		for (int j = GetSize(inputs)-1; j >= 0; j--) {
			bool depends = false;
			for (int value = 0; value < (1 << GetSize(inputs)); value++)
				if (((table >> value) & 1) != ((table >> (value ^ (1 << j))) & 1)) depends = true;
			if (depends) continue;
			unsigned smaller = 0;
			for (int value = 0; value < (1 << (GetSize(inputs)-1)); value++) {
				int old = (value & ((1 << j)-1)) | ((value >> j) << (j+1));
				smaller |= ((table >> old) & 1) << value;
			}
			inputs.erase(inputs.begin()+j);
			table = smaller;
		}
		if (inputs.empty()) return table & 1;
		if (GetSize(inputs) == 1 && table == 2) return inputs[0];
		auto key = std::make_pair(inputs, table);
		auto found = cache.find(key);
		if (found != cache.end()) return found->second;
		if (nodes.size() >= 24000) {
			overflow = true;
			return 0;
		}
		int id = GetSize(nodes);
		nodes.push_back({{}, inputs, table, false});
		cache[key] = id;
		return id;
	}
	int gate(const std::vector<int> &args, unsigned mask) {
		int best = lut(args, mask), bestcost = cost({best});
		// 枚举相邻节点的部分展开，允许只合并其中一个子节点。
		for (int expand = 1; expand < (1 << GetSize(args)); expand++) {
			std::vector<int> inputs;
			bool valid = true;
			for (int j = 0; j < GetSize(args); j++) {
				if ((expand & (1 << j)) && nodes[args[j]].leaf) {
					valid = false;
					break;
				}
				auto source = (expand & (1 << j)) ? nodes[args[j]].inputs : std::vector<int>{args[j]};
				for (int id : source) if (id > 1 && std::find(inputs.begin(), inputs.end(), id) == inputs.end()) inputs.push_back(id);
			}
			if (!valid || GetSize(inputs) > 4) continue;
			unsigned table = 0;
			for (int value = 0; value < (1 << GetSize(inputs)); value++) {
				auto input_value = [&](int id) { return id < 2 ? id : (value >> (std::find(inputs.begin(), inputs.end(), id)-inputs.begin())) & 1; };
				int index = 0;
				for (int j = 0; j < GetSize(args); j++) {
					int v;
					if (expand & (1 << j)) {
						int sub = 0;
						for (int k = 0; k < GetSize(nodes[args[j]].inputs); k++)
							sub |= input_value(nodes[args[j]].inputs[k]) << k;
						v = (nodes[args[j]].mask >> sub) & 1;
					} else v = input_value(args[j]);
					index |= v << j;
				}
				table |= ((mask >> index) & 1) << value;
			}
			int candidate = lut(inputs, table), c = cost({candidate});
			if (c < bestcost) {
				best = candidate;
				bestcost = c;
			}
		}
		return best;
	}
	int mux(int a, int b, int s) { return gate({a,b,s}, 0xca); }
	int select(const std::vector<int> &data, const std::vector<int> &control, int level = 0, int prefix = 0) {
		if (level == GetSize(control)) return data[prefix];
		return mux(select(data, control, level+1, prefix), select(data, control, level+1, prefix | (1 << level)), control[level]);
	}
	int reduce(std::vector<int> data) {
		if (data.empty()) return 0;
		while (GetSize(data) > 1) {
			std::vector<int> next;
			for (int j = 0; j < GetSize(data); j += 4) {
				std::vector<int> args(data.begin()+j, data.begin()+std::min(j+4,GetSize(data)));
				next.push_back(gate(args, 0xfffe));
			}
			data = std::move(next);
		}
		return data[0];
	}
	SigSpec emit(Module *module, IdString celltype, const std::vector<int> &roots) const {
		auto used = live(roots);
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
			SigSpec input;
			for (int arg : node.inputs)
				input.append(signals[arg]);
			unsigned mask = 0;
			for (int code = 0; code < 16; code++)
				mask |= ((node.mask >> (code & ((1 << GetSize(input))-1))) & 1) << code;
			input.extend_u0(4);
			if (celltype.empty()) {
				cell->setParam(ID::WIDTH, 4);
				cell->setParam(ID::LUT, Const(mask,16));
				cell->setPort(ID::A, input);
				cell->setPort(ID::Y, wire);
			} else {
				cell->setParam(ID(lut_mask), Const(mask,16));
				cell->setParam(ID(sum_lutc_input), Const("datac"));
				cell->setPort(ID(dataa), input[0]);
				cell->setPort(ID(datab), input[1]);
				cell->setPort(ID(datac), input[2]);
				cell->setPort(ID(datad), input[3]);
				cell->setPort(ID(cin), State::S0);
				cell->setPort(ID(combout), wire);
			}
		}
		SigSpec result;
		for (int id : roots)
			result.append(signals[id]);
		return result;
	}
};

struct RelationWorker {
	Module *module;
	Design *design;
	SigMap sigmap;
	PmuxCellTypes types;
	IdString luttype;
	struct Driver { Cell *cell = nullptr; int count = 0; };
	dict<SigBit, Driver> drivers;
	dict<SigBit, pool<Cell *>> users;
	pool<SigBit> observed, kept, unknown, input_bits;
	int budget = 60000;
	RelationWorker(Module *m, Design *d, IdString t) : module(m), design(d), sigmap(m), types(m,d), luttype(t) {
		for (auto wire : m->wires()) for (auto bit : sigmap(wire)) {
			if (wire->port_input) {
				drivers[bit].count++;
				input_bits.insert(bit);
			}
			if (wire->port_output || wire->get_bool_attribute(ID::keep)) observed.insert(bit);
			if (wire->get_bool_attribute(ID::keep)) kept.insert(bit);
		}
		for (auto cell : m->cells()) for (auto &port : cell->connections()) {
			bool out = types.cell_output(cell->type,port.first), in = types.cell_input(cell->type,port.first);
			for (auto bit : sigmap(port.second)) {
				if (out) {
					auto &driver = drivers[bit];
					driver.count++;
					driver.cell = cell;
				}
				if (in || !out) users[bit].insert(cell);
				if (!in && !out) unknown.insert(bit);
				if (cell->get_bool_attribute(ID::keep)) kept.insert(bit);
			}
		}
	}
	bool unique(SigBit bit) const { return bit.wire && !unknown.count(bit) && drivers.count(bit) && drivers.at(bit).count == 1; }
	bool editable(Cell *cell) const {
		if (!design->selected(module,cell) || cell->get_bool_attribute(ID::keep) || !cell->hasPort(ID::Y)) return false;
		pool<SigBit> seen;
		for (auto &port : cell->connections()) if (types.cell_output(cell->type,port.first))
			for (auto bit : sigmap(port.second))
				if (!unique(bit) || drivers.at(bit).cell != cell || kept.count(bit) || !seen.insert(bit).second) return false;
		return true;
	}
	bool combinational(Cell *cell) const {
		return cell && !StaticCellTypes::categories.is_ff(cell->type) && types.cell_evaluable(cell->type) && cell->hasPort(ID::Y);
	}
	bool upstream(SigBit bit, const pool<SigBit> &targets, dict<SigBit,int> &state, int depth = 0) {
		if (--budget < 0 || depth > 96 || targets.count(bit) || unknown.count(bit)) return false;
		if (!bit.wire) return bit == State::S0 || bit == State::S1;
		if (!unique(bit)) return false;
		if (state.count(bit)) return state.at(bit) == 2;
		auto cell = drivers.at(bit).cell;
		if (!cell) return input_bits.count(bit);
		if (StaticCellTypes::categories.is_ff(cell->type)) return true;
		if (!combinational(cell)) return false;
		state[bit] = 1;
		for (auto &port : cell->connections()) if (types.cell_input(cell->type,port.first))
			for (auto in : sigmap(port.second)) if (!upstream(in,targets,state,depth+1)) return false;
		state[bit] = 2;
		return true;
	}
	struct Plan {
		RelationGraph graph;
		SigSpec targets;
		std::vector<int> roots;
		pool<Cell *> region, remove;
		int reference = 0;
	};
	int cell_cost(Cell *cell) const {
		int width = GetSize(cell->getPort(ID::Y));
		if (cell->type == ID($pmux)) return width * std::max(1,GetSize(cell->getPort(ID::S))-1);
		if (cell->type.in(ID($eq),ID($ne),ID($reduce_or),ID($reduce_and),ID($logic_not))) {
			int n = GetSize(cell->getPort(ID::A));
			if (cell->hasPort(ID::B))
				n = std::max(n, GetSize(cell->getPort(ID::B)));
			return std::max(1,(n+1)/3);
		}
		return width;
	}
	bool finalize(Plan &plan, bool tables = false) {
		if (plan.targets.empty() || plan.graph.overflow) return false;
		pool<SigBit> target(plan.targets.begin(),plan.targets.end()), leaves;
		if (GetSize(target) != GetSize(plan.targets)) return false;
		for (int id : plan.graph.live(plan.roots)) if (plan.graph.nodes[id].leaf && plan.graph.nodes[id].bit.wire) leaves.insert(plan.graph.nodes[id].bit);
		dict<SigBit,int> state;
		for (auto bit : leaves) if (!upstream(bit,target,state)) return false;
		plan.remove = plan.region;
		bool changed;
		do {
			changed = false;
			for (auto cell : std::vector<Cell *>(plan.remove.begin(),plan.remove.end())) {
				bool preserve = !editable(cell);
				for (auto &port : cell->connections()) if (types.cell_output(cell->type,port.first)) for (auto bit : sigmap(port.second)) {
					if (leaves.count(bit) || kept.count(bit) || unknown.count(bit)) preserve = true;
					if (target.count(bit)) continue;
					if (observed.count(bit)) preserve = true;
					for (auto user : users[bit]) if (!plan.remove.count(user)) preserve = true;
				}
				if (preserve) {
					plan.remove.erase(cell);
					changed = true;
				}
			}
		} while (changed);
		if (tables) {
			int old = 0;
			for (auto cell : plan.remove)
				old += cell_cost(cell);
			// 多输出单元的保留位不会贡献可删除成本。
			if (plan.graph.cost(plan.roots) >= old) return false;
		} else {
			int retained = 0;
			for (auto cell : plan.region) if (!plan.remove.count(cell)) {
				bool root = false;
				for (auto bit : sigmap(cell->getPort(ID::Y)))
					if (target.count(bit)) root = true;
				if (!root) retained += cell_cost(cell);
			}
			if (plan.graph.cost(plan.roots)+retained >= plan.reference) return false;
		}
		return true;
	}
	void commit(Plan &plan) {
		pool<SigBit> targets(plan.targets.begin(),plan.targets.end());
		// 改写宽单元的部分输出时，独立断开这些位的旧驱动。
		for (auto cell : plan.region) if (!plan.remove.count(cell)) {
			std::vector<std::pair<IdString,SigSpec>> updates;
			for (auto &port : cell->connections()) if (types.cell_output(cell->type,port.first)) {
				auto value = port.second, canonical = sigmap(value);
				bool changed = false;
				for (int j = 0; j < GetSize(value); j++) if (targets.count(canonical[j])) {
					value[j] = SigBit(module->addWire(NEW_ID));
					changed = true;
				}
				if (changed) updates.emplace_back(port.first,value);
			}
			for (auto &port : updates) cell->setPort(port.first,port.second);
		}
		log_assert(GetSize(plan.targets) == GetSize(plan.roots));
		auto result = plan.graph.emit(module, luttype, plan.roots);
		module->connect(plan.targets, result);
		for (auto cell : plan.remove) module->remove(cell);
	}
	struct Cube { dict<SigBit,bool> bits; };
	bool decode(SigBit bit, Cube &cube, pool<Cell *> &region) {
		if (!unique(bit) || --budget < 0) return false;
		auto cell = drivers.at(bit).cell;
		if (!cell || !editable(cell) || !cell->type.in(ID($eq),ID($logic_not)) || GetSize(cell->getPort(ID::Y)) != 1) return false;
		auto a = sigmap(cell->getPort(ID::A));
		SigSpec b(State::S0, GetSize(a));
		if (cell->type == ID($eq)) {
			b = sigmap(cell->getPort(ID::B));
			bool sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
			int width = std::max(GetSize(a), GetSize(b));
			a.extend_u0(width, sign);
			b.extend_u0(width, sign);
		}
		if (GetSize(a) > 16) return false;
		for (int j = 0; j < GetSize(a); j++) {
			auto x = a[j], y = b[j];
			if ((!x.wire && x != State::S0 && x != State::S1) || (!y.wire && y != State::S0 && y != State::S1)) return false;
			if (x == y) continue;
			if (!x.wire) std::swap(x,y);
			if (!x.wire || y.wire || (cube.bits.count(x) && cube.bits.at(x) != (y == State::S1))) return false;
			cube.bits[x] = y == State::S1;
		}
		if (cube.bits.empty() || GetSize(cube.bits) > 4) return false;
		region.insert(cell);
		return true;
	}
	struct Table {
		Cell *cell;
		SigSpec control;
		std::vector<SigSpec> data;
		pool<Cell *> region;
	};
	bool table(Cell *cell, Table &result) {
		if (!editable(cell) || cell->type != ID($pmux)) return false;
		auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S));
		if (a.empty() || GetSize(a) > 128 || GetSize(s) < 3 || GetSize(s) > 16 || GetSize(b) != GetSize(a)*GetSize(s)) return false;
		std::vector<Cube> cubes(GetSize(s));
		for (int j = 0; j < GetSize(s); j++) if (!decode(s[j],cubes[j],result.region)) return false;
		std::vector<SigBit> controls;
		for (auto &entry : cubes[0].bits)
			controls.push_back(entry.first);
		std::sort(controls.begin(), controls.end());
		int n = GetSize(controls);
		if (n < 2 || n > 4 || GetSize(s) < (1 << n)-1) return false;
		result.control = SigSpec(controls);
		result.cell = cell;
		result.data.assign(1 << n, a);
		pool<int> seen;
		for (int j = 0; j < GetSize(s); j++) {
			if (GetSize(cubes[j].bits) != n) return false;
			int code = 0;
			for (int k = 0; k < n; k++) {
				auto bit = cubes[j].bits.find(controls[k]);
				if (bit == cubes[j].bits.end()) return false;
				if (bit->second) code |= 1 << k;
			}
			if (!seen.insert(code).second) return false;
			result.data[code] = b.extract(j*GetSize(a),GetSize(a));
		}
		for (auto &branch : result.data) for (auto bit : branch) if (!bit.wire && bit != State::S0 && bit != State::S1) return false;
		result.region.insert(cell);
		return true;
	}
	bool xor_pair(SigBit bit, std::vector<SigBit> &leaves, pool<Cell *> &region) {
		if (!unique(bit)) return false;
		auto cell = drivers.at(bit).cell;
		if (!cell || !editable(cell) || cell->type != ID($xor)) return false;
		auto y = sigmap(cell->getPort(ID::Y));
		int offset = -1;
		for (int j = 0; j < GetSize(y); j++) if (y[j] == bit) offset = j;
		if (offset < 0) return false;
		auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B));
		bool sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
		a.extend_u0(GetSize(y), sign);
		b.extend_u0(GetSize(y), sign);
		if (!a[offset].wire || !b[offset].wire || a[offset] == b[offset]) return false;
		leaves = {a[offset], b[offset]};
		std::sort(leaves.begin(), leaves.end());
		region.insert(cell);
		return true;
	}
	struct Field {
		SigBit y;
		std::vector<SigBit> data;
	};
	bool parity(const Field &p, const Field &q, const SigSpec &control, Plan &plan) {
		if (GetSize(control) != 2) return false;
		std::vector<std::vector<SigBit>> pl(4), ql(4);
		std::vector<SigBit> common;
		pool<Cell *> region;
		for (int code = 0; code < 4; code++) {
			if (!xor_pair(p.data[code],pl[code],region) || !xor_pair(q.data[code],ql[code],region)) return false;
			std::vector<SigBit> combined;
			std::set_symmetric_difference(pl[code].begin(),pl[code].end(),ql[code].begin(),ql[code].end(),std::back_inserter(combined));
			if (combined.empty() || GetSize(combined) > 4) return false;
			if (code == 0) common = combined; else if (common != combined) return false;
		}
		auto &g = plan.graph;
		std::vector<int> controls;
		for (auto bit : control)
			controls.push_back(g.leaf(bit));
		int best = -1, bestcost = 1000;
		for (int orientation = 0; orientation < 16; orientation++) for (int order = 0; order < 2; order++) {
			std::vector<int> left, right;
			for (int code = 0; code < 4; code++) {
				left.push_back(g.leaf(pl[code][(orientation >> code)&1]));
				right.push_back(g.leaf(pl[code][1-((orientation >> code)&1)]));
			}
			std::vector<int> c = controls;
			if (order) {
				std::swap(c[0], c[1]);
				std::swap(left[1], left[2]);
				std::swap(right[1], right[2]);
			}
			int candidate = g.gate({g.select(left,c),g.select(right,c)},0x6), cost = g.cost({candidate});
			if (cost < bestcost) {
				best = candidate;
				bestcost = cost;
			}
		}
		std::vector<int> inputs;
		for (auto bit : common)
			inputs.push_back(g.leaf(bit));
		unsigned mask = 0;
		for (int code = 0; code < (1 << GetSize(inputs)); code++)
			if (__builtin_parity(unsigned(code))) mask |= 1 << code;
		int other = g.gate({best,g.lut(inputs,mask)},0x6);
		if (g.cost({best,other}) >= 10) return false;
		plan.targets.append(p.y);
		plan.targets.append(q.y);
		plan.roots.push_back(best);
		plan.roots.push_back(other);
		for (auto cell : region) plan.region.insert(cell);
		plan.reference += 14;
		return true;
	}
	bool exchange(const Field &p, const Field &q, const SigSpec &control, Plan &plan) {
		int n = GetSize(control), count = 1 << n;
		if (n < 3 || n > 4) return false;
		for (auto field : {&p, &q}) for (auto bit : field->data) {
			if (!unique(bit)) return false;
			auto cell = drivers.at(bit).cell;
			if (!cell) {
				if (!input_bits.count(bit)) return false;
			}
			else {
				if (!StaticCellTypes::categories.is_ff(cell->type) || !cell->hasPort(ID::Q)) return false;
				auto q = sigmap(cell->getPort(ID::Q));
				if (std::find(q.begin(),q.end(),bit) == q.end()) return false;
			}
		}
		int bestsplit = -1, bestmatches = -1;
		for (int split = 0; split < n; split++) {
			int matches = 0;
			for (int code = 0; code < count; code++) if (!(code & (1 << split)))
				if (p.data[code] == q.data[code | (1 << split)] && q.data[code] == p.data[code | (1 << split)]) matches++;
			if (matches > bestmatches) {
				bestmatches = matches;
				bestsplit = split;
			}
		}
		if (bestmatches < count/2-1 || bestmatches < 3) return false;
		auto &g = plan.graph;
		int swap = g.leaf(control[bestsplit]);
		std::vector<int> c;
		for (int j = 0; j < n; j++) if (j != bestsplit) c.push_back(g.leaf(control[j]));
		std::vector<int> u, v;
		for (int group = 0; group < count/2; group++) {
			int even = (group & ((1 << bestsplit)-1)) | ((group >> bestsplit) << (bestsplit+1)), odd = even | (1 << bestsplit);
			u.push_back(g.mux(g.leaf(p.data[even]),g.leaf(q.data[odd]),swap));
			v.push_back(g.mux(g.leaf(q.data[even]),g.leaf(p.data[odd]),swap));
		}
		auto shared_select = [&](const std::vector<int> &data) {
			std::vector<int> terms;
			std::vector<int> high(c.begin()+1,c.end());
			for (int group = 0; group < GetSize(data)/2; group++) {
				unsigned table = 1 << group;
				int enable = g.lut(high, table);
				terms.push_back(g.gate({data[2*group],data[2*group+1],c[0],enable},0xca00));
			}
			return g.reduce(terms);
		};
		int selected_u = shared_select(u), selected_v = shared_select(v);
		int outp = g.mux(selected_u,selected_v,swap), outq = g.mux(selected_v,selected_u,swap);
		if (g.cost({outp,outq}) >= 2*(count-1)) return false;
		plan.targets.append(p.y);
		plan.targets.append(q.y);
		plan.roots.push_back(outp);
		plan.roots.push_back(outq);
		plan.reference += 2*(count-1);
		return true;
	}
	bool coarse(const std::vector<Table> &tables, Plan &plan) {
		std::vector<Field> fields;
		for (auto &table : tables) {
			auto y = sigmap(table.cell->getPort(ID::Y));
			for (int j = 0; j < GetSize(y); j++) {
				Field field{y[j], {}};
				for (auto &data : table.data)
					field.data.push_back(data[j]);
				fields.push_back(std::move(field));
			}
		}
		if (GetSize(fields) > 128) return false;
		pool<int> used;
		for (int j = 0; j < GetSize(fields); j++) if (!used.count(j)) for (int k = j+1; k < GetSize(fields); k++) if (!used.count(k)) {
			if (--budget < 0) return false;
			if (parity(fields[j],fields[k],tables[0].control,plan) || exchange(fields[j],fields[k],tables[0].control,plan)) {
				used.insert(j);
				used.insert(k);
				break;
			}
		}
		if (plan.targets.empty()) return false;
		for (auto &table : tables) for (auto cell : table.region) plan.region.insert(cell);
		return finalize(plan);
	}
	struct TableBits {
		dict<SigBit, std::vector<SigBit>> inputs;
		pool<SigBit> inverted;
		dict<SigBit, uint32_t> masks;
	};
	bool table_inputs(Cell *cell, SigBit bit, std::vector<SigBit> &inputs, bool &inverted) {
		if (!cell->hasPort(ID::A) || !cell->hasPort(ID::Y)) return false;
		auto a = sigmap(cell->getPort(ID::A)), y = sigmap(cell->getPort(ID::Y));
		if (a.empty() || y.empty() || GetSize(a) > 128 || GetSize(y) > 128) return false;
		int offset = -1;
		for (int j = 0; j < GetSize(y); j++) if (y[j] == bit) offset = j;
		if (offset < 0) return false;
		auto parameter = [&](IdString name, int expected) {
			return cell->hasParam(name) && cell->getParam(name).is_fully_def() && cell->getParam(name).as_int() == expected;
		};
		bool mux = cell->type.in(ID($mux), ID($_MUX_));
		if (mux) {
			if (GetSize(cell->connections()) != 4 || !cell->hasPort(ID::B) || !cell->hasPort(ID::S)) return false;
			auto b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S));
			if (GetSize(a) != GetSize(y) || GetSize(b) != GetSize(y) || GetSize(s) != 1) return false;
			if (cell->type == ID($mux) ? !parameter(ID::WIDTH, GetSize(y)) : GetSize(y) != 1) return false;
			inputs = {a[offset], b[offset], s[0]};
			return true;
		}
		if (GetSize(cell->connections()) != 2) return false;
		if (cell->type.in(ID($_NOT_), ID($_BUF_))) {
			if (GetSize(a) != 1 || GetSize(y) != 1) return false;
			inverted = cell->type == ID($_NOT_);
			inputs = {a[0]};
			return true;
		}
		if (cell->type == ID($buf)) {
			if (GetSize(a) != GetSize(y) || !parameter(ID::WIDTH, GetSize(y))) return false;
			inputs = {a[offset]};
			return true;
		}
		if (!cell->type.in(ID($not), ID($pos)) || !parameter(ID::A_WIDTH, GetSize(a)) ||
		    !parameter(ID::Y_WIDTH, GetSize(y)) || !cell->hasParam(ID::A_SIGNED) ||
		    !cell->getParam(ID::A_SIGNED).is_fully_def() || GetSize(cell->getParam(ID::A_SIGNED)) != 1) return false;
		bool sign = cell->getParam(ID::A_SIGNED).as_bool();
		inputs = {offset < GetSize(a) ? a[offset] : sign ? a[GetSize(a)-1] : SigBit(State::S0)};
		inverted = cell->type == ID($not);
		return true;
	}
	bool cone(SigBit bit, pool<SigBit> &leaves, pool<Cell *> &region, dict<SigBit,int> &state, TableBits &bits, int depth = 0) {
		if (--budget < 0 || depth > 32 || GetSize(region) > 128 || unknown.count(bit) || kept.count(bit)) return false;
		if (!bit.wire) return bit == State::S0 || bit == State::S1;
		if (!unique(bit)) return false;
		if (state.count(bit)) return state.at(bit) == 2;
		auto cell = drivers.at(bit).cell;
		if (!cell) {
			if (!input_bits.count(bit)) return false;
			leaves.insert(bit);
			return GetSize(leaves) <= 5;
		}
		if (!editable(cell)) return false;
		std::vector<SigBit> inputs;
		bool inverted = false;
		if (!table_inputs(cell,bit,inputs,inverted)) return false;
		state[bit] = 1;
		region.insert(cell);
		if (GetSize(region) > 128) return false;
		for (auto input : inputs) if (!cone(input,leaves,region,state,bits,depth+1)) return false;
		bits.inputs[bit] = std::move(inputs);
		if (inverted) bits.inverted.insert(bit);
		state[bit] = 2;
		return true;
	}
	uint32_t table_mask(SigBit bit, TableBits &bits) {
		if (!bit.wire) {
			log_assert(bit == State::S0 || bit == State::S1);
			return bit == State::S1 ? UINT32_MAX : 0;
		}
		auto found = bits.masks.find(bit);
		if (found != bits.masks.end()) return found->second;
		auto &inputs = bits.inputs.at(bit);
		log_assert(GetSize(inputs) == 1 || GetSize(inputs) == 3);
		uint32_t value = table_mask(inputs[0],bits);
		if (GetSize(inputs) == 3) {
			uint32_t b = table_mask(inputs[1],bits), s = table_mask(inputs[2],bits);
			value = (~s & value) | (s & b);
		} else if (bits.inverted.count(bit)) {
			value = ~value;
		}
		bits.masks[bit] = value;
		return value;
	}
	bool tables(Plan &plan) {
		pool<SigBit> endpoints;
		for (auto bit : observed) endpoints.insert(bit);
		for (auto cell : module->cells()) if (StaticCellTypes::categories.is_ff(cell->type) && cell->hasPort(ID::D))
			for (auto bit : sigmap(cell->getPort(ID::D))) endpoints.insert(bit);
		int candidates = 0;
		for (auto cell : module->selected_cells()) {
			if (budget <= 0 || candidates >= 32) break;
			if (cell->type != ID($mux) || !editable(cell)) continue;
			auto y = sigmap(cell->getPort(ID::Y));
			if (GetSize(y) < 2 || GetSize(y) > 128) continue;
			std::vector<SigBit> root_inputs;
			bool root_inverted = false;
			if (!table_inputs(cell,y[0],root_inputs,root_inverted)) continue;
			bool visible = true;
			for (auto bit : y) if (!endpoints.count(bit)) visible = false;
			if (!visible) continue;
			auto s = sigmap(cell->getPort(ID::S));
			if (GetSize(s) != 1 || !unique(s[0]) || !input_bits.count(s[0]) || drivers.at(s[0]).cell || kept.count(s[0])) continue;
			auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B));
			if (GetSize(a) != GetSize(y) || GetSize(b) != GetSize(y)) continue;
			bool active_high = a.is_fully_zero();
			if (!active_high && !b.is_fully_zero()) continue;
			auto data = active_high ? b : a;
			pool<SigBit> support;
			pool<Cell *> region;
			dict<SigBit, int> state;
			TableBits bits;
			bool valid = true;
			for (auto bit : data) if (!cone(bit,support,region,state,bits)) {
				valid = false;
				break;
			}
			if (!valid || GetSize(support) != 5 || support.count(s[0]) || GetSize(region) < 3) continue;
			candidates++;
			std::vector<SigBit> inputs(support.begin(), support.end());
			std::sort(inputs.begin(), inputs.end());
			if ((budget -= GetSize(bits.inputs)) < 0) break;
			const uint32_t patterns[] = {0xaaaaaaaaU,0xccccccccU,0xf0f0f0f0U,0xff00ff00U,0xffff0000U};
			for (int j = 0; j < 5; j++) bits.masks[inputs[j]] = patterns[j];
			std::vector<uint32_t> tables;
			for (auto bit : data)
				tables.push_back(table_mask(bit, bits));
			// 整字真值表必须实际使用全部五个地址输入。
			for (int j = 0; j < 5; j++) {
				bool depends = false;
				for (auto table : tables) for (int code = 0; code < 32; code++)
					if (((table >> code) & 1) != ((table >> (code ^ (1 << j))) & 1)) depends = true;
				if (!depends) valid = false;
			}
			if (!valid) continue;
			std::vector<int> args;
			for (auto input : inputs)
				args.push_back(plan.graph.leaf(input));
			int enable = plan.graph.leaf(s[0]);
			for (int j = 0; j < GetSize(y); j++) {
				auto shared = plan.graph.live(plan.roots);
				int best = -1, bestcost = 4;
				for (int split = 0; split < 5; split++) {
					std::vector<int> rest = args;
					rest.erase(rest.begin()+split);
					unsigned low = 0, high = 0;
					for (int code = 0; code < 16; code++) {
						int index = (code & ((1 << split)-1)) | ((code >> split) << (split+1));
						low |= ((tables[j] >> index) & 1) << code;
						high |= ((tables[j] >> (index | (1 << split))) & 1) << code;
					}
					int left = plan.graph.lut(rest,low), right = plan.graph.lut(rest,high);
					int root = plan.graph.lut({left,right,args[split],enable},active_high ? 0xca00 : 0x00ca), cost = 0;
					for (int id : plan.graph.live({root})) if (!shared.count(id) && !plan.graph.nodes[id].leaf) cost++;
					if (cost < bestcost) {
						best = root;
						bestcost = cost;
					}
				}
				log_assert(best >= 0);
				plan.targets.append(y[j]);
				plan.roots.push_back(best);
			}
			if (plan.graph.overflow) return false;
			plan.region.insert(cell);
			for (auto source : region)
				plan.region.insert(source);
		}
		return finalize(plan,true);
	}
};

struct OptPmuxRelPass : public Pass {
	OptPmuxRelPass() : Pass("opt_pmuxrel", "share complete-table output relations and bounded truth tables") {}
	void help() override {
		log("    opt_pmuxrel [-coarse | -tables] [-lut4 <celltype>] [selection]\n\n");
		log("Default -coarse: share complementary XOR fields and exchanged output fields\n");
		log("in complete two- to four-bit equality tables, after width reduction.\n");
		log("-tables: decompose explicitly enabled constant tables of five independent\n");
		log("module input address bits after memory_map and opt -undriven -fine.\n");
		log("Both modes plan bounded shared single-output LUT4 networks and preserve\n");
		log("registers, initialization, reset, external users, and unmatched output bits.\n");
		log("Default output cells are $lut. -lut4 emits Intel dataa/b/c/d, combout, cin=0,\n");
		log("lut_mask and sum_lutc_input=datac cells of the specified type.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		bool tables = false, mode = false;
		IdString luttype;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-tables" || args[argidx] == "-coarse") {
				if (mode) log_cmd_error("Specify exactly one stage.\n");
				tables = args[argidx] == "-tables";
				mode = true;
				continue;
			}
			if (args[argidx] == "-lut4") {
				if (argidx+1 >= args.size()) log_cmd_error("Missing cell type for -lut4.\n");
				luttype = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args,argidx,design);
		for (auto module : design->selected_modules()) {
			if (tables && GetSize(module->cells()) > 4096) continue;
			if (!tables && GetSize(module->cells()) > 20000) continue;
			bool candidate = false;
			for (auto cell : module->selected_cells()) {
				if (tables && cell->type == ID($mux) && GetSize(cell->getPort(ID::Y)) >= 2 &&
				    GetSize(cell->getPort(ID::S)) == 1 && cell->getPort(ID::S)[0].wire && cell->getPort(ID::S)[0].wire->port_input &&
				    (cell->getPort(ID::A).is_fully_zero() || cell->getPort(ID::B).is_fully_zero())) {
					candidate = true;
					break;
				}
				if (!tables && cell->type == ID($pmux) && GetSize(cell->getPort(ID::S)) >= 3 && GetSize(cell->getPort(ID::S)) <= 16) candidate = true;
			}
			if (!candidate) continue;
			RelationWorker worker(module,design,luttype);
			if (tables) {
				RelationWorker::Plan plan;
				if (worker.tables(plan)) worker.commit(plan);
			} else {
				dict<SigSpec,std::vector<RelationWorker::Table>> groups;
				for (auto cell : module->selected_cells()) {
					if (worker.budget <= 0) break;
					RelationWorker::Table table;
					if (worker.table(cell,table)) groups[table.control].push_back(std::move(table));
				}
				std::vector<RelationWorker::Plan> plans;
				pool<Cell *> reserved;
				for (auto &group : groups) {
					RelationWorker::Plan plan;
					if (!worker.coarse(group.second,plan)) continue;
					bool overlap = false;
					for (auto cell : plan.region) if (reserved.count(cell)) overlap = true;
					if (overlap) continue;
					for (auto cell : plan.region) reserved.insert(cell);
					plans.push_back(std::move(plan));
				}
				for (auto &plan : plans) worker.commit(plan);
			}
		}
	}
} OptPmuxRelPass;

PRIVATE_NAMESPACE_END
