// opt_pmuxselect 恢复互斥选择编码，以共享选择图、互补关系和数据余因子缩减逻辑。
// 复用控制变量排列与端口分类，按结构成本选择字段分解和共享网络。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "passes/opt/pmux_celltypes.h"
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxSelectGraph {
	struct Node {
		int kind;
		SigBit bit;
		int a, b, s;
	};
	std::vector<Node> nodes;
	dict<SigBit, int> leaves;
	dict<std::tuple<int, int, int, int>, int> unique;
	bool overflow = false;
	int complements = 0;

	int leaf(SigBit bit) {
		if (bit == State::S1) return leaf(State::S0) ^ 1;
		auto found = leaves.find(bit);
		if (found != leaves.end()) return found->second;
		int ref = 2 * GetSize(nodes);
		nodes.push_back({0, bit, 0, 0, 0});
		leaves[bit] = ref;
		return ref;
	}
	int flip(int ref) {
		log_assert(ref >= 0 && ref/2 < GetSize(nodes));
		if (nodes[ref/2].kind == 0 && !nodes[ref/2].bit.wire && nodes[ref/2].bit.data > State::S1)
			return leaf(State::Sx);
		return ref ^ 1;
	}
	int node(int kind, int a, int b, int s = 0) {
		auto key = std::make_tuple(kind, a, b, s);
		auto found = unique.find(key);
		if (found != unique.end()) return found->second;
		if (GetSize(nodes) >= 8192) {
			overflow = true;
			return leaf(State::Sx);
		}
		int ref = 2 * GetSize(nodes);
		nodes.push_back({kind, SigBit(), a, b, s});
		unique[key] = ref;
		return ref;
	}
	int xorgate(int a, int b) {
		int zero = leaf(State::S0), inv = (a ^ b) & 1;
		a &= ~1;
		b &= ~1;
		if (a == zero) return b ^ inv;
		if (b == zero) return a ^ inv;
		if (a == b) return zero ^ inv;
		if (b < a) std::swap(a, b);
		return node(2, a, b) ^ inv;
	}
	int mux(int s, int a, int b) {
		if (a == b) return a;
		int zero = leaf(State::S0);
		if (s == zero || s == (zero ^ 1)) return s == zero ? a : b;
		if (s & 1) {
			std::swap(a, b);
			s ^= 1;
		}
		if ((a ^ b) == 1) {
			complements++;
			return xorgate(a, s);
		}
		int inv = a & 1;
		if (inv) {
			a = flip(a);
			b = flip(b);
		}
		return node(1, a, b, s) ^ inv;
	}
	void reachable(int ref, pool<int> &seen, pool<int> &inverted) const {
		log_assert(ref >= 0 && ref/2 < GetSize(nodes));
		if (ref & 1) inverted.insert(ref/2);
		if (!seen.insert(ref/2).second) return;
		auto &n = nodes[ref/2];
		if (n.kind) {
			reachable(n.a, seen, inverted);
			reachable(n.b, seen, inverted);
		}
		if (n.kind == 1) reachable(n.s, seen, inverted);
	}
	std::pair<int, int> cost(const std::vector<int> &roots) const {
		pool<int> seen, inverted;
		for (int ref : roots) reachable(ref, seen, inverted);
		int count = 0, gates = 0;
		for (int index : seen) if (nodes[index].kind) {
			count++;
			gates += nodes[index].kind == 1 ? 3 : 4;
		}
		for (int index : inverted) if (nodes[index].kind || nodes[index].bit.wire) {
			count++;
			gates++;
		}
		return {count, gates};
	}
};

struct PmuxSelectGateCost {
	struct Node { int type, a, b, c; };
	std::vector<Node> nodes = {{0, 0, 0, 0}, {0, 0, 0, 0}};
	dict<SigBit, int> leaves;
	dict<std::tuple<int, int, int, int>, int> unique;
	int leaf(SigBit bit) {
		if (!bit.wire && bit.data <= State::S1) return bit.data == State::S1;
		auto found = leaves.find(bit);
		if (found != leaves.end()) return found->second;
		int index = GetSize(nodes);
		nodes.push_back({0, 0, 0, 0});
		leaves[bit] = index;
		return index;
	}
	int gate(int type, int a, int b = 0, int c = 0) {
		if (type == 1 && a < 2) return a ^ 1;
		if (type == 2 || type == 3) {
			if (a == b) return a;
			if (a > b) std::swap(a, b);
			if (type == 2) {
				if (a == 0) return 0;
				if (a == 1) return b;
			}
			if (type == 3) {
				if (a == 0) return b;
				if (a == 1) return 1;
			}
		}
		if (type == 4) {
			if (a == b) return a;
			if (c < 2) return c ? b : a;
		}
		auto key = std::make_tuple(type, a, b, c);
		auto found = unique.find(key);
		if (found != unique.end()) return found->second;
		int index = GetSize(nodes);
		nodes.push_back({type, a, b, c});
		unique[key] = index;
		return index;
	}
	int reduce(std::vector<int> bits) {
		if (bits.empty()) return 0;
		while (GetSize(bits) > 1) {
			std::vector<int> next;
			for (int i = 0; i < GetSize(bits); i += 2) next.push_back(i+1 < GetSize(bits) ? gate(3, bits[i], bits[i+1]) : bits[i]);
			bits = std::move(next);
		}
		return bits[0];
	}
	std::vector<int> pmux(const SigSpec &a, const SigSpec &b, const std::vector<int> &select) {
		log_assert(GetSize(b) == GetSize(a)*GetSize(select));
		int any = reduce(select);
		std::vector<int> roots;
		for (int j = 0; j < GetSize(a); j++) {
			std::vector<int> terms;
			for (int i = 0; i < GetSize(select); i++) {
				auto bit = b[i*GetSize(a)+j];
				terms.push_back(!bit.wire && bit.data > State::S1 ? 0 : gate(2, leaf(bit), select[i]));
			}
			int value = reduce(terms);
			roots.push_back(!a[j].wire && a[j].data > State::S1 ? value : gate(4, leaf(a[j]), value, any));
		}
		return roots;
	}
	int visit(int index, pool<int> &seen) const {
		if (!seen.insert(index).second || nodes[index].type == 0) return 0;
		auto &n = nodes[index];
		return (n.type == 4 ? 3 : 1) + visit(n.a, seen) + (n.type != 1 ? visit(n.b, seen) : 0) + (n.type == 4 ? visit(n.c, seen) : 0);
	}
	int cost(const std::vector<int> &roots) const {
		pool<int> seen;
		int result = 0;
		for (int root : roots) result += visit(root, seen);
		return result;
	}
};

struct PmuxSelectWorker {
	Module *module;
	Design *design;
	SigMap sigmap;
	PmuxCellTypes types;
	struct Driver { Cell *cell = nullptr; int offset = 0; int count = 0; };
	dict<SigBit, Driver> drivers;
	pool<SigBit> kept, unknown;
	int work = 2000000;
	bool exhausted = false;

	PmuxSelectWorker(Module *m, Design *d) : module(m), design(d), sigmap(m), types(m, d) {
		for (auto wire : module->wires()) {
			bool keep = wire->get_bool_attribute(ID::keep);
			if (!wire->port_input && !wire->port_output && !keep) continue;
			for (auto bit : sigmap(wire)) {
				if (wire->port_input) drivers[bit].count++;
				if (keep) kept.insert(bit);
			}
		}
		for (auto cell : module->cells()) for (auto &port : cell->connections()) {
			auto signal = sigmap(port.second);
			bool output = types.cell_output(cell->type, port.first), input = types.cell_input(cell->type, port.first);
			for (int i = 0; i < GetSize(signal); i++) {
				auto bit = signal[i];
				if (output) {
					auto &entry = drivers[bit];
					entry.count++;
					entry.cell = cell;
					entry.offset = i;
				}
				if (!input && !output) unknown.insert(bit);
				if (cell->get_bool_attribute(ID::keep)) kept.insert(bit);
			}
		}
	}
	bool spend(int amount = 1) {
		work -= amount;
		if (work < 0) exhausted = true;
		return !exhausted;
	}
	bool unique(SigBit bit) const {
		return bit.wire && !unknown.count(bit) && drivers.count(bit) && drivers.at(bit).count == 1;
	}
	bool editable(Cell *cell) const {
		if (!design->selected(module, cell) || cell->get_bool_attribute(ID::keep) || !cell->hasPort(ID::Y)) return false;
		pool<SigBit> outputs;
		for (auto bit : sigmap(cell->getPort(ID::Y)))
			if (!unique(bit) || drivers.at(bit).cell != cell || kept.count(bit) || !outputs.insert(bit).second) return false;
		return true;
	}
	SigBit operand(Cell *cell, IdString port, int offset) {
		auto signal = sigmap(cell->getPort(port));
		auto parameter = port == ID::A ? ID::A_SIGNED : ID::B_SIGNED;
		bool sign = cell->hasParam(parameter) && cell->getParam(parameter).as_bool();
		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor)))
			sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
		return offset < GetSize(signal) ? signal[offset] : sign && !signal.empty() ? signal.back() : SigBit(State::S0);
	}
	struct Cube { dict<SigBit, bool> bits; bool dead = false; };
	bool constraint(Cube &cube, SigBit a, SigBit b) {
		if ((!a.wire && a.data > State::S1) || (!b.wire && b.data > State::S1)) return false;
		if (a == b) return true;
		if (a.wire && b.wire) return false;
		if (!a.wire && !b.wire) { cube.dead = true; return true; }
		if (!a.wire) std::swap(a, b);
		bool value = b == State::S1;
		if (cube.bits.count(a) && cube.bits.at(a) != value) cube.dead = true;
		cube.bits[a] = value;
		return true;
	}
	bool decode(SigBit bit, Cube &cube) {
		if (!bit.wire) {
			if (bit == State::S0) { cube.dead = true; return true; }
			return bit == State::S1;
		}
		if (!unique(bit) || !drivers.at(bit).cell) return false;
		auto entry = drivers.at(bit); auto cell = entry.cell;
		if (!cell->type.in(ID($eq), ID($logic_not)) || !cell->hasPort(ID::Y)) return false;
		if (entry.offset) { cube.dead = true; return true; }
		auto a = sigmap(cell->getPort(ID::A));
		if (GetSize(a) != cell->getParam(ID::A_WIDTH).as_int() || GetSize(a) > 256) return false;
		SigSpec b(State::S0, GetSize(a));
		if (cell->type == ID($eq)) {
			b = sigmap(cell->getPort(ID::B));
			if (GetSize(b) != cell->getParam(ID::B_WIDTH).as_int() || GetSize(b) > 256) return false;
			int width = std::max(GetSize(a), GetSize(b));
			bool sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
			a.extend_u0(width, sign); b.extend_u0(width, sign);
		}
		for (int i = 0; i < GetSize(a); i++) if (!constraint(cube, a[i], b[i])) return false;
		return true;
	}
	// 只穿过组合单元检查依赖；时序单元的输出作为独立输入边界。
	bool upstream(SigBit bit, const pool<SigBit> &outputs, dict<SigBit, int> &state) {
		if (!spend() || outputs.count(bit) || unknown.count(bit)) return false;
		if (!bit.wire) return !drivers.count(bit);
		if (!unique(bit)) return false;
		if (state.count(bit)) return state.at(bit) == 2;
		auto cell = drivers.at(bit).cell;
		if (!cell || RTLIL::builtin_ff_cell_types().count(cell->type)) { state[bit] = 2; return true; }
		if (!types.cell_evaluable(cell->type)) return false;
		state[bit] = 1;
		for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first))
			for (auto input : sigmap(port.second)) if (!upstream(input, outputs, state)) return false;
		state[bit] = 2;
		return true;
	}
	struct Function { std::vector<SigBit> support; std::vector<State> table; };
	Function atom(SigBit bit) {
		if (!bit.wire) return {{}, {bit.data}};
		return {{bit}, {State::S0, State::S1}};
	}
	void minimize(Function &f) {
		for (int i = GetSize(f.support)-1; i >= 0; i--) {
			bool equal = true;
			for (int c = 0; c < GetSize(f.table); c++) if (!(c & (1 << i)) && f.table[c] != f.table[c | (1 << i)]) equal = false;
			if (!equal) continue;
			std::vector<State> table;
			for (int c = 0; c < GetSize(f.table); c++) if (!(c & (1 << i))) table.push_back(f.table[c]);
			f.support.erase(f.support.begin()+i);
			f.table = std::move(table);
		}
	}
	State evaluate(const Function &f, const std::vector<SigBit> &support, int code) {
		int index = 0;
		for (int i = 0; i < GetSize(f.support); i++) {
			auto found = std::lower_bound(support.begin(), support.end(), f.support[i]);
			log_assert(found != support.end() && *found == f.support[i]);
			if (code & (1 << (found-support.begin()))) index |= 1 << i;
		}
		return f.table[index];
	}
	Function expression(SigBit bit, int code, const dict<SigBit, int> &controls,
			dict<std::pair<SigBit, int>, Function> &cache, pool<SigBit> &active, pool<Cell *> &expanded, int depth) {
		if (controls.count(bit)) return atom((code & (1 << controls.at(bit))) ? State::S1 : State::S0);
		if (!bit.wire) return atom(bit);
		auto key = std::make_pair(bit, code);
		if (cache.count(key)) return cache.at(key);
		if (!spend() || depth == 0 || GetSize(cache) >= 65536 || GetSize(expanded) >= 4096 || !unique(bit) || !drivers.at(bit).cell || kept.count(bit)) return atom(bit);
		if (!active.insert(bit).second) { exhausted = true; return atom(bit); }
		auto entry = drivers.at(bit); auto cell = entry.cell;
		bool unary = cell->type.in(ID($not), ID($pos), ID($buf));
		bool binary = cell->type.in(ID($and), ID($or), ID($xor), ID($xnor));
		bool mux = cell->type == ID($mux) && GetSize(cell->getPort(ID::S)) == 1;
		Function result = atom(bit);
		if (unary || binary || mux) {
			std::vector<Function> args;
			args.push_back(expression(operand(cell, ID::A, entry.offset), code, controls, cache, active, expanded, depth-1));
			if (binary || mux) args.push_back(expression(operand(cell, ID::B, entry.offset), code, controls, cache, active, expanded, depth-1));
			if (mux) args.push_back(expression(sigmap(cell->getPort(ID::S))[0], code, controls, cache, active, expanded, depth-1));
			pool<SigBit> support;
			for (auto &arg : args) for (auto input : arg.support) support.insert(input);
			if (GetSize(support) <= 3) {
				result.support.assign(support.begin(), support.end());
				std::sort(result.support.begin(), result.support.end());
				result.table.clear();
				for (int c = 0; c < (1 << GetSize(result.support)); c++) {
					std::vector<Const> values;
					for (auto &arg : args) values.emplace_back(evaluate(arg, result.support, c));
					Const value;
					if (mux) value = const_mux(values[0], values[1], values[2]);
					else if (cell->type.in(ID($buf), ID($pos))) value = values[0];
					else value = CellTypes::eval(cell->type, values[0], binary ? values[1] : Const(), false, false, 1);
					result.table.push_back(value[0]);
				}
				bool defined = true;
				for (auto value : result.table) if (value > State::S1) defined = false;
				// 成本分析使用具有确定结果的分支函数。
				if (defined) {
					minimize(result);
					expanded.insert(cell);
				}
				else result = atom(bit);
			}
		}
		active.erase(bit);
		cache[key] = result;
		return result;
	}
	int build(PmuxSelectGraph &graph, const std::vector<int> &table, const std::vector<SigBit> &order, int depth = 0, int code = 0) {
		if (!spend()) { graph.overflow = true; return graph.leaf(State::Sx); }
		if (depth == GetSize(order)) return table[code];
		int a = build(graph, table, order, depth+1, code), b = build(graph, table, order, depth+1, code | (1 << depth));
		return graph.mux(graph.leaf(order[depth]), a, b);
	}
	int function_graph(PmuxSelectGraph &graph, const Function &f) {
		std::vector<int> values;
		for (auto value : f.table) values.push_back(graph.leaf(value));
		return build(graph, values, f.support);
	}
	int reference_tree(const std::vector<SigBit> &table, const std::vector<int> &order, int depth, int code, std::map<std::vector<SigBit>, int> &memo) {
		std::vector<SigBit> values;
		for (int c = 0; c < (1 << (GetSize(order)-depth)); c++) {
			int index = code;
			for (int i = depth; i < GetSize(order); i++) if (c & (1 << (i-depth))) index |= 1 << order[i];
			values.push_back(table[index]);
		}
		if (!spend(GetSize(values))) return 0;
		bool same = true;
		for (auto value : values) if (value != values[0]) same = false;
		if (same) return 0;
		if (memo.count(values)) return 0;
		memo[values] = 1;
		return 1 + reference_tree(table, order, depth+1, code, memo) + reference_tree(table, order, depth+1, code | (1 << order[depth]), memo);
	}
	struct Plan {
		PmuxSelectGraph graph;
		std::vector<int> roots;
		int reference = 0, support_saved = 0, swaps = 0;
		std::vector<int> field_masks;
		bool fields = false;
		int count = 0, gates = 0;
	};
	bool candidate(Cell *cell, Plan &best, std::vector<SigBit> &controls, std::vector<std::vector<SigBit>> &tables) {
		if (!editable(cell)) return false;
		auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S)), y = sigmap(cell->getPort(ID::Y));
		int width = GetSize(y), branches = GetSize(s);
		if (width < 1 || width > 256 || branches < 3 || branches > 64 || cell->getParam(ID::WIDTH).as_int() != width ||
			cell->getParam(ID::S_WIDTH).as_int() != branches || GetSize(a) != width || GetSize(b) != width*branches) return false;
		std::vector<Cube> cubes(branches); pool<SigBit> support, outputs;
		for (auto bit : y) outputs.insert(bit);
		for (int i = 0; i < branches; i++) {
			if (!decode(s[i], cubes[i])) return false;
			if (!cubes[i].dead) for (auto &constraint : cubes[i].bits) support.insert(constraint.first);
		}
		if (support.empty() || GetSize(support) > 6 || width*(1 << GetSize(support)) > 16384) return false;
		controls.assign(support.begin(), support.end()); std::sort(controls.begin(), controls.end());
		dict<SigBit, int> positions;
		for (int i = 0; i < GetSize(controls); i++) positions[controls[i]] = i;
		dict<SigBit, int> dependency;
		for (auto bit : a) if (!upstream(bit, outputs, dependency)) return false;
		for (auto bit : b) if (!upstream(bit, outputs, dependency)) return false;
		for (auto bit : controls) if (!upstream(bit, outputs, dependency)) return false;
		int size = 1 << GetSize(controls);
		tables.assign(width, {});
		for (int c = 0; c < size; c++) {
			int branch = -1;
			for (int i = 0; i < branches; i++) {
				bool match = !cubes[i].dead;
				for (auto &constraint : cubes[i].bits) if (bool(c & (1 << positions.at(constraint.first))) != constraint.second) match = false;
				if (!match) continue;
				if (branch != -1) return false;
				branch = i;
			}
			for (int j = 0; j < width; j++) tables[j].push_back(branch < 0 ? a[j] : b[branch*width+j]);
		}
		std::vector<std::vector<Function>> functions(width);
		dict<std::pair<SigBit, int>, Function> cache; pool<SigBit> active; pool<Cell *> expanded;
		std::vector<int> masks;
		int field_choices = 0;
		for (int j = 0; j < width; j++) {
			int mask = 0;
			for (int i = 0; i < GetSize(controls); i++)
				for (int c = 0; c < size; c++) if (!(c & (1 << i)) && tables[j][c] != tables[j][c | (1 << i)]) { mask |= 1 << i; break; }
			masks.push_back(mask);
			field_choices += 1 << __builtin_popcount(unsigned(mask));
			for (int c = 0; c < size; c++) functions[j].push_back(expression(tables[j][c], c, positions, cache, active, expanded, 8));
		}
		PmuxSelectGateCost old_cost;
		std::vector<int> original_select;
		for (auto bit : s) original_select.push_back(old_cost.leaf(bit));
		int original_gates = old_cost.cost(old_cost.pmux(a, b, original_select));
		std::vector<std::vector<int>> orders;
		for (int reverse = 0; reverse < 2; reverse++) for (int shift = 0; shift < GetSize(controls); shift++) {
			std::vector<int> order;
			for (int i = 0; i < GetSize(controls); i++) order.push_back(reverse ? (shift-i+GetSize(controls))%GetSize(controls) : (shift+i)%GetSize(controls));
			if (std::find(orders.begin(), orders.end(), order) == orders.end()) orders.push_back(order);
		}
		bool accepted = false;
		for (auto &order : orders) {
			Plan plan;
			std::vector<SigBit> selectors;
			for (int i : order) selectors.push_back(controls[i]);
			std::vector<int> permuted(size);
			for (int c = 0; c < size; c++)
				for (int i = 0; i < GetSize(order); i++)
					if (c & (1 << i)) permuted[c] |= 1 << order[i];
			for (int j = 0; j < width; j++) {
				std::map<std::vector<SigBit>, int> memo;
				plan.reference += reference_tree(tables[j], order, 0, 0, memo);
				std::vector<int> leaves(size);
				for (int c = 0; c < size; c++) {
					int index = permuted[c];
					auto &function = functions[j][index];
					leaves[c] = GetSize(function.support) <= 1 ? function_graph(plan.graph, function) : plan.graph.leaf(tables[j][index]);
				}
				int normal = build(plan.graph, leaves, selectors), result = normal;
				pool<SigBit> data;
				for (auto &function : functions[j]) for (auto bit : function.support) data.insert(bit);
				if (!data.empty() && GetSize(data) <= 3) {
					std::vector<SigBit> atoms(data.begin(), data.end()); std::sort(atoms.begin(), atoms.end());
					std::vector<int> cofactor;
					for (int d = 0; d < (1 << GetSize(atoms)); d++) {
						std::vector<int> values(size);
						for (int c = 0; c < size; c++) {
							int index = permuted[c];
							values[c] = plan.graph.leaf(evaluate(functions[j][index], atoms, d));
						}
						cofactor.push_back(build(plan.graph, values, selectors));
					}
					int swapped = build(plan.graph, cofactor, atoms);
					if (plan.graph.cost({swapped}).first < plan.graph.cost({normal}).first) {
						result = swapped;
						plan.swaps++;
					}
				}
				plan.roots.push_back(result);
				plan.support_saved += GetSize(controls) - __builtin_popcount(unsigned(masks[j]));
			}
			if (exhausted || plan.graph.overflow) return false;
			auto cost = plan.graph.cost(plan.roots);
			plan.count = cost.first;
			plan.gates = cost.second;
			// 按原始 PMUX 的数据选择数量计算字段支持缩减。
			bool field_gain = plan.support_saved > 0 && 4*field_choices <= 3*width*branches;
			int separate = 0;
			for (int root : plan.roots) separate += plan.graph.cost({root}).first;
			bool structural = plan.support_saved || plan.swaps || separate > plan.count || plan.graph.complements;
			bool graph_gain = structural && 4*plan.count <= 3*plan.reference && plan.count+2 <= plan.reference;
			if ((!graph_gain && !field_gain) || plan.gates >= original_gates) continue;
			if (!accepted || plan.count < best.count || (plan.count == best.count && plan.gates < best.gates)) {
				best = std::move(plan);
				accepted = true;
			}
		}
		// 字段选择保留原始 PMUX 的编码形式，全部编码均具有真实默认数据。
		if (accepted && best.support_saved > 0 && 4*field_choices <= 3*width*branches && best.swaps == 0 && best.graph.complements == 0) {
			PmuxSelectGateCost field_cost;
			dict<int, std::vector<int>> groups;
			for (int j = 0; j < width; j++) groups[masks[j]].push_back(j);
			std::vector<int> roots;
			for (auto &group : groups) {
				std::vector<int> indices;
				for (int i = 0; i < GetSize(controls); i++) if (group.first & (1 << i)) indices.push_back(i);
				SigSpec data;
				for (int c = 0; c < (1 << GetSize(indices)); c++) {
					int code = 0;
					for (int i = 0; i < GetSize(indices); i++) if (c & (1 << i)) code |= 1 << indices[i];
					for (int j : group.second) data.append(tables[j][code]);
				}
				if (indices.empty()) for (auto bit : data) roots.push_back(field_cost.leaf(bit));
				else {
					std::vector<int> decoders;
					for (int c = 1; c < (1 << GetSize(indices)); c++) {
						int condition = 1;
						for (int i = 0; i < GetSize(indices); i++) {
							int bit = field_cost.leaf(controls[indices[i]]);
							condition = field_cost.gate(2, condition, c & (1 << i) ? bit : field_cost.gate(1, bit));
						}
						decoders.push_back(condition);
					}
					auto group_roots = field_cost.pmux(data.extract(0, GetSize(group.second)), data.extract(GetSize(group.second), GetSize(data)-GetSize(group.second)), decoders);
					roots.insert(roots.end(), group_roots.begin(), group_roots.end());
				}
			}
			int gates = field_cost.cost(roots);
			if (gates < original_gates) {
				best.fields = true;
				best.field_masks = masks;
				best.gates = gates;
			}
		}
		return accepted;
	}
	SigBit materialize(PmuxSelectGraph &graph, int ref, dict<int, SigBit> &cache) {
		log_assert(ref >= 0 && ref/2 < GetSize(graph.nodes));
		auto found = cache.find(ref);
		if (found != cache.end()) return found->second;
		auto &node = graph.nodes[ref/2];
		SigBit value;
		if (ref & 1) {
			auto input = materialize(graph, ref ^ 1, cache);
			if (!input.wire) value = const_not(Const(input.data), Const(), false, false, 1)[0];
			else {
				auto wire = module->addWire(NEW_ID);
				module->addNot(NEW_ID, input, wire);
				value = SigBit(wire);
			}
		} else if (!node.kind) value = node.bit;
		else {
			auto a = materialize(graph, node.a, cache), b = materialize(graph, node.b, cache);
			auto wire = module->addWire(NEW_ID);
			if (node.kind == 1) module->addMux(NEW_ID, a, b, materialize(graph, node.s, cache), wire);
			else module->addXor(NEW_ID, a, b, wire);
			value = SigBit(wire);
		}
		cache[ref] = value;
		return value;
	}
	void commit(Cell *cell, Plan &plan, const std::vector<SigBit> &controls, const std::vector<std::vector<SigBit>> &tables) {
		auto y = sigmap(cell->getPort(ID::Y));
		SigSpec output;
		if (plan.fields) {
			dict<int, std::vector<int>> groups;
			for (int j = 0; j < GetSize(y); j++) groups[plan.field_masks[j]].push_back(j);
			for (auto &group : groups) {
				std::vector<int> indices;
				SigSpec select;
				for (int i = 0; i < GetSize(controls); i++) if (group.first & (1 << i)) {
					indices.push_back(i);
					select.append(controls[i]);
				}
				SigSpec data, target;
				for (int j : group.second) target.append(y[j]);
				for (int c = 0; c < (1 << GetSize(indices)); c++) {
					int code = 0;
					for (int i = 0; i < GetSize(indices); i++) if (c & (1 << i)) code |= 1 << indices[i];
					for (int j : group.second) data.append(tables[j][code]);
				}
				if (indices.empty()) module->connect(target, data);
				else {
					SigSpec decoders;
					for (int c = 1; c < (1 << GetSize(indices)); c++) {
						auto wire = module->addWire(NEW_ID);
						module->addEq(NEW_ID, select, Const(c, GetSize(indices)), wire);
						decoders.append(wire);
					}
					module->addPmux(NEW_ID, data.extract(0, GetSize(target)), data.extract(GetSize(target), GetSize(data)-GetSize(target)), decoders, target);
				}
			}
		} else {
			dict<int, SigBit> cache;
			for (int root : plan.roots) output.append(materialize(plan.graph, root, cache));
			module->connect(y, output);
		}
		module->remove(cell);
	}
};

struct OptPmuxSelectPass : public Pass {
	OptPmuxSelectPass() : Pass("opt_pmuxselect", "decompose bounded encoded PMUX selection with shared cofactors") {}
	void help() override {
		log("    opt_pmuxselect [selection]\n\n");
		log("Recover disjoint finite equality decoders and preserve all default table entries.\n");
		log("Share bounded Shannon graphs, complement edges and small data cofactors.\n");
		log("Accept only structural reductions with lower estimated selection costs.\n");
		log("Undefined input regions may be refined according to synthesis semantics.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		extra_args(args, 1, design);
		for (auto module : design->selected_modules()) {
			bool has_candidate = false;
			for (auto cell : module->selected_cells()) if (cell->type == ID($pmux)) {
				has_candidate = true;
				break;
			}
			if (!has_candidate) continue;
			PmuxSelectWorker worker(module, design);
			struct Edit {
				Cell *cell;
				PmuxSelectWorker::Plan plan;
				std::vector<SigBit> controls;
				std::vector<std::vector<SigBit>> tables;
			};
			std::vector<Edit> edits;
			for (auto cell : module->selected_cells()) if (cell->type == ID($pmux)) {
				Edit edit;
				edit.cell = cell;
				if (worker.candidate(cell, edit.plan, edit.controls, edit.tables)) edits.push_back(std::move(edit));
				if (worker.exhausted) break;
			}
			// 所有计划在原始索引上完成，提交阶段只删除目标 PMUX。
			for (auto &edit : edits) worker.commit(edit.cell, edit.plan, edit.controls, edit.tables);
		}
	}
} OptPmuxSelectPass;

PRIVATE_NAMESPACE_END
