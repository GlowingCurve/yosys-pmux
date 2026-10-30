// opt_pmuxselect 恢复互斥选择编码，以共享选择图、互补关系和数据余因子缩减逻辑。
// 复用控制变量排列与端口分类，按结构成本选择字段分解和共享网络。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "passes/opt/pmux_celltypes.h"
#include "passes/opt/pmux_lut_cost.h"
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxSelectGraph {
	struct Node {
		int kind;
		SigBit bit;
		int a, b, s;
		bool can_z;
	};
	std::vector<Node> nodes;
	dict<SigBit, int> leaves;
	dict<std::tuple<int, int, int, int>, int> unique;
	bool overflow = false;
	int complements = 0;

	void release_build_indices() {
		dict<SigBit, int>().swap(leaves);
		dict<std::tuple<int, int, int, int>, int>().swap(unique);
	}
	int leaf(SigBit bit, bool can_z = false) {
		if (bit == State::S1) return leaf(State::S0) ^ 1;
		auto found = leaves.find(bit);
		if (found != leaves.end()) {
			log_assert(nodes[found->second/2].can_z == (can_z || bit == State::Sz));
			return found->second;
		}
		int ref = 2 * GetSize(nodes);
		nodes.push_back({0, bit, 0, 0, 0, can_z || bit == State::Sz});
		leaves[bit] = ref;
		return ref;
	}
	bool can_output_z(int ref) const {
		log_assert(ref >= 0 && ref/2 < GetSize(nodes));
		return !(ref & 1) && nodes[ref/2].can_z;
	}
	int flip(int ref) {
		log_assert(!can_output_z(ref));
		const auto &node = nodes[ref/2];
		if (node.kind == 0 && !node.bit.wire && node.bit.data > State::S1) {
			log_assert(node.bit == State::Sx);
			return leaf(State::Sx);
		}
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
		nodes.push_back({kind, SigBit(), a, b, s, kind == 1 && (can_output_z(a) || can_output_z(b))});
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
		if ((a ^ b) == 1 && !can_output_z(a) && !can_output_z(b)) {
			complements++;
			return xorgate(a, s);
		}
		int inv = (a & 1) && !can_output_z(b);
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
	struct CostContext {
		// 低位分别记录节点访问和反相访问，其他位记录当前遍历。
		std::vector<unsigned> marks;
		unsigned generation = 0;
	};
	void cost_visit(int ref, CostContext &context, std::pair<int, int> &result) const {
		log_assert(ref >= 0 && ref/2 < GetSize(nodes));
		auto &mark = context.marks[ref/2];
		if ((mark & ~3u) != context.generation) mark = context.generation;
		const auto &node = nodes[ref/2];
		if ((ref & 1) && !(mark & 2)) {
			mark |= 2;
			if (node.kind || node.bit.wire) { result.first++; result.second++; }
		}
		if (mark & 1) return;
		mark |= 1;
		if (node.kind) {
			result.first++;
			result.second += node.kind == 1 ? 3 : 4;
			cost_visit(node.a, context, result);
			cost_visit(node.b, context, result);
		}
		if (node.kind == 1) cost_visit(node.s, context, result);
	}
	std::pair<int, int> cost(const std::vector<int> &roots, CostContext &context) const {
		context.marks.resize(GetSize(nodes), 0);
		context.generation += 4;
		if (!context.generation) {
			std::fill(context.marks.begin(), context.marks.end(), 0);
			context.generation = 4;
		}
		std::pair<int, int> result = {0, 0};
		for (int ref : roots) cost_visit(ref, context, result);
		return result;
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
	struct User { Cell *cell; IdString port; int offset; };
	dict<SigBit, std::vector<User>> users;
	pool<SigBit> module_outputs;
	int work = 2000000;
	bool exhausted = false;
	bool recovered_only = false;
	bool users_indexed = false, users_valid = false;
	int cost_work = 1048576;
	int cost_diagnostic_work = 16384;
	bool cost_stopped = false, cost_live_built = false, cost_live_valid = false;
	bool cost_budget_active = false;
	size_t recovered_nodes = 0, recovered_roots = 0;
	bool cost_boundaries_frozen = false, cost_operators_built = false;
	dict<Cell *, dict<IdString, SigSpec>> cost_ports;
	dict<Cell *, dict<IdString, RTLIL::PortDir>> cost_directions;
	pool<SigBit> cost_live, cost_boundaries, cost_preserved;
	pool<SigBit> emission_inputs, removed_outputs;
	pool<Cell *> cost_legacy_cells;
	enum class CostKind { Opaque, Gate, Reduce, Compare, Logic, Pmux };
	enum class CostShape { Unsupported, Unary, Bitwise, Mux, Pmux, Compare, Reduce, Logic };
	struct CostExpression {
		CostKind kind = CostKind::Opaque;
		SigSpec inputs;
		uint16_t table = 0;
		int split = 0, operator_id = -1;
		bool invert = false;
	};
	dict<SigBit, CostExpression> cost_expressions;
	dict<Cell *, CostShape> cost_shapes;
	using CostSignature = std::tuple<CostKind, uint16_t, int, bool, SigSpec>;
	dict<CostSignature, int> cost_signatures;
	std::vector<std::vector<SigBit>> cost_operators;

	PmuxSelectWorker(Module *m, Design *d, bool recovered_only = false) : module(m), design(d), sigmap(m), types(m, d), recovered_only(recovered_only) {
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
	bool index_users() {
		if (users_indexed) return users_valid;
		users_indexed = true;
		for (auto wire : module->wires()) {
			if (!cost_spend()) return false;
			if (!wire->port_output) continue;
			for (auto bit : sigmap(wire)) {
				if (!cost_spend()) return false;
				module_outputs.insert(bit);
			}
		}
		for (auto cell : module->cells()) {
			if (!cost_spend()) return false;
			cost_ports[cell];
			cost_directions[cell];
			for (auto &port : cell->connections()) {
				if (!cost_spend()) return false;
				if (!cost_spend(GetSize(port.second))) return false;
				auto signal = sigmap(port.second);
				cost_ports[cell][port.first] = signal;
				auto direction = types.cell_port_dir(cell->type, port.first);
				cost_directions[cell][port.first] = direction;
				bool input = direction == RTLIL::PD_INPUT || direction == RTLIL::PD_INOUT;
				bool output = direction == RTLIL::PD_OUTPUT;
				if (!input && output) continue;
				for (int i = 0; i < GetSize(signal); i++) {
					if (!cost_spend()) return false;
					users[signal[i]].push_back({cell, port.first, i});
				}
			}
		}
		users_valid = true;
		return users_valid;
	}
	struct Wrapper {
		Cell *cell = nullptr;
		bool inner_b = false;
		SigSpec other;
		SigBit select;
		SigSpec y, inner_y;
	};
	bool wrapper(Cell *cell, Wrapper &result) {
		auto y = sigmap(cell->getPort(ID::Y));
		log_assert(!y.empty());
		auto found = users.find(y[0]);
		if (found == users.end() || GetSize(found->second) != 1) return false;
		auto first = found->second[0];
		auto outer = first.cell;
		if (outer->type != ID($mux) || !first.port.in(ID::A, ID::B) || first.offset != 0 || !editable(outer)) return false;
		int width = GetSize(y);
		if (!outer->hasParam(ID::WIDTH) || outer->getParam(ID::WIDTH).as_int() != width ||
			!outer->hasPort(ID::A) || !outer->hasPort(ID::B) || !outer->hasPort(ID::S) ||
			GetSize(outer->getPort(ID::A)) != width || GetSize(outer->getPort(ID::B)) != width ||
			GetSize(outer->getPort(ID::Y)) != width || GetSize(outer->getPort(ID::S)) != 1) return false;
		if (sigmap(outer->getPort(first.port)) != y) return false;
		pool<SigBit> inner_outputs;
		for (int i = 0; i < width; i++) {
			if (!spend() || module_outputs.count(y[i])) return false;
			auto entry = users.find(y[i]);
			if (entry == users.end() || GetSize(entry->second) != 1) return false;
			auto use = entry->second[0];
			if (use.cell != outer || use.port != first.port || use.offset != i) return false;
			inner_outputs.insert(y[i]);
		}
		auto output = sigmap(outer->getPort(ID::Y));
		for (auto bit : output) if (!spend() || inner_outputs.count(bit)) return false;
		auto select = sigmap(outer->getPort(ID::S))[0];
		if (!select.wire && select.data > State::S1) return false;
		result.cell = outer;
		result.inner_b = first.port == ID::B;
		result.other = sigmap(outer->getPort(result.inner_b ? ID::A : ID::B));
		result.select = select;
		result.y = output;
		if (!cost_spend(width)) return false;
		result.inner_y = y;
		return true;
	}
	SigBit operand(Cell *cell, IdString port, int offset) {
		const auto &signal = cell->getPort(port);
		auto parameter = port == ID::A ? ID::A_SIGNED : ID::B_SIGNED;
		bool sign = cell->hasParam(parameter) && cell->getParam(parameter).as_bool();
		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor)))
			sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
		return sigmap(offset < GetSize(signal) ? signal[offset] : sign && !signal.empty() ? signal.back() : SigBit(State::S0));
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
	bool decode(SigBit bit, Cube &cube, bool inequalities = false) {
		if (!bit.wire) {
			if (bit == State::S0) { cube.dead = true; return true; }
			return bit == State::S1;
		}
		if (!unique(bit) || !drivers.at(bit).cell) return false;
		auto entry = drivers.at(bit); auto cell = entry.cell;
		if (!cell->type.in(ID($eq), ID($logic_not)) && !(inequalities && cell->type == ID($ne))) return false;
		if (!cell->hasPort(ID::Y)) return false;
		if (entry.offset) { cube.dead = true; return true; }
		auto a = sigmap(cell->getPort(ID::A));
		if (GetSize(a) != cell->getParam(ID::A_WIDTH).as_int() || GetSize(a) > 256) return false;
		SigSpec b(State::S0, GetSize(a));
		if (cell->type.in(ID($eq), ID($ne))) {
			b = sigmap(cell->getPort(ID::B));
			if (GetSize(b) != cell->getParam(ID::B_WIDTH).as_int() || GetSize(b) > 256) return false;
			int width = std::max(GetSize(a), GetSize(b));
			bool sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
			a.extend_u0(width, sign); b.extend_u0(width, sign);
		}
		for (int i = 0; i < GetSize(a); i++) if (!constraint(cube, a[i], b[i])) return false;
		return true;
	}
	enum class SourceState { Active, Logic, HighZ };
	bool source_z(SigBit bit, const dict<SigBit, SourceState> &state) const {
		if (!bit.wire) return bit == State::Sz;
		auto found = state.find(bit);
		log_assert(found != state.end() && found->second != SourceState::Active);
		return found->second == SourceState::HighZ;
	}
	bool forwarded_z(Cell *cell, int offset, const dict<SigBit, SourceState> &state, bool incoming_z, bool &result) {
		result = incoming_z;
		if (cell->type == ID($lut)) {
			if (!spend()) return false;
			const auto &table = cell->parameters.at(ID::LUT);
			if (!spend(GetSize(table))) return false;
			int width = cell->getParam(ID::WIDTH).as_int();
			log_assert(width >= 0 && offset == 0);
			result = false;
			for (int i = 0; i < GetSize(table); i++) {
				if (width < 31 && (i >> width)) break;
				if (table[i] == State::Sz) { result = true; break; }
			}
			return true;
		}
		if (!incoming_z) return true;
		if (!spend()) return false;
		if (cell->type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($logic_not), ID($logic_and), ID($logic_or),
			ID($reduce_bool), ID($reduce_or), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor),
			ID($eq), ID($ne), ID($eqx), ID($nex), ID($lt), ID($le), ID($gt), ID($ge), ID($sop))) result = false;
		else if (cell->type.in(ID($pos), ID($buf))) {
			if (!spend(GetSize(cell->getPort(ID::A)) + 1)) return false;
			result = source_z(operand(cell, ID::A, offset), state);
		} else if (cell->type == ID($mux)) {
			if (!spend(GetSize(cell->getPort(ID::A)) + GetSize(cell->getPort(ID::B)) + 4)) return false;
			auto s = sigmap(cell->getPort(ID::S));
			log_assert(GetSize(s) == 1);
			result = false;
			if (s[0] != State::S1) result |= source_z(operand(cell, ID::A, offset), state);
			if (s[0] != State::S0) result |= source_z(operand(cell, ID::B, offset), state);
		} else if (cell->type == ID($pmux)) {
			if (!spend(2*GetSize(cell->getPort(ID::A)) + 2*GetSize(cell->getPort(ID::B)) + 4*GetSize(cell->getPort(ID::S)))) return false;
			auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S));
			log_assert(offset >= 0 && offset < GetSize(a) && GetSize(b) == GetSize(a)*GetSize(s));
			int selected = -1;
			for (int i = 0; i < GetSize(s); i++) if (s[i] == State::S1) {
				if (selected >= 0) { result = false; return true; }
				selected = i;
			}
			if (selected >= 0) result = source_z(b[selected*GetSize(a)+offset], state);
			else {
				result = source_z(a[offset], state);
				for (int i = 0; i < GetSize(s); i++) if (s[i] != State::S0) result |= source_z(b[i*GetSize(a)+offset], state);
			}
		}
		return true;
	}
	// 只穿过组合单元检查依赖；时序单元的输出作为独立输入边界。
	bool upstream(SigBit bit, const pool<SigBit> &outputs, dict<SigBit, SourceState> &state) {
		if (!spend() || outputs.count(bit) || unknown.count(bit)) return false;
		if (!bit.wire) return !drivers.count(bit);
		if (!unique(bit)) return false;
		if (state.count(bit)) return state.at(bit) != SourceState::Active;
		auto driver = drivers.at(bit);
		auto cell = driver.cell;
		if (!cell || StaticCellTypes::categories.is_ff(cell->type)) { state[bit] = SourceState::Logic; return true; }
		if (!types.cell_evaluable(cell->type)) return false;
		state[bit] = SourceState::Active;
		bool incoming_z = false;
		for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first)) {
			for (auto input : sigmap(port.second)) {
				if (!upstream(input, outputs, state)) return false;
				incoming_z |= source_z(input, state);
			}
		}
		bool high_z;
		if (!forwarded_z(cell, driver.offset, state, incoming_z, high_z)) return false;
		state[bit] = high_z ? SourceState::HighZ : SourceState::Logic;
		return true;
	}
	int graph_leaf(PmuxSelectGraph &graph, SigBit bit, const dict<SigBit, SourceState> &state) {
		return graph.leaf(bit, source_z(bit, state));
	}
	struct Function { std::vector<SigBit> support; std::vector<State> table; };
	void check_function(const Function &f) {
		log_assert(GetSize(f.support) <= 6);
		log_assert(GetSize(f.table) == (1 << GetSize(f.support)));
		log_assert(std::is_sorted(f.support.begin(), f.support.end()));
		log_assert(std::adjacent_find(f.support.begin(), f.support.end()) == f.support.end());
	}
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
		log_assert(GetSize(support) <= 6 && code >= 0 && code < (1 << GetSize(support)));
		int index = 0;
		for (int i = 0; i < GetSize(f.support); i++) {
			auto found = std::lower_bound(support.begin(), support.end(), f.support[i]);
			log_assert(found != support.end() && *found == f.support[i]);
			if (code & (1 << (found-support.begin()))) index |= 1 << i;
		}
		log_assert(index < GetSize(f.table));
		return f.table[index];
	}
	bool combine(IdString type, const std::vector<Function> &args, int limit, Function &result) {
		bool mux = type == ID($mux), unary = type.in(ID($not), ID($pos), ID($buf));
		log_assert(limit >= 0 && limit <= 6);
		log_assert(mux || unary || type.in(ID($and), ID($or), ID($xor), ID($xnor)));
		log_assert(GetSize(args) == (mux ? 3 : unary ? 1 : 2));
		pool<SigBit> support;
		for (auto &arg : args) {
			check_function(arg);
			for (auto input : arg.support) support.insert(input);
		}
		if (GetSize(support) > limit) return false;
		result.support.assign(support.begin(), support.end());
		std::sort(result.support.begin(), result.support.end());
		result.table.clear();
		std::array<std::array<int, 6>, 3> projections;
		std::array<Const, 3> values;
		for (int i = 0; i < GetSize(args); i++) {
			for (int j = 0; j < GetSize(args[i].support); j++) {
				auto found = std::lower_bound(result.support.begin(), result.support.end(), args[i].support[j]);
				log_assert(found != result.support.end() && *found == args[i].support[j]);
				projections[i][j] = 1 << (found-result.support.begin());
			}
			values[i].resize(1, State::S0);
		}
		for (int c = 0; c < (1 << GetSize(result.support)); c++) {
			for (int i = 0; i < GetSize(args); i++) {
				int index = 0;
				for (int j = 0; j < GetSize(args[i].support); j++)
					if (c & projections[i][j]) index |= 1 << j;
				log_assert(index < GetSize(args[i].table));
				values[i].set(0, args[i].table[index]);
			}
			Const value;
			if (mux) value = const_mux(values[0], values[1], values[2]);
			else if (type.in(ID($buf), ID($pos))) value = values[0];
			else value = CellTypes::eval(type, values[0], unary ? Const() : values[1], false, false, 1);
			log_assert(GetSize(value) == 1);
			if (value[0] > State::S1) return false;
			result.table.push_back(value[0]);
		}
		minimize(result);
		check_function(result);
		return true;
	}
	struct ControlContext {
		bool expand = false;
		dict<SigBit, Function> cache;
		pool<SigBit> active;
		int nodes = 0, edges = 0, work = 32768;
	};
	bool control_spend(ControlContext &context, int amount) {
		if (!context.expand) return true;
		if (amount > context.work) return false;
		context.work -= amount;
		return spend(amount);
	}
	bool control_combine(ControlContext &context, IdString type, const std::vector<Function> &args, Function &result) {
		pool<SigBit> support;
		for (auto &arg : args) for (auto bit : arg.support) support.insert(bit);
		if (GetSize(support) > 6 || !control_spend(context, (1 << GetSize(support))*GetSize(args))) return false;
		Function combined;
		if (!combine(type, args, 6, combined)) return false;
		result = std::move(combined);
		return true;
	}
	bool control_reduce(SigSpec signal, IdString type, ControlContext &context, Function &result, int depth) {
		result = atom(type == ID($and) ? State::S1 : State::S0);
		for (auto bit : signal) {
			Function input;
			if (!control(bit, context, input, depth) || !control_combine(context, type, {result, input}, result)) return false;
		}
		return true;
	}
	bool control_port(Cell *cell, IdString port, IdString parameter) {
		return cell->hasPort(port) && cell->hasParam(parameter) && GetSize(cell->getPort(port)) <= 256 &&
			GetSize(cell->getPort(port)) > 0 && GetSize(cell->getPort(port)) == cell->getParam(parameter).as_int();
	}
	bool control(SigBit bit, ControlContext &context, Function &result, int depth) {
		if (!bit.wire) {
			if (bit.data > State::S1) return false;
			result = atom(bit);
			return true;
		}
		if (context.cache.count(bit)) { result = context.cache.at(bit); return true; }
		if (!unique(bit)) return false;
		auto entry = drivers.at(bit); auto cell = entry.cell;
		if (context.expand && (!cell || kept.count(bit))) { result = atom(bit); context.cache[bit] = result; return true; }
		bool unary = cell && cell->type.in(ID($not), ID($pos), ID($buf));
		bool binary = cell && cell->type.in(ID($and), ID($or), ID($xor), ID($xnor));
		bool compare = cell && cell->type.in(ID($eq), ID($ne), ID($logic_not));
		bool logic = cell && cell->type.in(ID($logic_and), ID($logic_or));
		bool reduce = cell && cell->type.in(ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor));
		bool mux = cell && cell->type == ID($mux);
		if (context.expand) {
			if (!unary && !binary && !compare && !logic && !reduce && !mux) { result = atom(bit); context.cache[bit] = result; return true; }
			if (depth == 0 || !context.active.insert(bit).second || ++context.nodes > 256) return false;
			bool plain = mux || cell->type == ID($buf);
			if (!control_port(cell, ID::A, plain ? ID::WIDTH : ID::A_WIDTH) ||
				!control_port(cell, ID::Y, plain ? ID::WIDTH : ID::Y_WIDTH)) return false;
			if ((binary || logic || mux || cell->type.in(ID($eq), ID($ne))) &&
				!control_port(cell, ID::B, plain ? ID::WIDTH : ID::B_WIDTH)) return false;
			if (mux && (!cell->hasPort(ID::S) || GetSize(cell->getPort(ID::S)) != 1)) return false;
			int edges = 0;
			for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first)) {
				edges += GetSize(port.second);
				for (auto input : sigmap(port.second)) if (!input.wire && input.data > State::S1) return false;
			}
			context.edges += edges;
			if (context.edges > 2048 || !control_spend(context, 1+edges)) return false;
		}
		Cube cube;
		if (decode(bit, cube, context.expand)) {
			result = atom(cube.dead ? State::S0 : State::S1);
			if (!cube.dead) for (auto &constraint : cube.bits) {
				Function input = atom(constraint.first);
				if (context.expand && !control(constraint.first, context, input, depth-1)) return false;
				if (!constraint.second && !control_combine(context, ID($not), {input}, input)) return false;
				if (!control_combine(context, ID($and), {result, input}, result)) return false;
			}
			if (context.expand && cell && cell->type == ID($ne) && entry.offset == 0 &&
				!control_combine(context, ID($not), {result}, result)) return false;
		} else if (!context.expand) return false;
		else if (compare) result = atom(bit);
		else if ((logic || reduce) && entry.offset > 0) result = atom(State::S0);
		else if (logic || reduce) {
			IdString type = cell->type == ID($reduce_and) ? ID($and) :
				cell->type.in(ID($reduce_xor), ID($reduce_xnor)) ? ID($xor) : ID($or);
			if (!control_reduce(sigmap(cell->getPort(ID::A)), type, context, result, depth-1)) return false;
			if (logic) {
				Function other;
				if (!control_reduce(sigmap(cell->getPort(ID::B)), ID($or), context, other, depth-1) ||
					!control_combine(context, cell->type == ID($logic_and) ? ID($and) : ID($or), {result, other}, result)) return false;
			}
			if (cell->type == ID($reduce_xnor) && !control_combine(context, ID($not), {result}, result)) return false;
		} else {
			Function input;
			std::vector<Function> args;
			if (!control(operand(cell, ID::A, entry.offset), context, input, depth-1)) return false;
			args.push_back(input);
			if (binary || mux) {
				if (!control(operand(cell, ID::B, entry.offset), context, input, depth-1)) return false;
				args.push_back(input);
			}
			if (mux) {
				if (!control(sigmap(cell->getPort(ID::S))[0], context, input, depth-1)) return false;
				args.push_back(input);
			}
			if (!control_combine(context, cell->type, args, result)) return false;
		}
		context.active.erase(bit);
		context.cache[bit] = result;
		return true;
	}
	struct Selection {
		bool expanded = false;
		std::vector<SigBit> controls;
		std::vector<int> branch_for_code;
		int defaults = 0;
	};
	bool wrapper_selection(const Selection &inner, const Wrapper &wrapper, Selection &result) {
		result.expanded = inner.expanded;
		result.controls = inner.controls;
		if (wrapper.select.wire && std::find(result.controls.begin(), result.controls.end(), wrapper.select) == result.controls.end()) {
			result.controls.push_back(wrapper.select);
			std::sort(result.controls.begin(), result.controls.end());
		}
		if (GetSize(result.controls) > 6) return false;
		int size = 1 << GetSize(result.controls);
		if (GetSize(wrapper.y)*size > 16384 || !spend(size*(GetSize(inner.controls)+1))) return false;
		log_assert(GetSize(inner.branch_for_code) == (1 << GetSize(inner.controls)));
		std::vector<int> positions;
		for (auto bit : inner.controls) {
			auto found = std::lower_bound(result.controls.begin(), result.controls.end(), bit);
			log_assert(found != result.controls.end() && *found == bit);
			positions.push_back(found-result.controls.begin());
		}
		for (int c = 0; c < size; c++) {
			int code = 0;
			for (int i = 0; i < GetSize(positions); i++) if (c & (1 << positions[i])) code |= 1 << i;
			int branch = inner.branch_for_code[code];
			result.branch_for_code.push_back(branch);
			result.defaults += branch < 0;
		}
		return true;
	}
	bool selection_table(Cell *cell, bool expand, Selection &result) {
		if (!editable(cell)) return false;
		auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S)), y = sigmap(cell->getPort(ID::Y));
		int width = GetSize(y), branches = GetSize(s);
		if (width < 1 || width > 256 || branches < 3 || branches > 64 || cell->getParam(ID::WIDTH).as_int() != width ||
			cell->getParam(ID::S_WIDTH).as_int() != branches || GetSize(a) != width || GetSize(b) != width*branches) return false;
		ControlContext context;
		context.expand = expand;
		std::vector<Function> select(branches);
		pool<SigBit> support;
		for (int i = 0; i < branches; i++) {
			if (!control(s[i], context, select[i], 16)) {
				log_debug("PMUX select %s.%s: %s control recovery rejected.\n", log_id(module), log_id(cell), expand ? "boolean" : "direct");
				return false;
			}
			for (auto bit : select[i].support) support.insert(bit);
		}
		if (support.empty() || GetSize(support) > 6) return false;
		int size = 1 << GetSize(support);
		if (width*size > 16384 || !control_spend(context, size*branches)) return false;
		result.controls.assign(support.begin(), support.end());
		std::sort(result.controls.begin(), result.controls.end());
		result.expanded = expand;
		for (int c = 0; c < size; c++) {
			int branch = -1;
			for (int i = 0; i < branches; i++) if (evaluate(select[i], result.controls, c) == State::S1) {
				if (branch != -1) {
					log_debug("PMUX select %s.%s: overlapping control code %d.\n", log_id(module), log_id(cell), c);
					return false;
				}
				branch = i;
			}
			result.branch_for_code.push_back(branch);
			result.defaults += branch == -1;
		}
		log_debug("PMUX select %s.%s: recovered %s controls=%d defaults=%d.\n", log_id(module), log_id(cell),
			expand ? "boolean" : "direct", GetSize(result.controls), result.defaults);
		return true;
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
			Function combined;
			if (combine(cell->type, args, 3, combined)) { result = std::move(combined); expanded.insert(cell); }
		}
		active.erase(bit);
		cache[key] = result;
		return result;
	}
	int build(PmuxSelectGraph &graph, const std::vector<int> &table, const std::vector<SigBit> &order, const dict<SigBit, SourceState> &state, int depth = 0, int code = 0) {
		if (!spend()) { graph.overflow = true; return graph.leaf(State::Sx); }
		if (depth == GetSize(order)) return table[code];
		int a = build(graph, table, order, state, depth+1, code), b = build(graph, table, order, state, depth+1, code | (1 << depth));
		return graph.mux(graph_leaf(graph, order[depth], state), a, b);
	}
	int function_graph(PmuxSelectGraph &graph, const Function &f, const dict<SigBit, SourceState> &state) {
		std::vector<int> values;
		for (auto value : f.table) values.push_back(graph.leaf(value));
		return build(graph, values, f.support, state);
	}
	int reference_tree(const std::vector<SigBit> &table, const std::vector<int> &permuted, int depth, int code, std::map<std::vector<SigBit>, int> &memo) {
		std::vector<SigBit> values;
		for (int c = 0; c < (GetSize(permuted) >> depth); c++)
			values.push_back(table[permuted[code | (c << depth)]]);
		if (!spend(GetSize(values))) return 0;
		bool same = true;
		for (auto value : values) if (value != values[0]) same = false;
		if (same) return 0;
		if (memo.count(values)) return 0;
		memo[values] = 1;
		return 1 + reference_tree(table, permuted, depth+1, code, memo) + reference_tree(table, permuted, depth+1, code | (1 << depth), memo);
	}
	struct Plan {
		PmuxSelectGraph graph;
		std::vector<int> roots;
		int reference = 0, support_saved = 0, swaps = 0;
		std::vector<int> field_masks;
		bool fields = false;
		int count = 0, gates = 0;
		pool<SigBit> inputs;
		bool inputs_collected = false;
		Plan() = default;
		Plan(const Plan &) = delete;
		Plan &operator=(const Plan &) = delete;
		Plan(Plan &&) = default;
		Plan &operator=(Plan &&) = default;
	};
	struct Recovered {
		struct Alternative { Plan plan; int order; };
		Cell *cell = nullptr;
		SigSpec y;
		Selection selection;
		std::vector<Alternative> plans;
		int original_gates = 0;
		bool ready = false, capacity_rejected = false;
		Recovered() = default;
		Recovered(const Recovered &) = delete;
		Recovered &operator=(const Recovered &) = delete;
		Recovered(Recovered &&) = default;
		Recovered &operator=(Recovered &&) = default;
	};
	void release_recovered_plan(const Plan &plan) {
		log_assert(recovered_nodes >= plan.graph.nodes.capacity() && recovered_roots >= plan.roots.capacity());
		recovered_nodes -= plan.graph.nodes.capacity();
		recovered_roots -= plan.roots.capacity();
	}
	void release_recovered(Recovered &record, int chosen = -1, Plan *result = nullptr) {
		log_assert((chosen < 0) == (result == nullptr));
		for (int i = 0; i < GetSize(record.plans); i++) {
			if (i == chosen) *result = std::move(record.plans[i].plan);
			else release_recovered_plan(record.plans[i].plan);
		}
		std::vector<Recovered::Alternative>().swap(record.plans);
		record.ready = false;
	}
	bool save_recovered(Recovered &record, Plan &plan, int order, int orders) {
		log_assert(!record.ready && !record.capacity_rejected && !plan.fields);
		size_t nodes = plan.graph.nodes.capacity(), roots = plan.roots.capacity();
		if (nodes > 8192-recovered_nodes || roots > 16384-recovered_roots) {
			if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered storage capacity rejected nodes=%zu+%zu roots=%zu+%zu.\n",
				log_id(module), log_id(record.cell), recovered_nodes, nodes, recovered_roots, roots);
			release_recovered(record);
			record.capacity_rejected = true;
			return false;
		}
		if (!spend(1 + (record.plans.empty() ? orders : 0))) {
			release_recovered(record);
			return false;
		}
		if (record.plans.empty()) record.plans.reserve(orders);
		log_assert(GetSize(record.plans) < orders && record.plans.capacity() >= size_t(orders));
		recovered_nodes += nodes;
		recovered_roots += roots;
		record.plans.push_back({std::move(plan), order});
		if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered saved order=%d nodes=%d/%zu roots=%d/%zu.\n",
			log_id(module), log_id(record.cell), order, GetSize(record.plans.back().plan.graph.nodes), nodes, GetSize(record.plans.back().plan.roots), roots);
		return true;
	}
	bool cost_spend(int amount = 1) {
		log_assert(!cost_budget_active);
		if (cost_stopped) return false;
		cost_work -= amount;
		bool valid = spend(amount);
		if (cost_work < 0 || !valid) cost_stopped = true;
		return !cost_stopped;
	}
	bool cost_diagnostic(int amount = 1) {
		if (!ys_debug(1) || amount > cost_diagnostic_work) return false;
		cost_diagnostic_work -= amount;
		return true;
	}
	static bool cost_read(int &remaining, int64_t amount = 1) {
		if (amount > remaining) { remaining = -1; return false; }
		remaining -= amount;
		return true;
	}
	const SigSpec &cost_port(Cell *cell, IdString name) const {
		log_assert(users_valid && cost_ports.count(cell) && cost_ports.at(cell).count(name));
		return cost_ports.at(cell).at(name);
	}
	SigBit cost_operand(Cell *cell, IdString name, int offset) const {
		const auto &signal = cost_port(cell, name);
		bool sign = cell->hasParam(ID::A_SIGNED) && cell->getParam(ID::A_SIGNED).as_bool();
		if (cell->hasPort(ID::B)) sign &= cell->hasParam(ID::B_SIGNED) && cell->getParam(ID::B_SIGNED).as_bool();
		return offset < GetSize(signal) ? signal[offset] : sign && !signal.empty() ? signal.back() : SigBit(State::S0);
	}
	CostShape cost_shape(Cell *cell, int &remaining) {
		auto found = cost_shapes.find(cell);
		if (found != cost_shapes.end()) return found->second;
		if (!cost_read(remaining)) return CostShape::Unsupported;
		CostShape shape = CostShape::Unsupported;
		auto sized = [&](IdString port, IdString parameter) {
			return cell->hasPort(port) && cell->hasParam(parameter) &&
				GetSize(cost_port(cell, port)) == cell->getParam(parameter).as_int();
		};
		bool unary = cell->type.in(ID($not), ID($pos), ID($buf));
		bool binary = cell->type.in(ID($and), ID($or), ID($xor), ID($xnor));
		bool compare = cell->type.in(ID($eq), ID($ne));
		bool reduce = cell->type.in(ID($logic_not), ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor));
		bool logic = cell->type.in(ID($logic_and), ID($logic_or));
		if (cell->type.in(ID($mux), ID($pmux))) {
			if (sized(ID::Y, ID::WIDTH) && sized(ID::A, ID::WIDTH) && cell->hasPort(ID::B) && cell->hasPort(ID::S)) {
				int width = GetSize(cost_port(cell, ID::Y)), branches = GetSize(cost_port(cell, ID::S));
				if (cell->type == ID($mux) && branches == 1 && GetSize(cost_port(cell, ID::B)) == width) shape = CostShape::Mux;
				if (cell->type == ID($pmux) && cell->hasParam(ID::S_WIDTH) && cell->getParam(ID::S_WIDTH).as_int() == branches &&
					GetSize(cost_port(cell, ID::B)) == width*branches) shape = CostShape::Pmux;
			}
		} else if (cell->type == ID($buf)) {
			if (sized(ID::Y, ID::WIDTH) && sized(ID::A, ID::WIDTH)) shape = CostShape::Unary;
		} else if ((unary || binary || compare || reduce || logic) && sized(ID::Y, ID::Y_WIDTH) && sized(ID::A, ID::A_WIDTH) &&
			cell->hasParam(ID::A_SIGNED) && (!(binary || compare || logic) || (sized(ID::B, ID::B_WIDTH) && cell->hasParam(ID::B_SIGNED)))) {
			shape = unary ? CostShape::Unary : binary ? CostShape::Bitwise : compare ? CostShape::Compare : reduce ? CostShape::Reduce : CostShape::Logic;
		}
		cost_shapes[cell] = shape;
		return shape;
	}
	CostExpression cost_expression(SigBit bit, int &remaining) {
		auto found = cost_expressions.find(bit);
		if (found != cost_expressions.end()) {
			if (!cost_read(remaining, GetSize(found->second.inputs))) return {};
			return found->second;
		}
		CostExpression result;
		if (!cost_read(remaining) || !unique(bit) || !drivers.at(bit).cell) return result;
		auto source = drivers.at(bit);
		auto cell = source.cell;
		if (!cell->hasPort(ID::Y) || source.offset >= GetSize(cost_port(cell, ID::Y)) || cost_port(cell, ID::Y)[source.offset] != bit ||
			StaticCellTypes::categories.is_ff(cell->type)) return cost_expressions[bit] = result;
		CostShape shape = cost_shape(cell, remaining);
		if (shape == CostShape::Unary || shape == CostShape::Bitwise || shape == CostShape::Mux) {
			if (!cost_read(remaining, 6)) return {};
			result.kind = CostKind::Gate;
			result.inputs.append(cost_operand(cell, ID::A, source.offset));
			if (shape != CostShape::Unary) result.inputs.append(shape == CostShape::Mux ? cost_port(cell, ID::B)[source.offset] : cost_operand(cell, ID::B, source.offset));
			if (shape == CostShape::Mux) result.inputs.append(cost_port(cell, ID::S));
			result.table = shape == CostShape::Mux ? 0xca : cell->type == ID($not) ? 1 : shape == CostShape::Unary ? 2 :
				cell->type == ID($and) ? 8 : cell->type == ID($or) ? 14 : cell->type == ID($xor) ? 6 : 9;
		} else if (shape == CostShape::Pmux) {
			result.kind = CostKind::Pmux;
			const auto &s = cost_port(cell, ID::S), &b = cost_port(cell, ID::B), &y = cost_port(cell, ID::Y);
			if (!cost_read(remaining, 2LL*(1+2LL*GetSize(s)))) return {};
			result.inputs.append(cost_port(cell, ID::A)[source.offset]);
			result.inputs.append(s);
			for (int i = 0; i < GetSize(s); i++) result.inputs.append(b[i*GetSize(y)+source.offset]);
			result.split = GetSize(s);
		} else if ((shape == CostShape::Compare || shape == CostShape::Reduce || shape == CostShape::Logic) && source.offset > 0) {
			result.kind = CostKind::Gate;
		} else if (shape == CostShape::Compare) {
			result.kind = CostKind::Compare;
			int width = std::max(GetSize(cost_port(cell, ID::A)), GetSize(cost_port(cell, ID::B)));
			if (!cost_read(remaining, 6LL*width)) return {};
			auto a = cost_port(cell, ID::A), b = cost_port(cell, ID::B);
			bool sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
			a.extend_u0(width, sign);
			b.extend_u0(width, sign);
			for (int i = 0; i < width; i++) {
				result.inputs.append(a[i]);
				result.inputs.append(b[i]);
			}
			result.invert = cell->type == ID($ne);
		} else if (shape == CostShape::Reduce || shape == CostShape::Logic) {
			result.kind = shape == CostShape::Reduce ? CostKind::Reduce : CostKind::Logic;
			int64_t width = GetSize(cost_port(cell, ID::A));
			if (shape == CostShape::Logic) width += GetSize(cost_port(cell, ID::B));
			if (!cost_read(remaining, 2*width)) return {};
			result.inputs = cost_port(cell, ID::A);
			result.split = GetSize(result.inputs);
			if (shape == CostShape::Logic) result.inputs.append(cost_port(cell, ID::B));
			result.table = cell->type.in(ID($reduce_and), ID($logic_and)) ? 8 :
				cell->type.in(ID($reduce_xor), ID($reduce_xnor)) ? 6 : 14;
			result.invert = cell->type.in(ID($logic_not), ID($reduce_xnor));
		} else {
			pool<SigBit> inputs;
			int connections = 0;
			bool usable = types.cell_evaluable(cell->type) && GetSize(cost_port(cell, ID::Y)) == 1;
			for (auto &port : cost_ports.at(cell)) {
				connections += GetSize(port.second);
				if (connections > 64) { usable = false; break; }
				if (port.first == ID::Y) continue;
				if (!port.first.in(ID::A, ID::B)) usable = false;
				for (auto input : port.second) {
					if (!cost_read(remaining)) return result;
					if (input.wire) inputs.insert(input);
					else if (input != State::S0 && input != State::S1) usable = false;
				}
			}
			if (usable && GetSize(inputs) <= 4) {
				result.inputs = SigSpec(std::vector<SigBit>(inputs.begin(), inputs.end()));
				result.inputs.sort();
				dict<SigBit, int> positions;
				for (int i = 0; i < GetSize(result.inputs); i++) positions[result.inputs[i]] = i;
				for (int assignment = 0; assignment < (1 << GetSize(result.inputs)); assignment++) {
					Const a, b;
					for (auto name : {ID::A, ID::B}) if (cell->hasPort(name)) for (auto input : cost_port(cell, name)) {
						if (!cost_read(remaining)) return result;
						State value = input.wire ? ((assignment >> positions.at(input)) & 1 ? State::S1 : State::S0) : input.data;
						(name == ID::A ? a : b).append(Const(value, 1));
					}
					if (!cost_read(remaining)) return result;
					bool error = false;
					auto value = CellTypes::eval(cell, a, b, &error);
					if (error || GetSize(value) != 1 || value[0] > State::S1) { usable = false; break; }
					if (value[0] == State::S1) result.table |= 1 << assignment;
				}
				if (usable) result.kind = CostKind::Gate;
			}
		}
		cost_expressions[bit] = result;
		return result;
	}
	// 运算编号仅在当前 Worker 的固定拓扑上复用。
	int cost_operator_id(SigBit bit, int &remaining) {
		if (!cost_read(remaining)) return -1;
		auto &expression = cost_expressions.at(bit);
		if (expression.kind == CostKind::Opaque || expression.operator_id >= 0)
			return expression.operator_id;
		if (!cost_read(remaining, 4LL*GetSize(expression.inputs))) return -1;
		auto inputs = expression.inputs;
		if (expression.kind == CostKind::Gate && GetSize(inputs) == 2 &&
			(expression.table == 8 || expression.table == 14 || expression.table == 6 || expression.table == 9)) inputs.sort();
		CostSignature signature = {expression.kind, expression.table, expression.split, expression.invert, std::move(inputs)};
		auto found = cost_signatures.emplace(std::move(signature), GetSize(cost_operators));
		if (found.second) cost_operators.emplace_back();
		return expression.operator_id = found.first->second;
	}
	bool build_cost_indices(int &remaining) {
		log_assert(cost_boundaries_frozen && users_valid);
		if (!cost_live_built) {
			cost_live_built = true;
			if (!cost_read(remaining, int64_t(GetSize(module_outputs))+GetSize(kept)+GetSize(cost_preserved))) return false;
			std::vector<SigBit> pending(module_outputs.begin(), module_outputs.end());
			for (auto bit : kept) pending.push_back(bit);
			for (auto bit : cost_preserved) pending.push_back(bit);
			for (auto cell : module->cells()) {
				if (!cost_read(remaining)) return false;
				if (design->selected(module, cell) && !cell->get_bool_attribute(ID::keep) &&
					(types.cell_evaluable(cell->type) || StaticCellTypes::categories.is_ff(cell->type))) continue;
				for (auto &port : cost_ports.at(cell)) for (auto bit : port.second) {
					if (!cost_read(remaining)) return false;
					pending.push_back(bit);
				}
			}
			pool<Cell *> expanded_full;
			for (int i = 0; i < GetSize(pending); i++) {
				auto bit = pending[i];
				if (!cost_read(remaining)) return false;
				if (!bit.wire || !cost_live.insert(bit).second || cost_boundaries.count(bit) || !unique(bit) || !drivers.at(bit).cell) continue;
				auto cell = drivers.at(bit).cell;
				SigSpec inputs;
				if (cost_shape(cell, remaining) != CostShape::Unsupported) inputs = cost_expression(bit, remaining).inputs;
				else {
					if (!expanded_full.insert(cell).second) continue;
					for (auto &port : cost_ports.at(cell)) if (cost_directions.at(cell).at(port.first) != RTLIL::PD_OUTPUT) {
						if (!cost_read(remaining, GetSize(port.second))) return false;
						inputs.append(port.second);
					}
				}
				for (auto input : inputs) {
					if (!cost_read(remaining)) return false;
					pending.push_back(input);
				}
			}
			cost_live_valid = remaining >= 0;
		}
		if (!cost_live_valid) return false;
		if (!cost_operators_built) {
			cost_operators_built = true;
			for (auto cell : module->cells()) {
				if (!cost_read(remaining)) return false;
				if (cost_legacy_cells.count(cell)) continue;
				if (cost_shape(cell, remaining) == CostShape::Unsupported) continue;
				for (auto bit : cost_port(cell, ID::Y)) {
					if (!cost_read(remaining)) return false;
					if (!cost_live.count(bit) || !unique(bit) || drivers.at(bit).cell != cell) continue;
					int id = cost_operator_id(bit, remaining);
					if (remaining < 0) return false;
					if (id >= 0) cost_operators[id].push_back(bit);
				}
			}
		}
		return remaining >= 0;
	}
	bool collect_plan_inputs(Plan &plan, const std::vector<SigBit> &controls,
			const std::vector<std::vector<SigBit>> &tables) {
		log_assert(!plan.inputs_collected && plan.inputs.empty());
		if (plan.fields) {
			log_assert(GetSize(plan.field_masks) == GetSize(tables));
			if (!cost_spend(GetSize(tables)*(GetSize(controls)+1))) return false;
			for (int j = 0; j < GetSize(tables); j++) {
				std::vector<int> indices;
				for (int i = 0; i < GetSize(controls); i++) if (plan.field_masks[j] & (1 << i)) {
					if (!cost_spend(3)) return false;
					plan.inputs.insert(controls[i]);
					indices.push_back(i);
				}
				for (int c = 0; c < (1 << GetSize(indices)); c++) {
					if (!cost_spend(GetSize(indices)+3)) return false;
					int code = 0;
					for (int i = 0; i < GetSize(indices); i++) if (c & (1 << i)) code |= 1 << indices[i];
					plan.inputs.insert(tables[j][code]);
				}
			}
		} else {
			if (!cost_spend(GetSize(plan.roots)+8*GetSize(plan.graph.nodes))) return false;
			pool<int> seen, inverted;
			for (int root : plan.roots) plan.graph.reachable(root, seen, inverted);
			for (int id : seen) if (!plan.graph.nodes[id].kind) plan.inputs.insert(plan.graph.nodes[id].bit);
		}
		plan.inputs_collected = true;
		return true;
	}
	void preserve_legacy(Cell *cell, const SigSpec &y, Plan &plan, const std::vector<SigBit> &controls,
			const std::vector<std::vector<SigBit>> &tables) {
		log_assert(!cost_boundaries_frozen);
		if (!collect_plan_inputs(plan, controls, tables) || !cost_spend(GetSize(y)+GetSize(plan.inputs))) return;
		cost_legacy_cells.insert(cell);
		for (auto bit : y) cost_boundaries.insert(bit);
		for (auto bit : plan.inputs) cost_preserved.insert(bit);
	}
	bool emission_compatible(const Plan &plan, const Wrapper *wrapper, Cell *cell) {
		log_assert(plan.inputs_collected);
		if (!cost_spend(GetSize(plan.inputs)+(wrapper ? GetSize(wrapper->inner_y) : 0))) return false;
		if (wrapper) for (auto bit : wrapper->inner_y) if (cost_preserved.count(bit) || emission_inputs.count(bit)) {
			if (cost_diagnostic()) log_debug("PMUX select %s.%s: emission deletion conflicts with accepted input %s.\n", log_id(module), log_id(wrapper->cell), log_signal(bit));
			return false;
		}
		for (auto bit : plan.inputs) if (removed_outputs.count(bit)) {
			if (cost_diagnostic()) log_debug("PMUX select %s.%s: emission input references accepted deletion %s.\n", log_id(module), log_id(cell), log_signal(bit));
			return false;
		}
		return true;
	}
	bool accept_plan(const Plan &plan, const Wrapper *wrapper) {
		log_assert(plan.inputs_collected);
		if (!cost_spend(3*(GetSize(plan.inputs)+(wrapper ? GetSize(wrapper->inner_y) : 0)))) return false;
		for (auto bit : plan.inputs) emission_inputs.insert(bit);
		if (wrapper) for (auto bit : wrapper->inner_y) log_assert(removed_outputs.insert(bit).second);
		return true;
	}
	enum class CostStatus { Profitable, NoGain, UnsupportedSource, UnsupportedActivatedBoundary, DepthLimit, NodeLimit, BudgetExhausted };
	struct CostResult {
		CostStatus status = CostStatus::NoGain;
		int before = 0, after = 0;
	};
	struct CostView {
		Cell *cell;
		const SigSpec *y;
		const Wrapper *wrapper;
		const Plan *plan;
	};
	struct CostSignal { int value, care; };
	using CostKey = std::pair<SigBit, int>;
	enum class CostReadKind { Primary, Boundary, Opaque, Fixed, Expanded };
	struct CostRead {
		CostSignal signal;
		CostReadKind kind;
		bool dependent;
	};
	struct CostSnapshot {
		struct Primary { uint16_t table; std::vector<int> inputs; bool leaf; };
		std::vector<Primary> nodes;
		dict<SigBit, int> leaves;
		dict<std::pair<uint16_t, std::vector<int>>, int> functions;
		dict<CostKey, CostRead> reads;
		pool<SigBit> expanded, opaque, fixed;
		std::vector<SigBit> expanded_order;
		int64_t copy_work() const {
			return 32LL*GetSize(nodes) + 8LL*GetSize(reads) +
				4LL*(GetSize(expanded)+GetSize(opaque)+GetSize(fixed)+GetSize(expanded_order));
		}
	};
	struct CostBudget {
		PmuxSelectWorker &worker;
		int initial, remaining;
		CostBudget(PmuxSelectWorker &worker) : worker(worker), initial(std::min(worker.work, worker.cost_work)), remaining(initial) {
			log_assert(!worker.cost_budget_active);
			worker.cost_budget_active = true;
		}
		~CostBudget() {
			worker.cost_budget_active = false;
			worker.cost_spend(initial-remaining);
		}
	};
	struct CostBuilder {
		PmuxSelectWorker &worker;
		PmuxLutCost::LutCostGraph &graph;
		const std::vector<CostView> &edits;
		const dict<SigBit, std::pair<int, int>> &replacements;
		const pool<SigBit> &removed;
		bool changed;
		CostStatus status = CostStatus::NoGain;
		dict<std::pair<SigBit, int>, CostSignal> bits;
		dict<std::tuple<int, int, int>, CostSignal> refs;
		pool<SigBit> active, expanded, opaque;
		std::vector<SigBit> expanded_order;
		CostSnapshot *record = nullptr;
		const CostSnapshot *original = nullptr;
		pool<CostKey> replayed;
		CostBuilder(PmuxSelectWorker &worker, PmuxLutCost::LutCostGraph &graph, const std::vector<CostView> &edits,
			const dict<SigBit, std::pair<int, int>> &replacements, const pool<SigBit> &removed, bool changed) :
			worker(worker), graph(graph), edits(edits), replacements(replacements), removed(removed), changed(changed) {}
		CostSignal operation(uint16_t table, const std::vector<CostSignal> &args) {
			if (!graph.valid) return {0, 0};
			std::vector<int> values, care;
			for (auto arg : args) { values.push_back(arg.value); care.push_back(arg.care); }
			return {graph.gate(table, values), graph.reduce(8, care, 1)};
		}
		CostSignal fail(CostStatus reason) {
			status = reason;
			graph.valid = false;
			return {0, 0};
		}
		CostSignal reference(int edit, int ref, int depth) {
			if (!graph.valid || !graph.spend()) return {0, 0};
			if (!depth) return fail(CostStatus::DepthLimit);
			auto key = std::make_tuple(edit, ref, depth);
			auto found = refs.find(key);
			if (found != refs.end()) return found->second;
			const auto &plan = *edits[edit].plan;
			log_assert(!plan.fields && ref >= 0 && ref/2 < GetSize(plan.graph.nodes));
			const auto &node = plan.graph.nodes[ref/2];
			CostSignal result;
			if (ref & 1) result = operation(1, {reference(edit, ref ^ 1, depth-1)});
			else if (!node.kind) result = bit(node.bit, depth-1);
			else if (node.kind == 1) result = operation(0xca, {reference(edit, node.a, depth-1), reference(edit, node.b, depth-1), reference(edit, node.s, depth-1)});
			else { log_assert(node.kind == 2); result = operation(6, {reference(edit, node.a, depth-1), reference(edit, node.b, depth-1)}); }
			refs[key] = result;
			return result;
		}
		bool replay_original(const CostKey &key) {
			log_assert(original && changed && original->reads.count(key));
			if (!graph.spend()) return false;
			if (!replayed.insert(key).second) return true;
			const auto &read = original->reads.at(key);
			log_assert(!read.dependent);
			auto value = key.first;
			if (read.kind == CostReadKind::Opaque) {
				opaque.insert(value);
				if (!worker.cost_live.count(value)) { fail(CostStatus::UnsupportedActivatedBoundary); return false; }
			} else if (read.kind == CostReadKind::Fixed) graph.fixed_bits.insert(value);
			else if (read.kind == CostReadKind::Expanded) {
				if (expanded.insert(value).second) expanded_order.push_back(value);
				log_assert(worker.cost_expressions.count(value));
				const auto &expression = worker.cost_expressions.at(value);
				if (!cost_read(graph.work, GetSize(expression.inputs))) {
					fail(CostStatus::BudgetExhausted);
					return false;
				}
				for (auto input : expression.inputs) if (input.wire)
					if (!replay_original({input, key.second-1})) return false;
			}
			return graph.valid;
		}
		CostSignal bit(SigBit value, int depth = 64) {
			if (!graph.valid || !graph.spend()) return {0, 0};
			if (!depth) return fail(CostStatus::DepthLimit);
			if (!value.wire) {
				log_assert(value == State::S0 || value == State::S1 || value == State::Sx || value == State::Sz);
				// SatGen 在当前证明入口将 Sz 导入为已定义零。
				return {value == State::S1 ? 1 : 0, value != State::Sx ? 1 : 0};
			}
			log_assert(!changed || !removed.count(value));
			auto key = std::make_pair(value, depth);
			auto found = bits.find(key);
			if (found != bits.end()) return found->second;
			if (original) {
				auto cached = original->reads.find(key);
				if (cached != original->reads.end() && !cached->second.dependent) {
					if (!replay_original(key)) return {0, 0};
					return bits[key] = cached->second.signal;
				}
			}
			log_assert(active.insert(value).second);
			CostSignal result;
			CostReadKind kind = CostReadKind::Primary;
			bool dependent = replacements.count(value) && !worker.cost_boundaries.count(value);
			if (changed && replacements.count(value)) {
				auto replacement = replacements.at(value);
				result = reference(replacement.first, replacement.second, depth-1);
			} else if (worker.cost_boundaries.count(value)) { kind = CostReadKind::Boundary; result = {graph.leaf(value), 1}; }
			else if (!worker.unique(value)) result = fail(CostStatus::UnsupportedSource);
			else {
				auto cell = worker.drivers.at(value).cell;
				if (!cell || StaticCellTypes::categories.is_ff(cell->type)) result = {graph.leaf(value), 1};
				else {
					auto expression = worker.cost_expression(value, graph.work);
					if (graph.work < 0) result = fail(CostStatus::BudgetExhausted);
					else if (expression.kind == CostKind::Opaque) {
						kind = CostReadKind::Opaque;
						opaque.insert(value);
						if (changed && !worker.cost_live.count(value)) result = fail(CostStatus::UnsupportedActivatedBoundary);
						else result = {graph.leaf(value), 1};
					} else if (worker.kept.count(value) || !worker.design->selected(worker.module, cell) || cell->get_bool_attribute(ID::keep)) {
						kind = CostReadKind::Fixed;
						graph.fixed_bits.insert(value);
						result = {graph.leaf(value), 1};
					} else {
						kind = CostReadKind::Expanded;
						if (expanded.insert(value).second) expanded_order.push_back(value);
						std::vector<CostSignal> args;
						for (auto input : expression.inputs) {
							args.push_back(bit(input, depth-1));
							if (!graph.valid) { active.erase(value); return {0, 0}; }
							if (record && input.wire) dependent |= record->reads.at({input, depth-1}).dependent;
						}
						std::vector<int> values, care;
						for (auto arg : args) { values.push_back(arg.value); care.push_back(arg.care); }
						if (expression.kind == CostKind::Gate) result = operation(expression.table, args);
						else if (expression.kind == CostKind::Compare) {
							std::vector<int> terms;
							for (int i = 0; i < GetSize(values); i += 2) terms.push_back(graph.gate(9, {values[i], values[i+1]}));
							result = {graph.reduce(8, terms, 1), graph.reduce(8, care, 1)};
						} else if (expression.kind == CostKind::Reduce) result = {graph.reduce(expression.table, values, expression.table == 8), graph.reduce(8, care, 1)};
						else if (expression.kind == CostKind::Logic) {
							std::vector<int> a(values.begin(), values.begin()+expression.split), b(values.begin()+expression.split, values.end());
							result = {graph.gate(expression.table, {graph.reduce(14, a, 0), graph.reduce(14, b, 0)}), graph.reduce(8, care, 1)};
						} else {
							log_assert(expression.kind == CostKind::Pmux && GetSize(args) == 1+2*expression.split);
							int enabled = 0, collision = 0;
							std::vector<int> terms, qualification;
							for (int i = 0; i < expression.split; i++) {
								auto control = args[1+i], data = args[1+expression.split+i];
								terms.push_back(graph.gate(8, {data.value, control.value}));
								qualification.push_back(control.care);
								qualification.push_back(graph.gate(14, {graph.gate(1, {control.value}), data.care}));
								collision = graph.gate(14, {collision, graph.gate(8, {enabled, control.value})});
								enabled = graph.gate(14, {enabled, control.value});
							}
							int selected = graph.reduce(14, terms, 0);
							qualification.push_back(graph.gate(1, {collision}));
							qualification.push_back(graph.gate(14, {enabled, args[0].care}));
							result = {args[0].value == 0 ? selected : graph.gate(0xca, {args[0].value, selected, enabled}), graph.reduce(8, qualification, 1)};
						}
						if (expression.invert) result = operation(1, {result});
					}
				}
			}
			active.erase(value);
			bits[key] = result;
			if (record && graph.valid) {
				if (!cost_read(graph.work, 8)) return fail(CostStatus::BudgetExhausted);
				record->reads[key] = {result, kind, dependent};
			}
			return result;
		}
	};
	CostStatus make_cost_snapshot(const CostView &edit, CostSnapshot &snapshot) {
		log_assert(cost_boundaries_frozen && !edit.wrapper && snapshot.nodes.empty());
		if (cost_stopped || work <= 0 || cost_work <= 0) {
			cost_stopped = true;
			return CostStatus::BudgetExhausted;
		}
		CostBudget budget(*this);
		if (!build_cost_indices(budget.remaining)) return CostStatus::BudgetExhausted;
		std::vector<CostView> edits = {edit};
		dict<SigBit, std::pair<int, int>> replacements;
		pool<SigBit> removed;
		if (!cost_read(budget.remaining, GetSize(*edit.y)+GetSize(cost_preserved))) return CostStatus::BudgetExhausted;
		for (int i = 0; i < GetSize(*edit.y); i++) replacements[(*edit.y)[i]] = {0, edit.plan->roots[i]};
		PmuxLutCost::LutCostGraph graph(budget.remaining);
		CostBuilder before(*this, graph, edits, replacements, removed, false);
		before.record = &snapshot;
		for (auto bit : *edit.y) { before.bit(bit); if (!graph.valid) break; }
		for (auto bit : cost_preserved) { if (!graph.valid) break; if (bit.wire) before.bit(bit); }
		if (!graph.valid) return budget.remaining < 0 ? CostStatus::BudgetExhausted :
			before.status == CostStatus::NoGain ? CostStatus::NodeLimit : before.status;
		log_assert(before.active.empty() && graph.certificates.empty() && graph.checked_certificates.empty() && graph.required.empty());
		int64_t copy_work = 32LL*GetSize(graph.nodes) + 8LL*GetSize(snapshot.reads) +
			4LL*(GetSize(before.expanded)+GetSize(before.opaque)+GetSize(graph.fixed_bits)+GetSize(before.expanded_order));
		if (!cost_read(budget.remaining, copy_work)) return CostStatus::BudgetExhausted;
		log_assert(snapshot.leaves.empty() && snapshot.functions.empty() && snapshot.fixed.empty());
		log_assert(snapshot.expanded.empty() && snapshot.opaque.empty() && snapshot.expanded_order.empty());
		snapshot.nodes.reserve(GetSize(graph.nodes));
		for (auto &node : graph.nodes) {
			log_assert(node.cost == -1 && node.cuts.empty() && node.best.empty());
			snapshot.nodes.push_back({node.table, std::move(node.inputs), node.leaf});
		}
		snapshot.leaves = std::move(graph.leaves);
		snapshot.functions = std::move(graph.functions);
		snapshot.fixed = std::move(graph.fixed_bits);
		snapshot.expanded = std::move(before.expanded);
		snapshot.opaque = std::move(before.opaque);
		snapshot.expanded_order = std::move(before.expanded_order);
		log_assert(copy_work == snapshot.copy_work());
		if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered snapshot nodes=%d reads=%d copy=%lld work=%d.\n",
			log_id(module), log_id(edit.cell), GetSize(snapshot.nodes), GetSize(snapshot.reads), (long long)copy_work, budget.initial-budget.remaining);
		return CostStatus::NoGain;
	}
	bool restore_cost_snapshot(const CostSnapshot &snapshot, PmuxLutCost::LutCostGraph &graph, CostBuilder &before) {
		log_assert(graph.valid && GetSize(graph.nodes) == 2 && before.bits.empty() && !before.changed && GetSize(snapshot.nodes) <= 4096);
		if (!cost_read(graph.work, snapshot.copy_work())) return false;
		graph.nodes.clear();
		graph.nodes.reserve(GetSize(snapshot.nodes));
		for (const auto &node : snapshot.nodes) graph.nodes.emplace_back(node.table, node.inputs, node.leaf);
		graph.leaves = snapshot.leaves;
		graph.functions = snapshot.functions;
		graph.fixed_bits = snapshot.fixed;
		for (const auto &read : snapshot.reads) before.bits[read.first] = read.second.signal;
		before.expanded = snapshot.expanded;
		before.opaque = snapshot.opaque;
		before.expanded_order = snapshot.expanded_order;
		return true;
	}
	bool cost_observed(SigBit bit, const pool<SigBit> &modeled, const pool<Cell *> &rewritten,
			dict<Cell *, std::vector<SigBit>> &generic, int &remaining) {
		if (!cost_live.count(bit)) return false;
		if (module_outputs.count(bit) || kept.count(bit) || cost_preserved.count(bit)) return true;
		auto found = users.find(bit);
		if (found == users.end()) return false;
		for (auto use : found->second) {
			if (!cost_read(remaining)) return false;
			auto cell = use.cell;
			if (rewritten.count(cell) || cost_legacy_cells.count(cell)) continue;
			auto direction = cost_directions.at(cell).at(use.port);
			if (direction == RTLIL::PD_UNKNOWN || direction == RTLIL::PD_INOUT || !design->selected(module, cell) || cell->get_bool_attribute(ID::keep)) return true;
			CostShape shape = cost_shape(cell, remaining);
			if ((shape == CostShape::Unary || shape == CostShape::Bitwise || shape == CostShape::Mux || shape == CostShape::Pmux) && use.port != ID::S) {
				log_assert(use.port.in(ID::A, ID::B));
				const auto &y = cost_port(cell, ID::Y), &input = cost_port(cell, use.port);
				int offset = shape == CostShape::Pmux && use.port == ID::B ? use.offset % GetSize(y) : use.offset;
				auto observed = [&](int index) { return cost_live.count(y[index]) && !modeled.count(y[index]); };
				if (!cost_read(remaining)) return false;
				if (offset < GetSize(y) && observed(offset)) return true;
				if (shape == CostShape::Unary || shape == CostShape::Bitwise) {
					bool sign = cell->hasParam(ID::A_SIGNED) && cell->getParam(ID::A_SIGNED).as_bool();
					if (cell->hasPort(ID::B)) sign &= cell->hasParam(ID::B_SIGNED) && cell->getParam(ID::B_SIGNED).as_bool();
					if (sign && use.offset == GetSize(input)-1) for (int index = GetSize(input); index < GetSize(y); index++) {
						if (!cost_read(remaining)) return false;
						if (observed(index)) return true;
					}
				}
			} else if (shape == CostShape::Compare || shape == CostShape::Reduce || shape == CostShape::Logic) {
				const auto &y = cost_port(cell, ID::Y);
				if (!cost_read(remaining)) return false;
				if (!y.empty() && cost_live.count(y[0]) && !modeled.count(y[0])) return true;
			} else {
				if (!types.cell_evaluable(cell->type) && !StaticCellTypes::categories.is_ff(cell->type)) return true;
				auto cached = generic.find(cell);
				if (cached == generic.end()) {
					std::vector<SigBit> outputs;
					for (auto &port : cost_ports.at(cell)) if (cost_directions.at(cell).at(port.first) != RTLIL::PD_INPUT) for (auto output : port.second) {
						if (!cost_read(remaining)) return false;
						if (cost_live.count(output)) outputs.push_back(output);
					}
					generic[cell] = std::move(outputs);
					cached = generic.find(cell);
				}
				while (!cached->second.empty()) {
					if (!cost_read(remaining)) return false;
					if (!modeled.count(cached->second.back())) return true;
					cached->second.pop_back();
				}
			}
		}
		return false;
	}
	static const char *cost_status_name(CostStatus status) {
		switch (status) {
		case CostStatus::Profitable: return "profitable";
		case CostStatus::NoGain: return "no-gain";
		case CostStatus::UnsupportedSource: return "unsupported-source";
		case CostStatus::UnsupportedActivatedBoundary: return "unsupported-activated-boundary";
		case CostStatus::DepthLimit: return "depth-limit";
		case CostStatus::NodeLimit: return "node-limit";
		case CostStatus::BudgetExhausted: return "budget-exhausted";
		}
		log_abort();
	}
	CostResult estimate_select(const std::vector<CostView> &edits, const CostSnapshot *snapshot = nullptr) {
		log_assert(cost_boundaries_frozen && !edits.empty());
		if (cost_stopped || work <= 0 || cost_work <= 0) {
			cost_stopped = true;
			return {CostStatus::BudgetExhausted, 0, 0};
		}
		CostBudget budget(*this);
		CostResult result;
		auto finish = [&](CostStatus status) {
			result.status = status;
			if (cost_diagnostic()) log_debug("PMUX select %s cost in %s: %s %d -> %d, %d targets, work used %d, remaining %d.\n",
				edits[0].wrapper ? "wrapper" : "recovered", log_id(module), cost_status_name(status), result.before, result.after, GetSize(edits), budget.initial-budget.remaining, cost_work-(budget.initial-budget.remaining));
			return result;
		};
		if (!build_cost_indices(budget.remaining)) return finish(CostStatus::BudgetExhausted);
		dict<SigBit, std::pair<int, int>> replacements;
		pool<Cell *> rewritten;
		pool<SigBit> roots, removed;
		for (int i = 0; i < GetSize(edits); i++) {
			const auto &edit = edits[i];
			log_assert(edit.y && edit.plan && !edit.plan->fields && GetSize(*edit.y) == GetSize(edit.plan->roots));
			log_assert(rewritten.insert(edit.cell).second);
			if (edit.wrapper) {
				log_assert(edit.wrapper->cell && rewritten.insert(edit.wrapper->cell).second);
				if (!cost_read(budget.remaining, GetSize(edit.wrapper->inner_y))) return finish(CostStatus::BudgetExhausted);
				for (auto bit : edit.wrapper->inner_y) log_assert(removed.insert(bit).second);
			}
			for (int j = 0; j < GetSize(*edit.y); j++) {
				if (!cost_read(budget.remaining)) return finish(CostStatus::BudgetExhausted);
				auto bit = (*edit.y)[j];
				log_assert(!cost_boundaries.count(bit) && !replacements.count(bit));
				replacements[bit] = {i, edit.plan->roots[j]};
				roots.insert(bit);
			}
		}
		if (!cost_read(budget.remaining, GetSize(cost_preserved))) return finish(CostStatus::BudgetExhausted);
		for (auto bit : cost_preserved) if (bit.wire) roots.insert(bit);
		PmuxLutCost::LutCostGraph graph(budget.remaining);
		CostBuilder before(*this, graph, edits, replacements, removed, false), after(*this, graph, edits, replacements, removed, true);
		if (snapshot) {
			log_assert(GetSize(edits) == 1 && !edits[0].wrapper);
			if (!restore_cost_snapshot(*snapshot, graph, before)) return finish(CostStatus::BudgetExhausted);
			after.original = snapshot;
		}
		auto add_root = [&](SigBit bit) { before.bit(bit); after.bit(bit); };
		for (auto bit : roots) {
			if (!graph.valid) break;
			add_root(bit);
		}
		pool<SigBit> modeled, checked;
		pool<int> signatures;
		dict<Cell *, std::vector<SigBit>> generic;
		std::vector<SigBit> pending;
		int before_count = 0, after_count = 0;
		auto collect = [&]() {
			while (before_count < GetSize(before.expanded_order)) {
				if (!graph.spend()) return;
				auto bit = before.expanded_order[before_count++];
				if (modeled.insert(bit).second) pending.push_back(bit);
			}
			while (after_count < GetSize(after.expanded_order)) {
				if (!graph.spend()) return;
				auto bit = after.expanded_order[after_count++];
				if (modeled.insert(bit).second) pending.push_back(bit);
			}
		};
		collect();
		for (int i = 0; graph.valid && i < GetSize(pending); i++) {
			auto bit = pending[i];
			if (!graph.spend()) break;
			if (cost_observed(bit, modeled, rewritten, generic, budget.remaining) && roots.insert(bit).second) {
				add_root(bit);
				collect();
			}
			int id = cost_operator_id(bit, budget.remaining);
			if (budget.remaining < 0) break;
			if (id < 0 || !signatures.insert(id).second) continue;
			for (auto outside : cost_operators[id]) {
				if (!graph.spend()) break;
				if (modeled.count(outside) || !cost_live.count(outside) || !checked.insert(outside).second) continue;
				if (cost_observed(outside, modeled, rewritten, generic, budget.remaining) && roots.insert(outside).second) {
					add_root(outside);
					collect();
				}
			}
		}
		if (budget.remaining < 0) return finish(CostStatus::BudgetExhausted);
		if (!graph.valid) {
			if (before.status != CostStatus::NoGain) return finish(before.status);
			if (after.status != CostStatus::NoGain) return finish(after.status);
			return finish(CostStatus::NodeLimit);
		}
		std::vector<int> old_roots, new_roots;
		for (auto bit : roots) {
			if (!graph.valid) break;
			auto old_signal = before.bit(bit), new_signal = after.bit(bit);
			graph.prepare_certificate(old_signal.value, old_signal.care);
			graph.prepare_certificate(new_signal.value, new_signal.care);
			old_roots.push_back(old_signal.value);
			new_roots.push_back(new_signal.value);
		}
		if (!graph.valid) return finish(budget.remaining < 0 ? CostStatus::BudgetExhausted : CostStatus::NodeLimit);
		auto old_cover = graph.cover(old_roots);
		dict<int, PmuxLutCost::Cut> old_cuts;
		if (ys_debug(1) && !snapshot) for (int id : old_cover) {
			if (!cost_diagnostic(1+GetSize(graph.nodes[id].best))) break;
			old_cuts[id] = graph.nodes[id].best;
		}
		auto new_cover = graph.cover(new_roots);
		if (budget.remaining < 0) return finish(CostStatus::BudgetExhausted);
		if (!graph.valid) return finish(CostStatus::NodeLimit);
		result.before = GetSize(old_cover)+GetSize(graph.fixed_bits);
		result.after = GetSize(new_cover)+GetSize(graph.fixed_bits);
		if (ys_debug(1)) {
			for (auto &edit : edits) {
				if (!cost_diagnostic()) break;
				if (edit.wrapper) log_debug("Select cost target %s outer %s.\n", log_id(edit.cell), log_id(edit.wrapper->cell));
				else log_debug("Select cost target %s recovered.\n", log_id(edit.cell));
			}
			for (auto bit : roots) {
				if (!cost_diagnostic()) break;
				log_debug("Select cost root %s before %d care %d after %d care %d.\n", log_signal(bit), before.bits.at({bit, 64}).value, before.bits.at({bit, 64}).care, after.bits.at({bit, 64}).value, after.bits.at({bit, 64}).care);
			}
			for (auto bit : before.expanded) {
				if (!cost_diagnostic()) break;
				log_debug("Select cost source %s retained %d.\n", log_signal(bit), after.expanded.count(bit));
			}
			for (auto bit : graph.fixed_bits) {
				if (!cost_diagnostic()) break;
				log_debug("Select cost fixed %s.\n", log_signal(bit));
			}
			if (!snapshot) for (auto &entry : graph.leaves) {
				if (!cost_diagnostic()) break;
				log_debug("Select cost leaf %s node %d.\n", log_signal(entry.first), entry.second);
			}
			if (!snapshot) for (int id = 0; id < GetSize(graph.nodes); id++) {
				const auto &node = graph.nodes[id];
				if (!cost_diagnostic(1+GetSize(node.inputs)+(old_cuts.count(id) ? GetSize(old_cuts.at(id)) : 0)+(new_cover.count(id) ? GetSize(node.best) : 0))) break;
				log_debug("Select cost node %d table %u leaf %d before %d after %d inputs", id, unsigned(node.table), node.leaf, old_cover.count(id), new_cover.count(id));
				for (int input : node.inputs) log_debug(" %d", input);
				log_debug(" cuts");
				if (old_cuts.count(id)) for (int input : old_cuts.at(id)) log_debug(" %d", input);
				log_debug(" / ");
				if (new_cover.count(id)) for (int input : node.best) log_debug(" %d", input);
				log_debug("\n");
			}
			if (cost_diagnostic()) log_debug("Select cost certificates 5/6/7=%d/%d/%d partial=%d nodes=%d.\n", graph.certificate_widths[5], graph.certificate_widths[6], graph.certificate_widths[7], graph.partial_functions, GetSize(graph.nodes));
		}
		return finish(result.before > result.after ? CostStatus::Profitable : CostStatus::NoGain);
	}
	// recovered 保留原输出，确认直接 MUX 使用环境的形状和输入依赖。
	bool recovered_context(Cell *cell) {
		log_assert(users_valid);
		pool<Cell *> checked;
		for (auto bit : cost_port(cell, ID::Y)) {
			if (!cost_spend()) return false;
			auto found = users.find(bit);
			if (found == users.end()) continue;
			for (auto use : found->second) {
				if (!cost_spend()) return false;
				auto outer = use.cell;
				if (outer->type != ID($mux) || !checked.insert(outer).second) continue;
				{
					CostBudget budget(*this);
					if (!cost_read(budget.remaining, 4) || GetSize(outer->connections()) != 4 ||
						cost_shape(outer, budget.remaining) != CostShape::Mux) return false;
				}
				if (work <= 0 || cost_work <= 0) return false;
				const auto &output = cost_port(outer, ID::Y);
				int width = GetSize(output);
				if (width < 1 || !cost_spend(width)) return false;
				pool<SigBit> outputs;
				for (int i = 0; i < width; i++) {
					auto bit = output[i];
					if (!unique(bit)) return false;
					const auto &driver = drivers.at(bit);
					if (driver.cell != outer || driver.offset != i || !outputs.insert(bit).second) return false;
				}
				dict<SigBit, SourceState> dependency;
				for (auto port : {ID::A, ID::B, ID::S}) for (auto input : cost_port(outer, port))
					if (!upstream(input, outputs, dependency)) return false;
			}
		}
		return work > 0 && cost_work > 0;
	}
	int choose_recovered(Recovered &record) {
		log_assert(record.ready && !record.plans.empty());
		if (!recovered_context(record.cell)) return -1;
		CostSnapshot snapshot;
		CostView view = {record.cell, &record.y, nullptr, &record.plans[0].plan};
		auto status = make_cost_snapshot(view, snapshot);
		if (status != CostStatus::NoGain) {
			if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered snapshot %s.\n", log_id(module), log_id(record.cell), cost_status_name(status));
			return -1;
		}
		int chosen = -1;
		std::tuple<int, int, int, int, int> best;
		for (int index = 0; index < GetSize(record.plans); index++) {
			if (cost_stopped || work <= 0 || cost_work <= 0) { cost_stopped = true; return -1; }
			auto &alternative = record.plans[index];
			auto &plan = alternative.plan;
			if (!collect_plan_inputs(plan, {}, {})) return -1;
			if (!emission_compatible(plan, nullptr, record.cell)) {
				if (cost_stopped) return -1;
				if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered order=%d emission-incompatible.\n",
					log_id(module), log_id(record.cell), alternative.order);
				continue;
			}
			view.plan = &plan;
			auto result = estimate_select({view}, &snapshot);
			if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered order=%d count=%d reference=%d gates=%d original_gates=%d %s %d -> %d.\n",
				log_id(module), log_id(record.cell), alternative.order, plan.count, plan.reference, plan.gates, record.original_gates,
				cost_status_name(result.status), result.before, result.after);
			if (cost_stopped) return -1;
			if (result.status != CostStatus::Profitable) continue;
			auto rank = std::make_tuple(result.after-result.before, result.after, plan.count, plan.gates, alternative.order);
			if (chosen < 0 || rank < best) { chosen = index; best = rank; }
		}
		if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered chosen=%d orders=%d storage=%zu/%zu.\n",
			log_id(module), log_id(record.cell), chosen < 0 ? -1 : record.plans[chosen].order, GetSize(record.plans), recovered_nodes, recovered_roots);
		return chosen;
	}
	bool candidate(Cell *cell, const Selection &selection, Plan &best, std::vector<std::vector<SigBit>> &tables,
			const Wrapper *wrapper = nullptr, Recovered *recovered = nullptr) {
		log_assert(!wrapper || !recovered);
		if (wrapper && cost_stopped) return false;
		auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S)), y = sigmap(cell->getPort(ID::Y));
		int width = GetSize(y), branches = GetSize(s);
		auto &controls = selection.controls;
		log_assert(!controls.empty() && GetSize(controls) <= 6);
		int size = 1 << GetSize(controls);
		log_assert(GetSize(selection.branch_for_code) == size);
		for (int branch : selection.branch_for_code) log_assert(branch >= -1 && branch < branches);
		pool<SigBit> outputs;
		for (auto bit : y) outputs.insert(bit);
		if (wrapper) for (auto bit : wrapper->y) outputs.insert(bit);
		dict<SigBit, int> positions;
		for (int i = 0; i < GetSize(controls); i++) positions[controls[i]] = i;
		dict<SigBit, SourceState> dependency;
		for (auto bit : a) if (!upstream(bit, outputs, dependency)) return false;
		for (auto bit : b) if (!upstream(bit, outputs, dependency)) return false;
		for (auto bit : controls) if (!upstream(bit, outputs, dependency)) return false;
		if (selection.expanded || wrapper) for (auto bit : s) if (!upstream(bit, outputs, dependency)) return false;
		if (wrapper) {
			if (!upstream(wrapper->select, outputs, dependency)) return false;
			for (auto bit : wrapper->other) if (!upstream(bit, outputs, dependency)) return false;
			if (!spend(width*size)) return false;
		}
		tables.assign(width, {});
		for (int c = 0; c < size; c++) {
			int branch = selection.branch_for_code[c];
			bool use_inner = true;
			if (wrapper) {
				bool selected = wrapper->select.wire ? (c & (1 << positions.at(wrapper->select))) != 0 : wrapper->select == State::S1;
				use_inner = selected == wrapper->inner_b;
			}
			for (int j = 0; j < width; j++) tables[j].push_back(!use_inner ? wrapper->other[j] : branch < 0 ? a[j] : b[branch*width+j]);
		}
		std::vector<std::vector<Function>> functions(width);
		// 每个编码最多保存八个数据赋值，每个 State 使用三个比特。
		struct Cofactors { std::vector<SigBit> atoms; std::vector<uint32_t> values; };
		std::vector<Cofactors> cofactors(width);
		std::vector<int> masks;
		int field_choices = 0, support_saved = 0;
		{
			dict<std::pair<SigBit, int>, Function> cache; pool<SigBit> active; pool<Cell *> expanded;
			for (int j = 0; j < width; j++) {
				int mask = 0;
				for (int i = 0; i < GetSize(controls); i++)
					for (int c = 0; c < size; c++) if (!(c & (1 << i)) && tables[j][c] != tables[j][c | (1 << i)]) { mask |= 1 << i; break; }
				masks.push_back(mask);
				int support_size = __builtin_popcount(unsigned(mask));
				field_choices += 1 << support_size;
				support_saved += GetSize(controls) - support_size;
				for (int c = 0; c < size; c++) functions[j].push_back(expression(tables[j][c], c, positions, cache, active, expanded, 8));
				pool<SigBit> data;
				for (auto &function : functions[j]) for (auto bit : function.support) data.insert(bit);
				if (!data.empty() && GetSize(data) <= 3) {
					auto &cofactor = cofactors[j];
					cofactor.atoms.assign(data.begin(), data.end());
					std::sort(cofactor.atoms.begin(), cofactor.atoms.end());
					cofactor.values.resize(size, 0);
					for (int c = 0; c < size; c++) for (int d = 0; d < (1 << GetSize(cofactor.atoms)); d++) {
						auto value = evaluate(functions[j][c], cofactor.atoms, d);
						log_assert(unsigned(value) < 8);
						cofactor.values[c] |= uint32_t(value) << (3*d);
					}
				}
			}
		}
		// 按原始 PMUX 的数据选择数量计算字段支持缩减。
		bool field_gain = !wrapper && support_saved > 0 && 4*field_choices <= 3*width*branches;
		// 原始数据叶节点全局互异时，完整选择图与参考树具有相同节点数量。
		auto legacy_no_gain = [&]() {
			if (wrapper || recovered || size < 4) return false;
			pool<SigBit> seen;
			for (int j = 0; j < width; j++) {
				if (!cofactors[j].atoms.empty()) return false;
				for (int c = 0; c < size; c++) {
					auto bit = tables[j][c];
					if (!bit.wire || !seen.insert(bit).second) return false;
					const auto &function = functions[j][c];
					if (GetSize(function.support) > 1) continue;
					if (GetSize(function.support) != 1 || function.support[0] != bit || GetSize(function.table) != 2 ||
						function.table[0] != State::S0 || function.table[1] != State::S1) return false;
				}
			}
			return true;
		};
		if (legacy_no_gain()) {
			log_debug("PMUX select %s.%s: complete distinct data table has no legacy gain.\n", log_id(module), log_id(cell));
			return false;
		}
		int original_gates;
		{
			PmuxSelectGateCost old_cost;
			std::vector<int> original_select;
			for (auto bit : s) original_select.push_back(old_cost.leaf(bit));
			auto original_roots = old_cost.pmux(a, b, original_select);
			if (wrapper) {
				int select = old_cost.leaf(wrapper->select);
				for (int j = 0; j < width; j++) {
					int other = old_cost.leaf(wrapper->other[j]);
					original_roots[j] = wrapper->inner_b ? old_cost.gate(4, other, original_roots[j], select) : old_cost.gate(4, original_roots[j], other, select);
				}
				if (!spend(GetSize(old_cost.nodes)+width)) return false;
			}
			original_gates = old_cost.cost(original_roots);
		}
		std::vector<std::vector<int>> orders;
		for (int reverse = 0; reverse < 2; reverse++) for (int shift = 0; shift < GetSize(controls); shift++) {
			std::vector<int> order;
			for (int i = 0; i < GetSize(controls); i++) order.push_back(reverse ? (shift-i+GetSize(controls))%GetSize(controls) : (shift+i)%GetSize(controls));
			if (std::find(orders.begin(), orders.end(), order) == orders.end()) orders.push_back(order);
		}
		bool accepted = false;
		bool saving = recovered != nullptr;
		PmuxSelectGraph::CostContext cost_context;
		for (int order_index = 0; order_index < GetSize(orders); order_index++) {
			auto &order = orders[order_index];
			if (wrapper && cost_stopped) break;
			Plan plan;
			plan.support_saved = support_saved;
			std::vector<SigBit> selectors;
			for (int i : order) selectors.push_back(controls[i]);
			std::vector<int> permuted(size);
			for (int c = 0; c < size; c++)
				for (int i = 0; i < GetSize(order); i++)
					if (c & (1 << i)) permuted[c] |= 1 << order[i];
			for (int j = 0; j < width; j++) {
				std::map<std::vector<SigBit>, int> memo;
				plan.reference += reference_tree(tables[j], permuted, 0, 0, memo);
				std::vector<int> leaves(size);
				for (int c = 0; c < size; c++) {
					int index = permuted[c];
					auto &function = functions[j][index];
					leaves[c] = GetSize(function.support) <= 1 ? function_graph(plan.graph, function, dependency) : graph_leaf(plan.graph, tables[j][index], dependency);
				}
				int normal = build(plan.graph, leaves, selectors, dependency), result = normal;
				const auto &cofactor = cofactors[j];
				if (!cofactor.atoms.empty()) {
					std::vector<int> cofactor_roots;
					for (int d = 0; d < (1 << GetSize(cofactor.atoms)); d++) {
						std::vector<int> values(size);
						for (int c = 0; c < size; c++) {
							int index = permuted[c];
							values[c] = plan.graph.leaf(State((cofactor.values[index] >> (3*d)) & 7));
						}
						cofactor_roots.push_back(build(plan.graph, values, selectors, dependency));
					}
					int swapped = build(plan.graph, cofactor_roots, cofactor.atoms, dependency);
					if (plan.graph.cost({swapped}, cost_context).first < plan.graph.cost({normal}, cost_context).first) {
						result = swapped;
						plan.swaps++;
					}
				}
				plan.roots.push_back(result);
			}
			if (exhausted || plan.graph.overflow) {
				if (recovered) release_recovered(*recovered);
				return false;
			}
			plan.graph.release_build_indices();
			auto cost = plan.graph.cost(plan.roots, cost_context);
			plan.count = cost.first;
			plan.gates = cost.second;
			int separate = 0;
			for (int root : plan.roots) separate += plan.graph.cost({root}, cost_context).first;
			bool structural = plan.support_saved || plan.swaps || separate > plan.count || plan.graph.complements;
			bool graph_gain = structural && 4*plan.count <= 3*plan.reference && plan.count+2 <= plan.reference;
			if (recovered_only || (!graph_gain && !field_gain) || plan.gates >= original_gates) {
				if (saving && !save_recovered(*recovered, plan, order_index, GetSize(orders))) saving = false;
				continue;
			}
			if (saving) { release_recovered(*recovered); saving = false; }
			if (wrapper && (!collect_plan_inputs(plan, controls, tables) || !emission_compatible(plan, wrapper, cell))) continue;
			if (wrapper && estimate_select({{cell, &wrapper->y, wrapper, &plan}}).status != CostStatus::Profitable) continue;
			if (!accepted || plan.count < best.count || (plan.count == best.count && plan.gates < best.gates)) {
				best = std::move(plan);
				accepted = true;
			}
		}
		// 字段选择保留原始 PMUX 的编码形式，全部编码均具有真实默认数据。
		if (!accepted && saving) {
			if (!selection.expanded) for (auto bit : s) if (!upstream(bit, outputs, dependency)) {
				release_recovered(*recovered);
				return false;
			}
			if (!spend(width)) { release_recovered(*recovered); return false; }
			log_assert(GetSize(recovered->plans) == GetSize(orders));
			recovered->y = y;
			recovered->original_gates = original_gates;
			recovered->ready = true;
			if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered complete orders=%d storage=%zu/%zu.\n",
				log_id(module), log_id(cell), GetSize(orders), recovered_nodes, recovered_roots);
		}
		if (accepted && field_gain && best.swaps == 0 && best.graph.complements == 0) {
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
		if (!accepted) log_debug("PMUX select %s.%s: selection cost rejected.\n", log_id(module), log_id(cell));
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
	void commit(Cell *cell, const SigSpec &y, Plan &plan, const std::vector<SigBit> &controls, const std::vector<std::vector<SigBit>> &tables) {
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
		log("    opt_pmuxselect [-defer-recovered | -recovered-only] [selection]\n\n");
		log("Recover bounded disjoint Boolean decoders and preserve all default table entries.\n");
		log("Share bounded Shannon graphs, complement edges and small data cofactors.\n");
		log("Accept only structural reductions with lower estimated selection costs.\n");
		log("Undefined input regions may be refined according to synthesis semantics.\n");
		log("-defer-recovered runs direct, Boolean and wrapper plans, saving remaining budgets.\n");
		log("-recovered-only consumes saved budgets for residual PMUX graphs after native optimizations.\n");
		log("Residual controls must pass bounded Boolean-source recovery; modules without saved budgets are skipped.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		bool defer_recovered = false, recovered_only = false;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-defer-recovered") { defer_recovered = true; continue; }
			if (args[argidx] == "-recovered-only") { recovered_only = true; continue; }
			break;
		}
		if (defer_recovered && recovered_only) log_cmd_error("Select one PMUX select stage.\n");
		extra_args(args, argidx, design);
		for (auto module : design->selected_modules()) {
			const std::string budget_key = "opt_pmuxselect.deferred." + module->name.str();
			auto save_budget = [&](int work, int cost, int diagnostic) {
				design->scratchpad_set_int(budget_key + ".work", std::max(0, work));
				design->scratchpad_set_int(budget_key + ".cost", std::max(0, cost));
				design->scratchpad_set_int(budget_key + ".diagnostic", std::max(0, diagnostic));
			};
			int remaining_work = 2000000, remaining_cost = 1048576, remaining_diagnostic = 16384;
			if (defer_recovered || recovered_only) {
				bool saved = design->scratchpad.count(budget_key + ".work") ||
					design->scratchpad.count(budget_key + ".cost") || design->scratchpad.count(budget_key + ".diagnostic");
				if (recovered_only && !saved) continue;
				if (saved) {
					remaining_work = design->scratchpad_get_int(budget_key + ".work", -1);
					remaining_cost = design->scratchpad_get_int(budget_key + ".cost", -1);
					remaining_diagnostic = design->scratchpad_get_int(budget_key + ".diagnostic", -1);
					if (remaining_work < 0 || remaining_work > 2000000 || remaining_cost < 0 || remaining_cost > 1048576 ||
						remaining_diagnostic < 0 || remaining_diagnostic > 16384)
						log_cmd_error("Incomplete or invalid deferred PMUX select budgets for module %s.\n", log_id(module));
				}
				design->scratchpad_unset(budget_key + ".work");
				design->scratchpad_unset(budget_key + ".cost");
				design->scratchpad_unset(budget_key + ".diagnostic");
			}
			bool has_candidate = false;
			for (auto cell : module->selected_cells()) if (cell->type == ID($pmux)) {
				has_candidate = true;
				break;
			}
			if (!has_candidate || ((defer_recovered || recovered_only) && remaining_work <= 0) ||
				(recovered_only && remaining_cost <= 0)) {
				if (defer_recovered) save_budget(remaining_work, remaining_cost, remaining_diagnostic);
				continue;
			}
			PmuxSelectWorker worker(module, design, recovered_only);
			if (defer_recovered || recovered_only) {
				worker.work = remaining_work;
				worker.cost_work = remaining_cost;
				worker.cost_diagnostic_work = remaining_diagnostic;
			}
			struct Edit {
				Cell *cell;
				SigSpec y;
				PmuxSelectWorker::Wrapper wrapper;
				PmuxSelectWorker::Plan plan;
				PmuxSelectWorker::Selection selection;
				std::vector<std::vector<SigBit>> tables;
				bool net = false;
				Edit() = default;
				Edit(const Edit &) = delete;
				Edit &operator=(const Edit &) = delete;
				Edit(Edit &&) = default;
				Edit &operator=(Edit &&) = default;
			};
			std::vector<Edit> edits;
			std::vector<Cell *> pending;
			std::vector<PmuxSelectWorker::Recovered> recovered;
			pool<Cell *> reserved;
			auto collect_candidate = [&](Cell *cell, bool expand) {
				Edit edit;
				edit.cell = cell;
				if (!worker.selection_table(cell, expand, edit.selection)) return false;
				PmuxSelectWorker::Recovered record;
				record.cell = cell;
				if (worker.candidate(cell, edit.selection, edit.plan, edit.tables, nullptr, defer_recovered ? nullptr : &record)) {
					edit.y = worker.sigmap(cell->getPort(ID::Y));
					reserved.insert(cell);
					edits.push_back(std::move(edit));
				} else {
					record.selection = std::move(edit.selection);
					recovered.push_back(std::move(record));
				}
				return true;
			};
			for (auto cell : module->selected_cells()) if (cell->type == ID($pmux)) {
				if (!collect_candidate(cell, recovered_only) && !recovered_only) pending.push_back(cell);
				if (worker.exhausted) break;
			}
			for (auto cell : pending) {
				if (worker.exhausted) break;
				collect_candidate(cell, true);
			}
			bool analyze_recovered = !recovered.empty() && (!recovered_only ||
				std::any_of(recovered.begin(), recovered.end(), [](const PmuxSelectWorker::Recovered &record) { return record.ready; }));
			if (defer_recovered && analyze_recovered &&
				std::none_of(recovered.begin(), recovered.end(), [](const PmuxSelectWorker::Recovered &record) { return record.ready; })) {
				analyze_recovered = false;
				for (auto cell : module->selected_cells()) if (cell->type == ID($mux) && !cell->get_bool_attribute(ID::keep)) {
					analyze_recovered = true;
					break;
				}
			}
			if (!worker.exhausted && analyze_recovered) {
				for (auto &edit : edits) worker.preserve_legacy(edit.cell, edit.y, edit.plan, edit.selection.controls, edit.tables);
				worker.cost_boundaries_frozen = true;
			}
			if (!worker.exhausted && analyze_recovered) worker.index_users();
			if (!recovered_only && worker.users_valid) for (auto &entry : recovered) {
				if (worker.exhausted || worker.cost_stopped) break;
				if (reserved.count(entry.cell)) continue;
				Edit edit;
				edit.cell = entry.cell;
				if (!worker.wrapper(edit.cell, edit.wrapper) || reserved.count(edit.wrapper.cell) ||
					!worker.wrapper_selection(entry.selection, edit.wrapper, edit.selection)) continue;
				log_debug("PMUX select %s.%s: recovered wrapper=%s controls=%d defaults=%d.\n", log_id(module), log_id(edit.cell),
					log_id(edit.wrapper.cell), GetSize(edit.selection.controls), edit.selection.defaults);
				if (!worker.candidate(edit.cell, edit.selection, edit.plan, edit.tables, &edit.wrapper)) continue;
				if (!worker.accept_plan(edit.plan, &edit.wrapper)) continue;
				edit.y = edit.wrapper.y;
				reserved.insert(edit.cell);
				reserved.insert(edit.wrapper.cell);
				edits.push_back(std::move(edit));
			}
			{
				std::vector<PmuxSelectWorker::CostView> wrapper_costs;
				for (auto &edit : edits) if (edit.wrapper.cell) wrapper_costs.push_back({edit.cell, &edit.y, &edit.wrapper, &edit.plan});
				if (!wrapper_costs.empty() && worker.estimate_select(wrapper_costs).status != PmuxSelectWorker::CostStatus::Profitable) {
					for (auto &edit : edits) if (edit.wrapper.cell) { reserved.erase(edit.cell); reserved.erase(edit.wrapper.cell); }
					edits.erase(std::remove_if(edits.begin(), edits.end(), [](const Edit &edit) { return edit.wrapper.cell != nullptr; }), edits.end());
					worker.emission_inputs.clear();
					worker.removed_outputs.clear();
				}
			}
			size_t wrapper_end = edits.size();
			for (auto &record : recovered) {
				int chosen = -1;
				if (record.ready && !reserved.count(record.cell) && !worker.exhausted && !worker.cost_stopped)
					chosen = worker.choose_recovered(record);
				if (chosen >= 0 && worker.accept_plan(record.plans[chosen].plan, nullptr)) {
					Edit edit;
					edit.cell = record.cell;
					edit.y = std::move(record.y);
					edit.selection = std::move(record.selection);
					edit.net = true;
					worker.release_recovered(record, chosen, &edit.plan);
					reserved.insert(edit.cell);
					edits.push_back(std::move(edit));
				} else worker.release_recovered(record);
			}
			if (edits.size() > wrapper_end) {
				std::vector<PmuxSelectWorker::CostView> combined;
				for (auto &edit : edits) if (edit.wrapper.cell || edit.net)
					combined.push_back({edit.cell, &edit.y, edit.wrapper.cell ? &edit.wrapper : nullptr, &edit.plan});
				if (worker.estimate_select(combined).status != PmuxSelectWorker::CostStatus::Profitable) {
					for (size_t i = wrapper_end; i < edits.size(); i++) worker.release_recovered_plan(edits[i].plan);
					edits.resize(wrapper_end);
				}
			}
			pool<SigBit> removed;
			pool<SigBit> final_outputs;
			pool<Cell *> final_targets;
			size_t stored_nodes = 0, stored_roots = 0;
			for (auto &edit : edits) {
				log_assert(final_targets.insert(edit.cell).second);
				if (edit.wrapper.cell) log_assert(final_targets.insert(edit.wrapper.cell).second);
				for (auto bit : edit.y) log_assert(final_outputs.insert(bit).second);
				if (edit.net) {
					stored_nodes += edit.plan.graph.nodes.capacity();
					stored_roots += edit.plan.roots.capacity();
				}
			}
			log_assert(worker.recovered_nodes == stored_nodes && worker.recovered_roots == stored_roots);
			if (worker.cost_diagnostic()) log_debug("PMUX select recovered storage in %s: nodes=%zu roots=%zu records=%d/%zu edits=%d/%zu.\n",
				log_id(module), stored_nodes, stored_roots, GetSize(recovered), recovered.capacity(), GetSize(edits), edits.capacity());
			for (auto &edit : edits) if (edit.wrapper.cell)
				for (auto bit : edit.wrapper.inner_y) log_assert(removed.insert(bit).second);
			if (!removed.empty()) for (auto &edit : edits) {
				log_assert(edit.plan.inputs_collected);
				for (auto bit : edit.plan.inputs) log_assert(!removed.count(bit));
			}
			// 所有计划在原始索引上完成，提交阶段使用保存的最终输出。
			for (auto &edit : edits) {
				if (edit.wrapper.cell)
					log("PMUX select %s.%s: committed mode=wrapper outer=%s inner_port=%s controls=%d defaults=%d.\n", log_id(module), log_id(edit.cell),
						log_id(edit.wrapper.cell), edit.wrapper.inner_b ? "B" : "A", GetSize(edit.selection.controls), edit.selection.defaults);
				else if (edit.net)
					log("PMUX select %s.%s: committed mode=recovered controls=%d defaults=%d.\n", log_id(module), log_id(edit.cell),
						GetSize(edit.selection.controls), edit.selection.defaults);
				else
					log("PMUX select %s.%s: committed mode=%s controls=%d defaults=%d.\n", log_id(module), log_id(edit.cell),
						edit.selection.expanded ? "boolean" : "direct", GetSize(edit.selection.controls), edit.selection.defaults);
				worker.commit(edit.cell, edit.y, edit.plan, edit.selection.controls, edit.tables);
				if (edit.wrapper.cell) module->remove(edit.wrapper.cell);
			}
			if (defer_recovered) save_budget(worker.work, worker.cost_work, worker.cost_diagnostic_work);
		}
	}
} OptPmuxSelectPass;

PRIVATE_NAMESPACE_END
