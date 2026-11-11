// opt_pmuxselect 恢复互斥选择编码，以共享选择图、互补关系和数据余因子缩减逻辑。
// 复用控制变量排列与端口分类，按结构成本选择字段分解和共享网络。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "passes/opt/pmux_decoder.h"
#include "passes/opt/pmux_lut_cost.h"
#include "passes/opt/pmux_netlist.h"
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
	using CostStatus = PmuxLutCost::CostStatus;
	Module *module;
	PmuxNetlist netlist;
	PmuxDecoder decoder;
	PmuxLutCost::ModuleCost module_cost;
	int work = 2000000;
	bool exhausted = false;
	bool recovered_only = false;
	int cost_work = 1048576;
	int cost_diagnostic_work = 16384;
	bool cost_stopped = false;
	size_t recovered_nodes = 0, recovered_roots = 0;
	pool<SigBit> preserved_inputs, emission_inputs, removed_outputs;

	PmuxSelectWorker(Module *module, Design *design, bool recovered_only = false)
		: module(module), netlist(module, design), decoder(netlist), module_cost(netlist), recovered_only(recovered_only) {}
	bool spend(int amount = 1) {
		work -= amount;
		if (work < 0) exhausted = true;
		return !exhausted;
	}
	static bool candidate_shape(Cell *cell) {
		if (cell->type != ID($pmux) || cell->get_bool_attribute(ID::keep) || !cell->hasParam(ID::WIDTH) ||
			!cell->hasParam(ID::S_WIDTH) || !cell->hasPort(ID::A) || !cell->hasPort(ID::B) ||
			!cell->hasPort(ID::S) || !cell->hasPort(ID::Y)) return false;
		int width = GetSize(cell->getPort(ID::Y)), branches = GetSize(cell->getPort(ID::S));
		return width >= 1 && width <= 256 && branches >= 3 && branches <= 64 &&
			cell->getParam(ID::WIDTH).as_int() == width && cell->getParam(ID::S_WIDTH).as_int() == branches &&
			GetSize(cell->getPort(ID::A)) == width && GetSize(cell->getPort(ID::B)) == width*branches;
	}
	struct Wrapper {
		Cell *cell = nullptr;
		bool inner_b = false;
		SigSpec other;
		SigBit select;
		SigSpec y, inner_y;
	};
	bool wrapper(Cell *cell, Wrapper &result) {
		const auto &y = netlist.port(cell, ID::Y);
		log_assert(!y.empty());
		const auto &first_users = netlist.users(y[0]);
		if (GetSize(first_users) != 1) return false;
		auto first = first_users[0];
		auto outer = first.cell;
		if (outer->type != ID($mux) || !first.port.in(ID::A, ID::B) || first.offset != 0 || !netlist.editable(outer)) return false;
		int width = GetSize(y);
		if (!outer->hasParam(ID::WIDTH) || outer->getParam(ID::WIDTH).as_int() != width ||
			!outer->hasPort(ID::A) || !outer->hasPort(ID::B) || !outer->hasPort(ID::S) ||
			GetSize(outer->getPort(ID::A)) != width || GetSize(outer->getPort(ID::B)) != width ||
			GetSize(outer->getPort(ID::Y)) != width || GetSize(outer->getPort(ID::S)) != 1) return false;
		if (netlist.port(outer, first.port) != y) return false;
		pool<SigBit> inner_outputs;
		for (int i = 0; i < width; i++) {
			if (!spend() || netlist.protected_bit(y[i])) return false;
			const auto &uses = netlist.users(y[i]);
			if (GetSize(uses) != 1) return false;
			auto use = uses[0];
			if (use.cell != outer || use.port != first.port || use.offset != i) return false;
			inner_outputs.insert(y[i]);
		}
		const auto &output = netlist.port(outer, ID::Y);
		for (auto bit : output) if (!spend() || inner_outputs.count(bit)) return false;
		auto select = netlist.port(outer, ID::S)[0];
		if (!select.wire && select.data > State::S1) return false;
		result.cell = outer;
		result.inner_b = first.port == ID::B;
		result.other = netlist.port(outer, result.inner_b ? ID::A : ID::B);
		result.select = select;
		result.y = output;
		if (!cost_spend(width)) return false;
		result.inner_y = y;
		return true;
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
		const auto *entry = netlist.source(bit);
		if (!entry) return false;
		auto cell = entry->cell;
		if (context.expand && (!cell || netlist.kept(bit))) { result = atom(bit); context.cache[bit] = result; return true; }
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
			for (auto &port : cell->connections()) if (netlist.cell_input(cell->type, port.first)) {
				edges += GetSize(port.second);
				for (auto input : netlist.port(cell, port.first)) if (!input.wire && input.data > State::S1) return false;
			}
			context.edges += edges;
			if (context.edges > 2048 || !control_spend(context, 1+edges)) return false;
		}
		PmuxDecoder::Cube cube;
		if (decoder.decode(bit, cube, context.expand)) {
			result = atom(cube.dead ? State::S0 : State::S1);
			if (!cube.dead) for (auto &constraint : cube.bits) {
				Function input = atom(constraint.first);
				if (context.expand && !control(constraint.first, context, input, depth-1)) return false;
				if (!constraint.second && !control_combine(context, ID($not), {input}, input)) return false;
				if (!control_combine(context, ID($and), {result, input}, result)) return false;
			}
			if (cube.inverted &&
				!control_combine(context, ID($not), {result}, result)) return false;
		} else if (!context.expand) return false;
		else if (compare) result = atom(bit);
		else if ((logic || reduce) && entry->offset > 0) result = atom(State::S0);
		else if (logic || reduce) {
			IdString type = cell->type == ID($reduce_and) ? ID($and) :
				cell->type.in(ID($reduce_xor), ID($reduce_xnor)) ? ID($xor) : ID($or);
			if (!control_reduce(netlist.port(cell, ID::A), type, context, result, depth-1)) return false;
			if (logic) {
				Function other;
				if (!control_reduce(netlist.port(cell, ID::B), ID($or), context, other, depth-1) ||
					!control_combine(context, cell->type == ID($logic_and) ? ID($and) : ID($or), {result, other}, result)) return false;
			}
			if (cell->type == ID($reduce_xnor) && !control_combine(context, ID($not), {result}, result)) return false;
		} else {
			Function input;
			std::vector<Function> args;
			if (!control(netlist.operand(cell, ID::A, entry->offset), context, input, depth-1)) return false;
			args.push_back(input);
			if (binary || mux) {
				if (!control(netlist.operand(cell, ID::B, entry->offset), context, input, depth-1)) return false;
				args.push_back(input);
			}
			if (mux) {
				if (!control(netlist.port(cell, ID::S)[0], context, input, depth-1)) return false;
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
		if (!candidate_shape(cell) || !netlist.editable(cell)) return false;
		const auto &s = netlist.port(cell, ID::S), &y = netlist.port(cell, ID::Y);
		int width = GetSize(y), branches = GetSize(s);
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
		if (!spend() || depth == 0 || GetSize(cache) >= 65536 || GetSize(expanded) >= 4096 || netlist.kept(bit)) return atom(bit);
		const auto *entry = netlist.source(bit);
		if (!entry || !entry->cell) return atom(bit);
		if (!active.insert(bit).second) { exhausted = true; return atom(bit); }
		auto cell = entry->cell;
		bool unary = cell->type.in(ID($not), ID($pos), ID($buf));
		bool binary = cell->type.in(ID($and), ID($or), ID($xor), ID($xnor));
		bool mux = cell->type == ID($mux) && GetSize(cell->getPort(ID::S)) == 1;
		Function result = atom(bit);
		if (unary || binary || mux) {
			std::vector<Function> args;
			args.push_back(expression(netlist.operand(cell, ID::A, entry->offset), code, controls, cache, active, expanded, depth-1));
			if (binary || mux) args.push_back(expression(netlist.operand(cell, ID::B, entry->offset), code, controls, cache, active, expanded, depth-1));
			if (mux) args.push_back(expression(netlist.port(cell, ID::S)[0], code, controls, cache, active, expanded, depth-1));
			Function combined;
			if (combine(cell->type, args, 3, combined)) { result = std::move(combined); expanded.insert(cell); }
		}
		active.erase(bit);
		cache[key] = result;
		return result;
	}
	int build(PmuxSelectGraph &graph, const std::vector<int> &table, const std::vector<SigBit> &order,
			const PmuxNetlist::Dependencies &dependency, int depth = 0, int code = 0) {
		if (!spend()) { graph.overflow = true; return graph.leaf(State::Sx); }
		if (depth == GetSize(order)) return table[code];
		int a = build(graph, table, order, dependency, depth+1, code);
		int b = build(graph, table, order, dependency, depth+1, code | (1 << depth));
		return graph.mux(graph.leaf(order[depth], dependency.high_z(order[depth])), a, b);
	}
	int function_graph(PmuxSelectGraph &graph, const Function &f, const PmuxNetlist::Dependencies &dependency) {
		std::vector<int> values;
		for (auto value : f.table) values.push_back(graph.leaf(value));
		return build(graph, values, f.support, dependency);
	}
	int reference_tree(const std::vector<SigBit> &table, const std::vector<int> &permuted) {
		struct Node { int a, b; };
		std::array<Node, 127> nodes;
		std::array<int, 64> refs;
		std::array<bool, 127> seen = {};
		dict<SigBit, int> leaves;
		dict<std::tuple<int, int, int>, int> unique;
		int count = 0, size = GetSize(permuted), depth = 0;
		log_assert(size > 0 && size <= 64 && !(size & (size-1)));
		for (int code = 0; code < size; code++) {
			auto bit = table[permuted[code]];
			auto found = leaves.find(bit);
			if (found != leaves.end()) refs[code] = found->second;
			else {
				refs[code] = leaves[bit] = count;
				nodes[count++] = {-1, -1};
			}
		}
		while ((1 << depth) < size) depth++;
		for (int level = depth-1; level >= 0; level--) for (int code = 0; code < (1 << level); code++) {
			int a = refs[code], b = refs[code | (1 << level)];
			if (a == b && nodes[a].a < 0) continue;
			auto key = std::make_tuple(level, a, b);
			auto found = unique.find(key);
			if (found != unique.end()) refs[code] = found->second;
			else {
				log_assert(count < GetSize(nodes));
				refs[code] = unique[key] = count;
				nodes[count++] = {a, b};
			}
		}
		auto visit = [&](auto &&self, int ref, int level) -> int {
			if (!spend(size >> level)) return 0;
			if (nodes[ref].a < 0 || seen[ref]) return 0;
			seen[ref] = true;
			return 1+self(self, nodes[ref].a, level+1)+self(self, nodes[ref].b, level+1);
		};
		return visit(visit, refs[0], 0);
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
	void preserve_plan_inputs(const SigSpec &y, Plan &plan, const std::vector<SigBit> &controls,
			const std::vector<std::vector<SigBit>> &tables) {
		if (!collect_plan_inputs(plan, controls, tables) || !cost_spend(GetSize(y)+GetSize(plan.inputs))) return;
		module_cost.preserve(y, plan.inputs);
		preserved_inputs.insert(plan.inputs.begin(), plan.inputs.end());
	}
	bool emission_compatible(const Plan &plan, const Wrapper *wrapper, Cell *cell) {
		log_assert(plan.inputs_collected);
		if (!cost_spend(GetSize(plan.inputs)+(wrapper ? GetSize(wrapper->inner_y) : 0))) return false;
		if (wrapper) for (auto bit : wrapper->inner_y) if (preserved_inputs.count(bit) || emission_inputs.count(bit)) {
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
	struct CostView {
		Cell *cell;
		const SigSpec *y;
		const Wrapper *wrapper;
		const Plan *plan;
	};
	using PlanCost = dict<std::pair<int, int>, PmuxLutCost::Signal>;

	PmuxLutCost::Signal cost_node(const PmuxSelectGraph &graph, int ref, PmuxLutCost::Builder &builder, int depth, PlanCost &memo) {
		log_assert(ref >= 0 && ref / 2 < GetSize(graph.nodes));
		if (depth <= 0) return builder.fail(CostStatus::DepthLimit);
		if (!builder.spend()) return builder.fail(CostStatus::BudgetExhausted);
		auto key = std::make_pair(ref, depth);
		auto found = memo.find(key);
		if (found != memo.end()) return found->second;
		const auto &node = graph.nodes[ref / 2];
		PmuxLutCost::Signal signal;
		if (ref & 1) signal = builder.operation(1, {cost_node(graph, ref ^ 1, builder, depth - 1, memo)});
		else if (!node.kind) signal = builder.bit(node.bit, depth - 1);
		else {
			auto a = cost_node(graph, node.a, builder, depth - 1, memo);
			auto b = cost_node(graph, node.b, builder, depth - 1, memo);
			if (node.kind == 1) signal = builder.operation(0xca, {a, b, cost_node(graph, node.s, builder, depth - 1, memo)});
			else {
				log_assert(node.kind == 2);
				signal = builder.operation(6, {a, b});
			}
		}
		return memo[key] = signal;
	}

	bool cost_request(const std::vector<CostView> &edits, PmuxLutCost::Request &request) {
		log_assert(!edits.empty());
		pool<Cell *> rewritten;
		for (const auto &edit : edits) {
			log_assert(edit.cell && edit.y && edit.plan && !edit.plan->fields && GetSize(*edit.y) == GetSize(edit.plan->roots));
			log_assert(rewritten.insert(edit.cell).second);
			if (!cost_spend(1 + GetSize(*edit.y) + (edit.wrapper ? GetSize(edit.wrapper->inner_y) : 0))) return false;
			if (edit.wrapper) {
				log_assert(edit.wrapper->cell && rewritten.insert(edit.wrapper->cell).second);
				for (auto bit : edit.wrapper->inner_y) log_assert(request.removed.insert(bit).second);
			}
			auto memo = std::make_shared<PlanCost>();
			const auto *graph = &edit.plan->graph;
			for (int i = 0; i < GetSize(*edit.y); i++) {
				auto bit = (*edit.y)[i];
				int ref = edit.plan->roots[i];
				log_assert(!request.replacements.count(bit));
				request.replacements[bit] = [this, graph, ref, memo](PmuxLutCost::Builder &builder, int depth) {
					return cost_node(*graph, ref, builder, depth, *memo);
				};
			}
		}
		return true;
	}

	PmuxLutCost::CostResult estimate_select(const std::vector<CostView> &edits, const PmuxLutCost::Snapshot *snapshot = nullptr) {
		PmuxLutCost::Request request;
		if (!cost_request(edits, request)) return {CostStatus::BudgetExhausted};
		int initial = std::min(work, cost_work), remaining = initial;
		auto result = module_cost.estimate(request, remaining, snapshot);
		cost_spend(initial - remaining);
		if (cost_diagnostic()) log_debug("PMUX select %s cost in %s: %s %d -> %d, %d targets, work used %d, remaining %d.\n",
			edits.front().wrapper ? "wrapper" : "recovered", log_id(module), PmuxLutCost::status_name(result.status), result.before, result.after,
			GetSize(edits), initial - remaining, cost_work);
		return result;
	}
	// recovered 保留原输出，确认直接 MUX 使用环境的形状和输入依赖。
	bool recovered_context(Cell *cell) {
		pool<Cell *> checked;
		for (auto bit : netlist.port(cell, ID::Y)) {
			if (!cost_spend()) return false;
			for (auto use : netlist.users(bit)) {
				if (!cost_spend()) return false;
				auto outer = use.cell;
				if (outer->type != ID($mux) || !checked.insert(outer).second) continue;
				if (!cost_spend(4) || GetSize(outer->connections()) != 4 || !outer->hasParam(ID::WIDTH) ||
					!outer->hasPort(ID::A) || !outer->hasPort(ID::B) || !outer->hasPort(ID::S) || !outer->hasPort(ID::Y)) return false;
				const auto &output = netlist.port(outer, ID::Y);
				int width = GetSize(output);
				if (width < 1 || width != outer->getParam(ID::WIDTH).as_int() || !cost_spend(width) ||
					GetSize(netlist.port(outer, ID::A)) != width || GetSize(netlist.port(outer, ID::B)) != width ||
					GetSize(netlist.port(outer, ID::S)) != 1) return false;
				pool<SigBit> outputs;
				for (int i = 0; i < width; i++) {
					auto bit = output[i];
					auto driver = netlist.source(bit);
					if (!driver || driver->cell != outer || driver->port != ID::Y || driver->offset != i || !outputs.insert(bit).second) return false;
				}
				PmuxNetlist::Dependencies dependency(netlist, outputs, work);
				for (auto port : {ID::A, ID::B, ID::S}) for (auto input : netlist.port(outer, port))
					if (!dependency.visit(input)) return false;
			}
		}
		return work > 0 && cost_work > 0;
	}
	int choose_recovered(Recovered &record) {
		log_assert(record.ready && !record.plans.empty());
		if (!recovered_context(record.cell)) return -1;
		PmuxLutCost::Snapshot snapshot;
		CostView view = {record.cell, &record.y, nullptr, &record.plans[0].plan};
		PmuxLutCost::Request request;
		if (!cost_request({view}, request)) return -1;
		int initial = std::min(work, cost_work), remaining = initial;
		auto status = module_cost.checkpoint(request, remaining, snapshot);
		cost_spend(initial - remaining);
		if (status != CostStatus::NoGain) {
			if (cost_diagnostic()) log_debug("PMUX select %s.%s: recovered snapshot %s.\n", log_id(module), log_id(record.cell), PmuxLutCost::status_name(status));
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
				PmuxLutCost::status_name(result.status), result.before, result.after);
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
		if (!spend(0) || (wrapper && cost_stopped)) return false;
		const auto &a = netlist.port(cell, ID::A), &b = netlist.port(cell, ID::B), &s = netlist.port(cell, ID::S), &y = netlist.port(cell, ID::Y);
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
		PmuxNetlist::Dependencies dependency(netlist, outputs, work, true);
		for (auto bit : a) if (!dependency.visit(bit)) return false;
		for (auto bit : b) if (!dependency.visit(bit)) return false;
		for (auto bit : controls) if (!dependency.visit(bit)) return false;
		if (selection.expanded || wrapper) for (auto bit : s) if (!dependency.visit(bit)) return false;
		if (wrapper) {
			if (!dependency.visit(wrapper->select)) return false;
			for (auto bit : wrapper->other) if (!dependency.visit(bit)) return false;
			if (!spend(width*size)) return false;
		}
		tables.assign(width, {});
		for (auto &table : tables) table.reserve(size);
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
		struct TableKey {
			const std::vector<SigBit> *table;
			bool operator==(const TableKey &other) const { return *table == *other.table; }
			[[nodiscard]] Hasher hash_into(Hasher h) const { h.eat(*table); return h; }
		};
		dict<TableKey, int> output_tables;
		std::vector<int> representatives;
		representatives.reserve(width);
		for (int j = 0; j < width; j++) {
			auto found = output_tables.find({&tables[j]});
			if (found != output_tables.end()) representatives.push_back(found->second);
			else { output_tables[{&tables[j]}] = j; representatives.push_back(j); }
		}
		std::vector<int> masks;
		int field_choices = 0, support_saved = 0;
		bool need_fields = !recovered_only || ys_debug(1);
		{
			dict<std::pair<SigBit, int>, Function> cache; pool<SigBit> active; pool<Cell *> expanded;
			for (int j = 0; j < width; j++) {
				int representative = representatives[j];
				if (need_fields) {
					int mask = representative < j ? masks[representative] : 0;
					if (representative == j) for (int i = 0; i < GetSize(controls); i++)
						for (int c = 0; c < size; c++) if (!(c & (1 << i)) && tables[j][c] != tables[j][c | (1 << i)]) { mask |= 1 << i; break; }
					masks.push_back(mask);
					int support_size = __builtin_popcount(unsigned(mask));
					field_choices += 1 << support_size;
					support_saved += GetSize(controls) - support_size;
				}
				if (representative < j) {
					for (int c = 0; c < size; c++) expression(tables[j][c], c, positions, cache, active, expanded, 8);
					continue;
				}
				functions[j].reserve(size);
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
		bool field_gain = !recovered_only && !wrapper && support_saved > 0 && 4*field_choices <= 3*width*branches;
		// 原始数据叶节点全局互异时，完整选择图与参考树具有相同节点数量。
		auto distinct_table = [&]() {
			if (wrapper || recovered || size < 4) return false;
			pool<SigBit> seen;
			for (int j = 0; j < width; j++) {
				int representative = representatives[j];
				if (!cofactors[representative].atoms.empty()) return false;
				for (int c = 0; c < size; c++) {
					auto bit = tables[j][c];
					if (!bit.wire || !seen.insert(bit).second) return false;
					const auto &function = functions[representative][c];
					if (GetSize(function.support) > 1) continue;
					if (GetSize(function.support) != 1 || function.support[0] != bit || GetSize(function.table) != 2 ||
						function.table[0] != State::S0 || function.table[1] != State::S1) return false;
				}
			}
			return true;
		};
		if (distinct_table()) {
			log_debug("PMUX select %s.%s: complete distinct data table has no sharing gain.\n", log_id(module), log_id(cell));
			return false;
		}
		int original_gates = 0;
		if (!recovered_only || ys_debug(1)) {
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
			struct BuiltOutput { int root, reference, work, complements, swaps; };
			std::vector<BuiltOutput> built(width);
			for (int j = 0; j < width; j++) {
				int representative = representatives[j];
				if (representative < j) {
					const auto &output = built[representative];
					if (!spend(output.work)) break;
					plan.reference += output.reference;
					plan.graph.complements += output.complements;
					plan.swaps += output.swaps;
					plan.roots.push_back(output.root);
					continue;
				}
				int initial_work = work, initial_complements = plan.graph.complements, initial_swaps = plan.swaps;
				int reference = reference_tree(tables[j], permuted);
				plan.reference += reference;
				std::vector<int> leaves(size);
				for (int c = 0; c < size; c++) {
					int index = permuted[c];
					auto &function = functions[j][index];
					auto bit = tables[j][index];
					leaves[c] = GetSize(function.support) <= 1 ? function_graph(plan.graph, function, dependency) : plan.graph.leaf(bit, dependency.high_z(bit));
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
				built[j] = {result, reference, initial_work-work, plan.graph.complements-initial_complements, plan.swaps-initial_swaps};
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
			if (!recovered_only) for (int root : plan.roots) separate += plan.graph.cost({root}, cost_context).first;
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
			if (!selection.expanded) for (auto bit : s) if (!dependency.visit(bit)) {
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
		if (accepted && !best.fields) std::vector<std::vector<SigBit>>().swap(tables);
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
			for (auto cell : module->selected_cells()) if (PmuxSelectWorker::candidate_shape(cell)) {
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
					edit.y = worker.netlist.port(cell, ID::Y);
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
			if (!worker.exhausted && analyze_recovered)
				for (auto &edit : edits) worker.preserve_plan_inputs(edit.y, edit.plan, edit.selection.controls, edit.tables);
			if (!worker.exhausted && analyze_recovered && !recovered_only) for (auto &entry : recovered) {
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
