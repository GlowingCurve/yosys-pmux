// opt_pmuxlut 将结构化 PMUX 编码为共享四输入逻辑，处理字段分解、首位检测和使能关系。
// 合并相同真值表节点，减少重复译码与选择运算。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/pmux_celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxLutGraph {
	struct Node {
		SigBit bit;
		std::vector<int> inputs;
		unsigned mask = 0;
	};
	std::vector<Node> nodes;
	dict<SigBit, int> leaves;
	std::map<std::pair<std::vector<int>, unsigned>, int> shared;
	bool overflow = false;
	int leaf(SigBit bit) {
		auto found = leaves.find(bit);
		if (found != leaves.end()) return found->second;
		int index = GetSize(nodes);
		nodes.push_back({bit, {}, 0});
		leaves[bit] = index;
		return index;
	}
	int lut(const std::vector<int> &args, unsigned mask) {
		log_assert(GetSize(args) <= 4);
		std::vector<int> inputs;
		for (int arg : args) {
			log_assert(arg >= 0 && arg < GetSize(nodes));
			auto &node = nodes[arg];
			if (node.inputs.empty() && !node.bit.wire) {
				log_assert(node.bit.data <= State::S1);
				continue;
			}
			if (std::find(inputs.begin(), inputs.end(), arg) == inputs.end()) inputs.push_back(arg);
		}
		std::sort(inputs.begin(), inputs.end());
		unsigned table = 0;
		for (int code = 0; code < (1 << GetSize(inputs)); code++) {
			int original = 0;
			for (int j = 0; j < GetSize(args); j++) {
				auto found = std::find(inputs.begin(), inputs.end(), args[j]);
				bool value = found == inputs.end() ? nodes[args[j]].bit == State::S1 : bool(code & (1 << (found-inputs.begin())));
				if (value) original |= 1 << j;
			}
			if (mask & (1u << original)) table |= 1u << code;
		}
		for (int j = GetSize(inputs)-1; j >= 0; j--) {
			bool relevant = false;
			for (int code = 0; code < (1 << GetSize(inputs)); code++)
				if (!(code & (1 << j)) && ((table >> code) & 1) != ((table >> (code | (1 << j))) & 1)) relevant = true;
			if (relevant) continue;
			unsigned next = 0;
			int offset = 0;
			for (int code = 0; code < (1 << GetSize(inputs)); code++) if (!(code & (1 << j))) {
				if (table & (1u << code)) next |= 1u << offset;
				offset++;
			}
			inputs.erase(inputs.begin()+j);
			table = next;
		}
		if (inputs.empty()) return leaf(table ? State::S1 : State::S0);
		if (GetSize(inputs) == 1 && table == 2) return inputs[0];
		auto key = std::make_pair(inputs, table);
		auto found = shared.find(key);
		if (found != shared.end()) return found->second;
		if (GetSize(nodes) >= 16384) {
			overflow = true;
			return leaf(State::S0);
		}
		int index = GetSize(nodes);
		nodes.push_back({SigBit(), inputs, table});
		shared[key] = index;
		return index;
	}
	template<typename F> int function(const std::vector<int> &args, F f) {
		unsigned mask = 0;
		for (int code = 0; code < (1 << GetSize(args)); code++) if (f(code)) mask |= 1u << code;
		return lut(args, mask);
	}
	int mux(int a, int b, int s) { return lut({a, b, s}, 0xca); }
	int invert(int index) {
		auto node = nodes[index];
		if (node.inputs.empty()) return lut({index}, 1);
		return lut(node.inputs, node.mask ^ ((1u << (1 << GetSize(node.inputs)))-1));
	}
	int reduce(std::vector<int> values, bool conjunction = false) {
		if (values.empty()) return leaf(conjunction ? State::S1 : State::S0);
		while (GetSize(values) > 1) {
			std::vector<int> next;
			for (int i = 0; i < GetSize(values); i += 4) {
				std::vector<int> group(values.begin()+i, values.begin()+std::min(i+4, GetSize(values)));
				int all = (1 << GetSize(group))-1;
				next.push_back(function(group, [=](int c) { return conjunction ? c == all : c != 0; }));
			}
			values = std::move(next);
		}
		return values[0];
	}
	void visit(int index, pool<int> &seen) const {
		if (!seen.insert(index).second) return;
		for (int input : nodes[index].inputs) visit(input, seen);
	}
	int cost(const std::vector<int> &roots, pool<SigBit> &referenced) const {
		pool<int> seen;
		int count = 0;
		for (int root : roots) visit(root, seen);
		for (int index : seen) {
			auto &node = nodes[index];
			if (node.inputs.empty()) referenced.insert(node.bit); else count++;
		}
		return count;
	}
};

struct PmuxLutWorker {
	Module *module;
	Design *design;
	SigMap sigmap;
	PmuxCellTypes types;
	struct Driver { Cell *cell = nullptr; int count = 0; };
	dict<SigBit, Driver> drivers;
	dict<SigBit, pool<Cell *>> users;
	pool<SigBit> observed, kept, unknown, input_bits;
	int budget = 200000;
	PmuxLutWorker(Module *m, Design *d) : module(m), design(d), sigmap(m), types(m, d) {
		for (auto wire : module->wires()) for (auto bit : sigmap(wire)) {
			if (wire->port_input) { drivers[bit].count++; input_bits.insert(bit); }
			if (wire->port_output || wire->get_bool_attribute(ID::keep)) observed.insert(bit);
			if (wire->get_bool_attribute(ID::keep)) kept.insert(bit);
		}
		for (auto cell : module->cells()) for (auto &port : cell->connections()) {
			bool input = types.cell_input(cell->type, port.first), output = types.cell_output(cell->type, port.first);
			for (auto bit : sigmap(port.second)) {
				if (output) { drivers[bit].count++; drivers[bit].cell = cell; }
				if (input || !output) users[bit].insert(cell);
				if (!input && !output) { unknown.insert(bit); observed.insert(bit); }
				if (cell->get_bool_attribute(ID::keep)) kept.insert(bit);
			}
		}
	}
	bool unique(SigBit bit) const { return bit.wire && !unknown.count(bit) && drivers.count(bit) && drivers.at(bit).count == 1; }
	bool data_source(SigBit bit) const {
		if (!unique(bit)) return false;
		auto cell = drivers.at(bit).cell;
		if (!cell) return input_bits.count(bit);
		if (!StaticCellTypes::categories.is_ff(cell->type) || !cell->hasPort(ID::Q) || !types.cell_output(cell->type, ID::Q)) return false;
		for (auto output : sigmap(cell->getPort(ID::Q))) if (output == bit) return true;
		return false;
	}
	bool editable(Cell *cell) const {
		if (!design->selected(module, cell) || cell->get_bool_attribute(ID::keep) || !cell->hasPort(ID::Y)) return false;
		pool<SigBit> seen;
		for (auto bit : sigmap(cell->getPort(ID::Y)))
			if (!unique(bit) || drivers.at(bit).cell != cell || kept.count(bit) || !seen.insert(bit).second) return false;
		return true;
	}
	bool upstream(SigBit bit, const pool<SigBit> &outputs, dict<SigBit, int> &state, int depth = 0) {
		if (--budget < 0 || depth > 128 || outputs.count(bit) || unknown.count(bit)) return false;
		if (!bit.wire) return bit.data <= State::S1 && !drivers.count(bit);
		if (!unique(bit)) return false;
		if (state.count(bit)) return state.at(bit) == 2;
		auto cell = drivers.at(bit).cell;
		if (!cell || StaticCellTypes::categories.is_ff(cell->type)) { state[bit] = 2; return true; }
		if (!types.cell_evaluable(cell->type)) return false;
		state[bit] = 1;
		for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first))
			for (auto input : sigmap(port.second)) if (!upstream(input, outputs, state, depth+1)) return false;
		state[bit] = 2; return true;
	}
	struct Cube { dict<SigBit, bool> bits; };
	bool decode(SigBit bit, Cube &cube, pool<Cell *> &expanded) {
		if (--budget < 0 || !unique(bit)) return false;
		auto cell = drivers.at(bit).cell;
		if (!cell || StaticCellTypes::categories.is_ff(cell->type)) { cube.bits[bit] = true; return true; }
		if (!cell->type.in(ID($eq), ID($logic_not))) return false;
		if (GetSize(cell->getPort(ID::Y)) != 1) return false;
		auto a = sigmap(cell->getPort(ID::A));
		if (a.empty() || GetSize(a) > 64) return false;
		SigSpec b(State::S0, GetSize(a));
		if (cell->type == ID($eq)) {
			b = sigmap(cell->getPort(ID::B));
			if (b.empty() || GetSize(b) > 64) return false;
			bool sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
			int width = std::max(GetSize(a), GetSize(b)); a.extend_u0(width, sign); b.extend_u0(width, sign);
		}
		for (int j = 0; j < GetSize(a); j++) {
			auto x = a[j], y = b[j];
			if ((!x.wire && x.data > State::S1) || (!y.wire && y.data > State::S1)) return false;
			if (x == y) continue;
			if (!x.wire) std::swap(x, y);
			if (!x.wire || y.wire || y.data > State::S1 || (cube.bits.count(x) && cube.bits.at(x) != (y == State::S1))) return false;
			cube.bits[x] = y == State::S1;
		}
		if (cube.bits.empty()) return false;
		expanded.insert(cell);
		return true;
	}
	struct Plan {
		Cell *root = nullptr;
		PmuxLutGraph graph;
		std::vector<int> roots;
		pool<Cell *> expanded, remove;
		SigSpec y;
		int reference = 0;
		bool private_decoders = false;
	};
	bool private_logic(Plan &plan) {
		pool<SigBit> referenced;
		int cost = plan.graph.cost(plan.roots, referenced);
		if (plan.graph.overflow || cost == 0) return false;
		plan.remove = plan.expanded;
		plan.remove.insert(plan.root);
		bool changed;
		do {
			changed = false;
			std::vector<Cell *> cells(plan.remove.begin(), plan.remove.end());
			for (auto cell : cells) {
				if (cell == plan.root) continue;
				bool preserve = !editable(cell);
				for (auto &port : cell->connections()) if (types.cell_output(cell->type, port.first)) for (auto bit : sigmap(port.second)) {
					if (observed.count(bit) || kept.count(bit) || referenced.count(bit)) preserve = true;
					for (auto user : users[bit]) if (!plan.remove.count(user)) preserve = true;
				}
				if (preserve) {
					plan.remove.erase(cell);
					changed = true;
				}
			}
		} while (changed);
		if (plan.private_decoders) for (auto cell : plan.expanded) if (!plan.remove.count(cell)) return false;
		// 使用固定点后实际可删除的控制逻辑核算剩余成本。
		int retained = 0;
		for (auto cell : plan.expanded) if (!plan.remove.count(cell)) {
			int width = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 1;
			retained += std::max(1, (width+1)/3);
		}
		if (cost + retained >= plan.reference) return false;
		pool<SigBit> outputs;
		dict<SigBit, int> state;
		for (auto bit : plan.y) outputs.insert(bit);
		for (auto bit : referenced) if (!upstream(bit, outputs, state)) return false;
		return true;
	}
	bool priority(Cell *cell, Plan &plan) {
		if (cell->type != ID($mux) || !editable(cell)) return false;
		int width = GetSize(cell->getPort(ID::Y));
		if (width < 2 || width > 128) return false;
		std::vector<SigBit> select;
		std::vector<SigSpec> data;
		auto current = cell;
		for (int depth = 0; depth < 4; depth++) {
			if (!editable(current) || current->type != ID($mux) || GetSize(current->getPort(ID::Y)) != width ||
				GetSize(current->getPort(ID::A)) != width || GetSize(current->getPort(ID::B)) != width || GetSize(current->getPort(ID::S)) != 1) return false;
			select.push_back(sigmap(current->getPort(ID::S))[0]);
			data.push_back(sigmap(current->getPort(ID::B)));
			plan.expanded.insert(current);
			auto a = sigmap(current->getPort(ID::A));
			if (depth == 3) {
				if (a != SigSpec(State::S0, width)) return false;
			}
			else {
				if (!unique(a[0]) || !drivers.at(a[0]).cell) return false;
				current = drivers.at(a[0]).cell;
				if (!current->hasPort(ID::Y) || sigmap(current->getPort(ID::Y)) != a) return false;
			}
		}
		auto &g = plan.graph;
		std::vector<int> s;
		for (auto bit : select) {
			if (!bit.wire && bit.data > State::S1) return false;
			s.push_back(g.leaf(bit));
		}
		for (int j = 0; j < width; j++) {
			pool<SigBit> distinct;
			for (int i = 0; i < 4; i++) if (!data[i][j].wire || !distinct.insert(data[i][j]).second) return false;
			int u = g.function({s[0], g.leaf(data[0][j]), s[1], g.leaf(data[1][j])}, [](int c) { return c & 1 ? bool(c & 2) : bool((c & 4) && (c & 8)); });
			int v = g.function({s[2], g.leaf(data[2][j]), s[3], g.leaf(data[3][j])}, [](int c) { return c & 1 ? bool(c & 2) : bool((c & 4) && (c & 8)); });
			plan.roots.push_back(g.function({s[0], s[1], u, v}, [](int c) { return c & 3 ? bool(c & 4) : bool(c & 8); }));
		}
		plan.reference = 4*width;
		return true;
	}
	bool onehot(Plan &plan, const std::vector<Cube> &cubes, const SigSpec &a, const SigSpec &b) {
		int branches = GetSize(cubes), width = GetSize(a);
		if (branches < 4 || branches > 16 || a != SigSpec(State::S0, width)) return false;
		std::vector<SigBit> controls;
		for (auto &entry : cubes[0].bits) controls.push_back(entry.first);
		std::sort(controls.begin(), controls.end());
		if (GetSize(controls) != branches) return false;
		std::vector<int> branch(branches, -1);
		for (int i = 0; i < branches; i++) {
			if (GetSize(cubes[i].bits) != branches) return false;
			int active = -1;
			for (int j = 0; j < branches; j++) {
				if (!cubes[i].bits.count(controls[j])) return false;
				if (cubes[i].bits.at(controls[j])) {
					if (active >= 0) return false;
					active = j;
				}
			}
			if (active < 0 || branch[active] >= 0) return false;
			branch[active] = i;
		}
		auto &g = plan.graph;
		std::vector<int> present, multiple;
		std::vector<std::vector<int>> selected(width);
		for (int i = 0; i < branches; i += 4) {
			std::vector<int> s;
			for (int k = i; k < std::min(i+4, branches); k++) s.push_back(g.leaf(controls[k]));
			present.push_back(g.function(s, [](int c) { return c != 0; }));
			multiple.push_back(g.function(s, [](int c) { return (c & (c-1)) != 0; }));
			for (int j = 0; j < width; j++) {
				std::vector<int> pairs;
				for (int k = 0; k < GetSize(s); k += 2) {
					std::vector<int> args = {s[k], g.leaf(b[branch[i+k]*width+j])};
					if (k+1 < GetSize(s)) {
						args.push_back(s[k+1]);
						args.push_back(g.leaf(b[branch[i+k+1]*width+j]));
					}
					pairs.push_back(g.function(args, [](int c) { return (c & 3) == 3 || (c & 12) == 12; }));
				}
				selected[j].push_back(g.reduce(pairs));
			}
		}
		int cross = g.function(present, [](int c) { return (c & (c-1)) != 0; }), local = g.reduce(multiple);
		for (int j = 0; j < width; j++) plan.roots.push_back(g.function({g.reduce(selected[j]), cross, local}, [](int c) { return c == 1; }));
		plan.reference = width*(branches-1) + branches*((branches+1)/3);
		return true;
	}
	struct Encoding {
		int present;
		std::vector<int> code;
	};
	Encoding leading_graph(PmuxLutGraph &g, const std::vector<int> &bits) {
		if (GetSize(bits) == 4) {
			Encoding result;
			result.present = g.function(bits, [](int c) { return c != 0; });
			for (int j = 0; j < 2; j++) result.code.push_back(g.function(bits, [=](int c) {
				int index = 0;
				while (index < 4 && !(c & (1 << index))) index++;
				return index < 4 && bool(index & (1 << j));
			}));
			return result;
		}
		log_assert(GetSize(bits) == 16);
		std::vector<Encoding> groups;
		std::vector<int> present;
		for (int i = 0; i < 16; i += 4) {
			groups.push_back(leading_graph(g, std::vector<int>(bits.begin()+i, bits.begin()+i+4)));
			present.push_back(groups.back().present);
		}
		auto high = leading_graph(g, present);
		Encoding result;
		result.present = high.present;
		for (int j = 0; j < 2; j++) {
			int low = g.mux(groups[0].code[j], groups[1].code[j], high.code[0]);
			int upper = g.mux(groups[2].code[j], groups[3].code[j], high.code[0]);
			result.code.push_back(g.mux(low, upper, high.code[1]));
		}
		result.code.insert(result.code.end(), high.code.begin(), high.code.end());
		return result;
	}
	bool leading(Plan &plan, const std::vector<Cube> &cubes, const SigSpec &a, const SigSpec &b) {
		int count = GetSize(cubes), width = GetSize(a);
		if ((count != 4 && count != 16) || width < (count == 4 ? 3 : 5) || width > 32 || a != SigSpec(Const(count, width))) return false;
		std::vector<int> order(count, -1);
		std::vector<SigBit> bits;
		for (int i = 0; i < count; i++) {
			int length = GetSize(cubes[i].bits);
			if (length < 1 || length > count || order[length-1] >= 0) return false;
			order[length-1] = i;
		}
		for (int k = 0; k < count; k++) {
			if (order[k] < 0 || b.extract(order[k]*width, width) != SigSpec(Const(k, width))) return false;
			auto &cube = cubes[order[k]];
			SigBit next;
			int ones = 0;
			for (auto &entry : cube.bits) if (entry.second) {
				next = entry.first;
				ones++;
			}
			if (ones != 1 || std::find(bits.begin(), bits.end(), next) != bits.end()) return false;
			for (auto bit : bits) if (!cube.bits.count(bit) || cube.bits.at(bit)) return false;
			bits.push_back(next);
		}
		auto &g = plan.graph;
		std::vector<int> inputs;
		for (auto bit : bits) inputs.push_back(g.leaf(bit));
		auto result = leading_graph(g, inputs);
		plan.roots = result.code;
		plan.roots.push_back(g.invert(result.present));
		while (GetSize(plan.roots) < width) plan.roots.push_back(g.leaf(State::S0));
		plan.reference = count*2+2;
		return true;
	}
	int encoded_tree(PmuxLutGraph &g, const std::vector<int> &data, const std::vector<SigBit> &controls,
			const std::vector<std::pair<SigBit, bool>> &prefix, int level) {
		if (GetSize(data) == 1) return data[0];
		log_assert(!data.empty() && GetSize(data) % 2 == 0 && level < GetSize(controls));
		std::vector<int> next;
		for (int i = 0; i < GetSize(data); i += 2) {
			std::vector<int> args = {data[i], data[i+1], g.leaf(controls[level])};
			if (level < GetSize(prefix)) args.push_back(g.leaf(prefix[level].first));
			bool polarity = level < GetSize(prefix) && prefix[level].second;
			bool gated = level < GetSize(prefix);
			next.push_back(g.function(args, [=](int c) { return (!gated || bool(c & 8) == polarity) && bool(c & 4 ? c & 2 : c & 1); }));
		}
		return encoded_tree(g, next, controls, prefix, level+1);
	}
	bool encoded(Plan &plan, const std::vector<Cube> &cubes, const SigSpec &a, const SigSpec &b) {
		int branches = GetSize(cubes), width = GetSize(a);
		if (branches < 4 || branches > 16 || (branches & (branches-1))) return false;
		std::vector<std::pair<SigBit, bool>> prefix;
		std::vector<SigBit> controls;
		for (auto &entry : cubes[0].bits) {
			bool common = true;
			for (auto &cube : cubes) if (!cube.bits.count(entry.first) || cube.bits.at(entry.first) != entry.second) common = false;
			if (common) prefix.push_back(entry); else controls.push_back(entry.first);
		}
		std::sort(controls.begin(), controls.end());
		int levels = GetSize(controls);
		if (levels > 4 || (1 << levels) != branches || GetSize(prefix) > levels || (!prefix.empty() && a != SigSpec(State::S0, width))) return false;
		std::vector<int> table(branches, -1);
		for (int i = 0; i < branches; i++) {
			if (GetSize(cubes[i].bits) != levels+GetSize(prefix)) return false;
			int code = 0;
			for (int j = 0; j < levels; j++) {
				auto bit = cubes[i].bits.find(controls[j]);
				if (bit == cubes[i].bits.end()) return false;
				if (bit->second) code |= 1 << j;
			}
			for (auto &entry : prefix) if (!cubes[i].bits.count(entry.first) || cubes[i].bits.at(entry.first) != entry.second) return false;
			if (table[code] >= 0) return false;
			table[code] = i;
		}
		auto &g = plan.graph;
		// 前缀文字按层分配，每条输入路径经过全部条件。
		if (!prefix.empty() || branches == 4 || width < 4) {
			for (int j = 0; j < width; j++) {
				std::vector<int> data;
				for (int i : table)
					data.push_back(g.leaf(b[i*width+j]));
				plan.roots.push_back(encoded_tree(g, data, controls, prefix, 0));
			}
		} else {
			for (int j = 0; j < width; j++) {
				pool<SigBit> distinct;
				for (int i : table) if (!data_source(b[i*width+j]) || !distinct.insert(b[i*width+j]).second) return false;
			}
			// 共享组译码，组内二选一与有效条件共同占用四个输入。
			std::vector<int> enable;
			int groups = branches/2;
			for (int group = 0; group < groups; group++) {
				std::vector<int> args;
				for (int k = 1; k < levels; k++)
					args.push_back(g.leaf(controls[k]));
				enable.push_back(g.function(args, [=](int c) { return c == group; }));
			}
			for (int j = 0; j < width; j++) {
				std::vector<int> terms;
				for (int group = 0; group < groups; group++) terms.push_back(g.lut({g.leaf(b[table[2*group]*width+j]), g.leaf(b[table[2*group+1]*width+j]), g.leaf(controls[0]), enable[group]}, 0xca00));
				plan.roots.push_back(g.reduce(terms));
			}
		}
		plan.private_decoders = prefix.empty();
		plan.reference = width*(branches-1) + (!prefix.empty() ? (GetSize(prefix)+2)/3 : 0);
		return true;
	}
	bool candidate(Cell *cell, Plan &plan) {
		if (!editable(cell)) return false;
		plan.root = cell;
		plan.y = sigmap(cell->getPort(ID::Y));
		if (cell->type == ID($mux)) return priority(cell, plan) && private_logic(plan);
		if (cell->type != ID($pmux)) return false;
		auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S));
		int width = GetSize(plan.y), branches = GetSize(s);
		if (width < 1 || width > 128 || branches < 4 || branches > 16 || GetSize(a) != width || GetSize(b) != width*branches) return false;
		for (auto bit : b) if (!bit.wire && bit.data > State::S1) return false;
		std::vector<Cube> cubes(branches);
		for (int i = 0; i < branches; i++) if (!decode(s[i], cubes[i], plan.expanded)) return false;
		Plan trial = plan;
		if (leading(trial, cubes, a, b) && private_logic(trial)) {
			plan = std::move(trial);
			return true;
		}
		trial = plan;
		if (onehot(trial, cubes, a, b) && private_logic(trial)) {
			plan = std::move(trial);
			return true;
		}
		trial = plan;
		if (encoded(trial, cubes, a, b) && private_logic(trial)) {
			plan = std::move(trial);
			return true;
		}
		return false;
	}
	SigBit materialize(Plan &plan, int index, dict<int, SigBit> &cache, IdString celltype) {
		log_assert(index >= 0 && index < GetSize(plan.graph.nodes));
		auto found = cache.find(index);
		if (found != cache.end()) return found->second;
		auto &node = plan.graph.nodes[index];
		if (node.inputs.empty()) return node.bit;
		SigSpec inputs;
		for (int input : node.inputs) inputs.append(materialize(plan, input, cache, celltype));
		auto wire = module->addWire(NEW_ID);
		if (celltype.empty()) module->addLut(NEW_ID, inputs, wire, Const(node.mask, 1 << GetSize(inputs)));
		else {
			auto cell = module->addCell(NEW_ID, celltype);
			unsigned mask = 0;
			for (int code = 0; code < 16; code++) if (node.mask & (1u << (code & ((1 << GetSize(inputs))-1)))) mask |= 1u << code;
			cell->setParam(ID(lut_mask), Const(mask, 16));
			cell->setParam(ID(sum_lutc_input), Const("datac"));
			IdString ports[] = {ID(dataa), ID(datab), ID(datac), ID(datad)};
			for (int j = 0; j < 4; j++) cell->setPort(ports[j], j < GetSize(inputs) ? inputs[j] : SigBit(State::S0));
			cell->setPort(ID(combout), wire);
			cell->setPort(ID(cin), State::S0);
		}
		cache[index] = SigBit(wire);
		return SigBit(wire);
	}
	void commit(Plan &plan, IdString celltype) {
		log_assert(GetSize(plan.y) == GetSize(plan.roots));
		dict<int, SigBit> cache;
		SigSpec result;
		for (int root : plan.roots) result.append(materialize(plan, root, cache, celltype));
		module->connect(plan.y, result);
		for (auto cell : plan.remove) module->remove(cell);
	}
};

struct OptPmuxLutPass : public Pass {
	OptPmuxLutPass() : Pass("opt_pmuxlut", "construct bounded shared LUT4 selection networks") {}
	void help() override {
		log("    opt_pmuxlut [-lut4 <celltype>] [selection]\n\n");
		log("Recognize complete equality tables, single-active-bit tables, consecutive\n");
		log("leading-zero prefixes and four-level priority selectors. Preserve defaults\n");
		log("and all priority conditions. Emit shared four-input $lut cells by default.\n");
		log("-lut4 emits Intel-style dataa/datab/datac/datad/combout cells with lut_mask\n");
		log("and sum_lutc_input=datac. Run after proc and width reduction, before techmap.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		IdString celltype;
		size_t argidx = 1;
		if (argidx < args.size() && args[argidx] == "-lut4") {
			if (argidx+1 >= args.size()) log_cmd_error("Missing cell type for -lut4.\n");
			celltype = RTLIL::escape_id(args[argidx+1]);
			argidx += 2;
		}
		extra_args(args, argidx, design);
		for (auto module : design->selected_modules()) {
			std::vector<Cell *> candidates;
			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($mux) && GetSize(cell->getPort(ID::Y)) >= 2) candidates.push_back(cell);
				if (cell->type == ID($pmux) && GetSize(cell->getPort(ID::S)) >= 4 && GetSize(cell->getPort(ID::S)) <= 16) candidates.push_back(cell);
			}
			if (candidates.empty()) continue;
			PmuxLutWorker worker(module, design);
			std::vector<PmuxLutWorker::Plan> plans;
			pool<Cell *> reserved;
			for (auto cell : candidates) {
				if (worker.budget < 0) break;
				PmuxLutWorker::Plan plan;
				if (!worker.candidate(cell, plan)) continue;
				bool overlap = false;
				for (auto remove : plan.remove) if (reserved.count(remove)) overlap = true;
				if (overlap) continue;
				for (auto remove : plan.remove) reserved.insert(remove);
				plans.push_back(std::move(plan));
			}
			for (auto &plan : plans) worker.commit(plan, celltype);
		}
	}
} OptPmuxLutPass;

PRIVATE_NAMESPACE_END
