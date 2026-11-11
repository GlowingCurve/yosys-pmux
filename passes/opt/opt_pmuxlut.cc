// opt_pmuxlut 将结构化 PMUX 编码为共享四输入逻辑，处理字段分解、首位检测和使能关系。
// 合并相同真值表节点，减少重复译码与选择运算。
#include "kernel/yosys.h"
#include "kernel/utils.h"
#include "passes/opt/pmux_decoder.h"
#include "passes/opt/pmux_lut_cost.h"
#include "passes/opt/pmux_lut_graph.h"
#include "passes/opt/pmux_netlist.h"

#include <algorithm>
#include <functional>
#include <memory>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxLutWorker {
	Module *module;
	PmuxNetlist netlist;
	PmuxDecoder decoder;
	int budget = 200000;
	IdString celltype;
	bool priority_generic;
	PmuxLutWorker(Module *m, Design *d, IdString celltype, bool priority_generic)
		: module(m), netlist(m, d), decoder(netlist), celltype(celltype), priority_generic(priority_generic) {}

	bool data_source(SigBit bit) const {
		auto source = netlist.source(bit);
		return source && (source->cell == nullptr ||
			(source->port == ID::Q && StaticCellTypes::categories.is_ff(source->cell->type)));
	}
	using Cube = PmuxDecoder::Cube;

	struct Plan {
		Cell *root = nullptr;
		PmuxLutGraph graph{PmuxLutGraph::Expansion::None, 16384};
		std::vector<int> roots;
		pool<Cell *> expanded, remove;
		SigSpec y;
		int reference = 0;
		int cost = 0, retained = 0;
		bool priority = false;
		int cover_before = -1, cover_after = -1;
		bool extended_priority = false;
		bool private_decoders = false;
	};
	struct PriorityReference {
		PmuxLutGraph graph{PmuxLutGraph::Expansion::None, 16384};
		dict<Cell *, std::vector<int>> outputs;
	};
	IdString emission_type(const Plan &plan) const {
		if (priority_generic && plan.priority && (plan.extended_priority || plan.cost == 0)) return IdString();
		return celltype;
	}
	bool priority_cover(Plan &plan, const PriorityReference &reference,
		const std::vector<int> &original_roots, const std::vector<int> &retained_roots) {
		PmuxLutCost::LutCostGraph graph(budget);
		dict<SigBit, std::pair<Cell *, int>> sources;
		for (auto &entry : reference.outputs) {
			const auto &output = netlist.port(entry.first, ID::Y);
			log_assert(GetSize(output) == GetSize(entry.second));
			for (int i = 0; i < GetSize(output); i++) {
				if (--budget < 0) return false;
				sources[output[i]] = {entry.first, entry.second[i]};
			}
		}
		dict<int, int> original, candidate;
		pool<int> active;
		bool valid = true;
		enum class SourceGraph { Original, Candidate };
		std::function<int(SourceGraph, int)> import_node = [&](SourceGraph source_graph, int index) -> int {
			if (--budget < 0) { valid = false; return 0; }
			bool from_original = source_graph == SourceGraph::Original;
			if (from_original && !active.insert(index).second) { valid = false; return 0; }
			auto &cache = from_original ? original : candidate;
			auto found = cache.find(index);
			if (found != cache.end()) {
				if (from_original) active.erase(index);
				return found->second;
			}
			const auto &node = (from_original ? reference.graph : plan.graph).node(index);
			int result;
			if (node.leaf) {
				auto source = sources.find(node.bit);
				if (source == sources.end()) result = graph.leaf(node.bit);
				else {
					if (!from_original && plan.remove.count(source->second.first)) { valid = false; return 0; }
					result = import_node(SourceGraph::Original, source->second.second);
				}
			} else {
				std::vector<int> inputs;
				for (int input : node.inputs) {
					if (--budget < 0) { valid = false; return 0; }
					inputs.push_back(import_node(source_graph, input));
				}
				result = graph.gate(node.mask, inputs);
			}
			if (from_original) active.erase(index);
			cache[index] = result;
			return result;
		};
		std::vector<int> before, after;
		for (int root : original_roots) before.push_back(import_node(SourceGraph::Original, root));
		for (int root : plan.roots) after.push_back(import_node(SourceGraph::Candidate, root));
		for (int root : retained_roots) after.push_back(import_node(SourceGraph::Original, root));
		if (!valid || !graph.valid || budget < 0) return false;
		plan.cover_before = GetSize(graph.cover(before));
		if (!graph.valid) return false;
		plan.cover_after = GetSize(graph.cover(after));
		if (!graph.valid) return false;
		bool strict = plan.extended_priority || plan.cost == 0;
		bool accepted = strict ? plan.cover_after < plan.cover_before : plan.cover_after <= plan.cover_before;
		if (!accepted)
			log_debug("PMUX LUT priority cover rejected %s: before=%d after=%d strict=%d.\n",
				log_id(plan.root), plan.cover_before, plan.cover_after, strict);
		return accepted;
	}
	bool private_logic(Plan &plan, PriorityReference *reference = nullptr) {
		pool<SigBit> referenced;
		int cost = plan.graph.cost(plan.roots, referenced);
		bool priority = plan.priority;
		log_assert(priority == (reference != nullptr));
		if (plan.graph.overflowed() || (cost == 0 && !priority)) return false;
		pool<SigBit> outputs(plan.y.begin(), plan.y.end());
		pool<Cell *> region = plan.expanded;
		region.insert(plan.root);
		plan.remove = netlist.private_cells(region, {plan.root}, outputs, referenced);
		if (!plan.remove.count(plan.root)) return false;
		bool all_private = plan.private_decoders || (priority && (plan.extended_priority || cost == 0));
		if (all_private)
			for (auto cell : plan.expanded) if (!plan.remove.count(cell)) return false;
		// 使用固定点后实际可删除的控制逻辑核算剩余成本。
		int retained = 0;
		std::vector<int> original_roots, retained_roots;
		if (priority) {
			if ((budget -= 2*reference->graph.node_count()) < 0) return false;
			original_roots = reference->outputs.at(plan.root);
			for (auto cell : plan.expanded) if (!plan.remove.count(cell)) {
				auto &roots = reference->outputs.at(cell);
				original_roots.insert(original_roots.end(), roots.begin(), roots.end());
				retained_roots.insert(retained_roots.end(), roots.begin(), roots.end());
			}
			plan.reference = reference->graph.cost(original_roots);
			retained = reference->graph.cost(retained_roots);
		} else {
			for (auto cell : plan.expanded) if (!plan.remove.count(cell)) {
				int width = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 1;
				retained += std::max(1, (width+1)/3);
			}
		}
		if (cost + retained >= plan.reference) return false;
		plan.cost = cost;
		plan.retained = retained;
		if (!netlist.independent(referenced, outputs, budget)) return false;
		if (priority && (emission_type(plan).empty() || plan.extended_priority || cost == 0) &&
			!priority_cover(plan, *reference, original_roots, retained_roots)) return false;
		return true;
	}
	int priority_reference(PriorityReference &reference, const std::vector<Cell *> &chain, const std::vector<SigBit> &select,
			const std::vector<SigSpec> &data, int width) {
		auto &g = reference.graph;
		std::vector<int> previous(width, g.leaf(State::S0));
		for (int depth = 3; depth >= 0; depth--) {
			auto &outputs = reference.outputs[chain[depth]];
			int s = g.leaf(select[depth]);
			for (int j = 0; j < width; j++) {
				if (--budget < 0) return -1;
				outputs.push_back(g.mux(previous[j], g.leaf(data[depth][j]), s));
			}
			previous = outputs;
		}
		if (g.overflowed() || (budget -= g.node_count()) < 0) return -1;
		return g.cost(previous);
	}
	int priority_function(PmuxLutGraph &g, const std::vector<int> &select, const std::vector<int> &data,
			int first, int last, int previous) {
		if ((budget -= 1+2*(last-first)) < 0) return -1;
		std::vector<int> inputs;
		auto add = [&](int index) {
			const auto &node = g.node(index);
			if (node.leaf && !node.bit.wire) {
				log_assert(node.bit.data <= State::S1);
				return;
			}
			if (std::find(inputs.begin(), inputs.end(), index) == inputs.end()) inputs.push_back(index);
		};
		add(previous);
		for (int depth = first; depth < last; depth++) {
			add(select[depth]);
			add(data[depth]);
		}
		if (GetSize(inputs) > 4) return -1;
		if ((budget -= 1 << GetSize(inputs)) < 0) return -1;
		// 每颗 LUT 覆盖完整优先子函数，保留未知控制下的已知输出。
		return g.function(inputs, [&](int code) {
			auto value = [&](int index) {
				const auto &node = g.node(index);
				if (node.leaf && !node.bit.wire) return node.bit == State::S1;
				auto found = std::find(inputs.begin(), inputs.end(), index);
				log_assert(found != inputs.end());
				return bool(code & (1 << (found-inputs.begin())));
			};
			bool result = value(previous);
			for (int depth = last-1; depth >= first; depth--)
				if (value(select[depth])) result = value(data[depth]);
			return result;
		});
	}
	bool priority(Cell *cell, Plan &plan, PriorityReference &reference) {
		if (cell->type != ID($mux) || !netlist.editable(cell)) return false;
		int width = GetSize(cell->getPort(ID::Y));
		if (width < 2 || width > 128) return false;
		std::vector<SigBit> select;
		std::vector<SigSpec> data;
		std::vector<Cell *> chain;
		auto current = cell;
		for (int depth = 0; depth < 4; depth++) {
			if (!netlist.editable(current) || current->type != ID($mux) || GetSize(current->getPort(ID::Y)) != width ||
				GetSize(current->getPort(ID::A)) != width || GetSize(current->getPort(ID::B)) != width || GetSize(current->getPort(ID::S)) != 1) return false;
			select.push_back(netlist.port(current, ID::S)[0]);
			data.push_back(netlist.port(current, ID::B));
			plan.expanded.insert(current);
			chain.push_back(current);
			const auto &a = netlist.port(current, ID::A);
			if (depth == 3) {
				if (a != SigSpec(State::S0, width)) return false;
			}
			else {
				current = netlist.driver(a[0]);
				if (!current || !current->hasPort(ID::Y) || netlist.port(current, ID::Y) != a) return false;
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
			std::vector<int> d;
			for (int i = 0; i < 4; i++) {
				auto bit = data[i][j];
				if (!bit.wire && bit.data > State::S1) return false;
				if (!bit.wire || !distinct.insert(bit).second) plan.extended_priority = true;
				d.push_back(g.leaf(bit));
			}
			int root = priority_function(g, s, d, 0, 4, g.leaf(State::S0));
			if (budget < 0) return false;
			if (root < 0) {
				int v = priority_function(g, s, d, 2, 4, g.leaf(State::S0));
				if (budget < 0) return false;
				log_assert(v >= 0);
				root = priority_function(g, s, d, 0, 2, v);
				if (budget < 0) return false;
				if (root < 0) {
					if ((budget -= 2) < 0) return false;
					root = g.mux(g.mux(v, d[1], s[1]), d[0], s[0]);
				}
			}
			plan.roots.push_back(root);
		}
		plan.priority = true;
		plan.reference = priority_reference(reference, chain, select, data, width);
		return plan.reference >= 0;
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
	int encoded_tree(PmuxLutGraph &g, const std::vector<int> &data, const SigSpec &controls,
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
		PmuxDecoder::Table decoded;
		if (!decoder.table(plan.root, cubes, decoded)) return false;
		const auto &prefix = decoded.prefix;
		const auto &controls = decoded.control;
		const auto &table = decoded.branch_for_code;
		int levels = GetSize(controls);
		if (levels > 4 || (1 << levels) != branches || GetSize(prefix) > levels || (!prefix.empty() && a != SigSpec(State::S0, width))) return false;
		log_assert(GetSize(table) == branches);
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
		if (!netlist.editable(cell)) return false;
		plan.root = cell;
		plan.y = netlist.port(cell, ID::Y);
		if (cell->type == ID($mux)) {
			PriorityReference reference;
			return priority(cell, plan, reference) && private_logic(plan, &reference);
		}
		if (cell->type != ID($pmux)) return false;
		const auto &a = netlist.port(cell, ID::A), &b = netlist.port(cell, ID::B), &s = netlist.port(cell, ID::S);
		int width = GetSize(plan.y), branches = GetSize(s);
		if (width < 1 || width > 128 || branches < 4 || branches > 16 || GetSize(a) != width || GetSize(b) != width*branches) return false;
		for (auto bit : b) if (!bit.wire && bit.data > State::S1) return false;
		std::vector<Cube> cubes(branches);
		for (int i = 0; i < branches; i++) {
			auto &cube = cubes[i];
			if (--budget < 0 || !decoder.decode(s[i], cube, false, true) || cube.dead || cube.bits.empty()) return false;
			if (cube.cell) {
				if (GetSize(netlist.port(cube.cell, ID::Y)) != 1) return false;
				plan.expanded.insert(cube.cell);
			} else if (!data_source(s[i]))
				return false;
		}
		for (auto build : {&PmuxLutWorker::leading, &PmuxLutWorker::onehot, &PmuxLutWorker::encoded}) {
			Plan trial;
			trial.root = plan.root;
			trial.y = plan.y;
			trial.expanded = plan.expanded;
			if ((this->*build)(trial, cubes, a, b) && private_logic(trial)) {
				plan = std::move(trial);
				return true;
			}
		}
		return false;
	}
	void commit(Plan &plan) {
		log_assert(GetSize(plan.y) == GetSize(plan.roots));
		if (plan.priority) {
			log_debug("PMUX LUT priority %s: reference=%d candidate=%d retained=%d removed=%d.\n",
				log_id(plan.root), plan.reference, plan.cost, plan.retained, GetSize(plan.remove));
			if (plan.cover_before >= 0)
				log_debug("PMUX LUT priority cover %s: before=%d after=%d.\n", log_id(plan.root), plan.cover_before, plan.cover_after);
		}
		module->connect(plan.y, plan.graph.emit(module, emission_type(plan), plan.roots));
		for (auto cell : plan.remove) module->remove(cell);
	}
};

struct OptPmuxLutPass : public Pass {
	OptPmuxLutPass() : Pass("opt_pmuxlut", "construct bounded shared LUT4 selection networks") {}
	void help() override {
		log("    opt_pmuxlut [-lut4 <celltype>] [-priority-generic] [selection]\n\n");
		log("Recognize complete equality tables, single-active-bit tables, consecutive\n");
		log("leading-zero prefixes and four-level priority selectors. Preserve defaults\n");
		log("and all priority conditions. Emit shared four-input $lut cells by default.\n");
		log("-lut4 emits Intel-style dataa/datab/datac/datad/combout cells with lut_mask\n");
		log("and sum_lutc_input=datac. Run after proc and width reduction, before techmap.\n");
		log("-priority-generic emits $lut cells for repeated-data, constant-data and\n");
		log("zero-LUT priority rewrites for subsequent general logic mapping. Ordinary\n");
		log("priority networks and the other families follow -lut4.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		IdString celltype;
		bool priority_generic = false;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-lut4") {
				if (argidx+1 >= args.size()) log_cmd_error("Missing cell type for -lut4.\n");
				celltype = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-priority-generic") { priority_generic = true; continue; }
			break;
		}
		extra_args(args, argidx, design);
		for (auto module : design->selected_modules()) {
			std::vector<Cell *> candidates;
			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($mux) && GetSize(cell->getPort(ID::Y)) >= 2) candidates.push_back(cell);
				if (cell->type == ID($pmux) && GetSize(cell->getPort(ID::S)) >= 4 && GetSize(cell->getPort(ID::S)) <= 16) candidates.push_back(cell);
			}
			if (candidates.empty()) continue;
			PmuxLutWorker worker(module, design, celltype, priority_generic);
			std::vector<std::unique_ptr<PmuxLutWorker::Plan>> plans;
			pool<Cell *> reserved;
			for (auto cell : candidates) {
				if (worker.budget < 0) break;
				auto plan = std::make_unique<PmuxLutWorker::Plan>();
				if (!worker.candidate(cell, *plan)) continue;
				bool overlap = false;
				for (auto remove : plan->remove) if (reserved.count(remove)) overlap = true;
				if (overlap) continue;
				for (auto remove : plan->remove) reserved.insert(remove);
				plans.push_back(std::move(plan));
			}
			for (auto &plan : plans) worker.commit(*plan);
		}
	}
} OptPmuxLutPass;

PRIVATE_NAMESPACE_END
