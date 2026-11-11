// opt_pmuxrel 共享互补字段、交换字段和关联布尔输出；合并重复的选择与四输入逻辑节点。
// tables 模式用 32 位并行求值分解五位地址表，将输出使能并入共享 LUT 网络。
#include "kernel/yosys.h"
#include "kernel/utils.h"
#include "passes/opt/pmux_decoder.h"
#include "passes/opt/pmux_lut_graph.h"
#include "passes/opt/pmux_netlist.h"
#include <algorithm>
#include <bitset>
#include <cstdint>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RelationWorker {
	Module *module;
	PmuxNetlist netlist;
	PmuxDecoder decoder;
	IdString luttype;
	int budget = 60000;
	RelationWorker(Module *m, Design *d, IdString t) : module(m), netlist(m, d), decoder(netlist), luttype(t) {}

	using Cube = PmuxDecoder::Cube;
	using Table = PmuxDecoder::Table;

	bool table(Cell *cell, Table &result) {
		if (cell->type != ID($pmux) || !netlist.editable(cell)) return false;
		const auto &a = netlist.port(cell, ID::A), &b = netlist.port(cell, ID::B), &s = netlist.port(cell, ID::S);
		int width = GetSize(a), branches = GetSize(s);
		if (width < 1 || width > 128 || branches < 3 || branches > 16 || GetSize(b) != width*branches) return false;
		std::vector<Cube> cubes(branches);
		for (int j = 0; j < branches; j++) {
			auto &cube = cubes[j];
			if (--budget < 0 || !decoder.decode(s[j], cube) || !cube.cell || !netlist.editable(cube.cell) ||
			    GetSize(netlist.port(cube.cell, ID::Y)) != 1) return false;
		}
		if (!decoder.table(cell, cubes, result) || !result.prefix.empty() || GetSize(result.control) < 2) return false;
		for (const auto &branch : result.data)
			for (auto bit : branch)
				if (!bit.wire && bit.data > State::S1) return false;
		return true;
	}

	struct Plan {
		PmuxLutGraph graph{PmuxLutGraph::Expansion::Subsets, 24000};
		SigSpec targets;
		std::vector<int> roots;
		pool<Cell *> region, remove;
		int reference = 0;
		bool columns = false;
		int retained_reference = 0;
		int shared_columns = 0;
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
	bool prepare_rewrite(Plan &plan)
	{
		if (plan.targets.empty() || plan.graph.overflowed()) return false;
		log_assert(GetSize(plan.targets) == GetSize(plan.roots));
		pool<SigBit> target(plan.targets.begin(),plan.targets.end());
		if (GetSize(target) != GetSize(plan.targets)) return false;
		auto leaves = plan.graph.referenced(plan.roots);
		if (!netlist.independent(leaves, target, budget)) return false;
		plan.remove = netlist.private_cells(plan.region, {}, target, leaves);
		return true;
	}
	bool profitable_relations(const Plan &plan)
	{
		pool<SigBit> target(plan.targets.begin(), plan.targets.end());
		int retained = 0;
		for (auto cell : plan.region) if (!plan.remove.count(cell)) {
			bool root = false;
			for (auto bit : netlist.port(cell, ID::Y))
				if (target.count(bit)) root = true;
			if (!root) retained += cell_cost(cell);
		}
		return plan.graph.cost(plan.roots) + retained < plan.reference;
	}
	void commit(const std::vector<Plan> &plans) {
		// 在修改连接关系和删除单元之前，使用网表索引断开所有被替换的输出位。
		for (const auto &plan : plans) {
			pool<SigBit> targets(plan.targets.begin(), plan.targets.end());
			for (auto cell : plan.region)
				if (!plan.remove.count(cell))
					netlist.disconnect_outputs(cell, targets);
		}
		for (const auto &plan : plans) {
			if (plan.columns) {
				int cost = plan.graph.cost(plan.roots);
				log_assert(cost + plan.retained_reference < plan.reference);
				log_debug("opt_pmuxrel columns outputs=%d shared=%d ordinary=%d original=%d retained=%d candidate=%d removed=%d\n",
				          GetSize(plan.targets), plan.shared_columns, GetSize(plan.targets)-plan.shared_columns, plan.reference,
				          plan.retained_reference, cost, GetSize(plan.remove));
			}
			log_assert(GetSize(plan.targets) == GetSize(plan.roots));
			module->connect(plan.targets, plan.graph.emit(module, luttype, plan.roots));
			for (auto cell : plan.remove) module->remove(cell);
		}
	}
	dict<Cell *, bool> xor_sources;
	pool<Cell *> exchange_sources;
	bool xor_pair(SigBit bit, std::vector<SigBit> &leaves, pool<Cell *> &region) {
		auto source = netlist.source(bit);
		if (!source || !source->cell || source->cell->type != ID($xor)) return false;
		auto cell = source->cell;
		auto found = xor_sources.find(cell);
		if (found == xor_sources.end()) {
			auto &valid = xor_sources[cell];
			int width = GetSize(cell->getPort(ID::Y));
			if ((budget -= width) < 0 || !netlist.editable(cell)) return false;
			int a_width = GetSize(cell->getPort(ID::A)), b_width = GetSize(cell->getPort(ID::B));
			if ((budget -= std::max(width,a_width) + std::max(width,b_width) + 2*width) < 0) return false;
			valid = true;
		}
		if (!xor_sources.at(cell) || source->port != ID::Y) return false;
		auto a = netlist.operand(cell, ID::A, source->offset), b = netlist.operand(cell, ID::B, source->offset);
		if (!a.wire || !b.wire || a == b) return false;
		leaves = {a, b};
		std::sort(leaves.begin(), leaves.end());
		region.insert(cell);
		return true;
	}
	struct Field {
		SigBit y;
		std::vector<SigBit> data;
		std::vector<std::vector<SigBit>> xor_inputs;
		pool<Cell *> xor_region;
		bool parity_valid = false, exchange_valid = false;
	};
	bool parity(const Field &p, const Field &q, const SigSpec &control, Plan &plan) {
		if (GetSize(control) != 2 || !p.parity_valid || !q.parity_valid) return false;
		auto &pl = p.xor_inputs;
		auto &ql = q.xor_inputs;
		std::vector<SigBit> common;
		for (int code = 0; code < 4; code++) {
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
		for (auto cell : p.xor_region) plan.region.insert(cell);
		for (auto cell : q.xor_region) plan.region.insert(cell);
		plan.reference += 14;
		return true;
	}
	bool exchange_input(SigBit bit) {
		auto source = netlist.source(bit);
		if (!source) return false;
		auto cell = source->cell;
		if (!cell) return true;
		if (source->port != ID::Q || !StaticCellTypes::categories.is_ff(cell->type)) return false;
		if (exchange_sources.insert(cell).second)
			budget -= 2*GetSize(cell->getPort(ID::Q));
		return budget >= 0;
	}
	bool exchange(const Field &p, const Field &q, const SigSpec &control, Plan &plan) {
		int n = GetSize(control), count = 1 << n;
		if (n < 3 || n > 4 || !p.exchange_valid || !q.exchange_valid) return false;
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
	bool relation_pairs(std::vector<Field> &fields, const SigSpec &control, std::vector<std::bitset<128>> &pairs) {
		int count = 1 << GetSize(control);
		pairs.resize(fields.size());
		int eligible = 0;
		if (GetSize(control) == 2) {
			using Signature = std::vector<std::vector<SigBit>>;
			dict<Signature,int> ids;
			std::vector<std::vector<int>> groups;
			std::vector<std::bitset<128>> masks;
			for (int j = 0; j < GetSize(fields); j++) {
				auto &field = fields[j];
				field.xor_inputs.resize(count);
				bool valid = true;
				for (int code = 0; code < count; code++) {
					if (--budget < 0) return false;
					if (!xor_pair(field.data[code],field.xor_inputs[code],field.xor_region)) {
						valid = false;
						break;
					}
				}
				field.parity_valid = valid;
				if (!valid) continue;
				eligible++;
				Signature signature(count-1);
				for (int code = 1; code < count; code++) {
					if (--budget < 0) return false;
					std::set_symmetric_difference(field.xor_inputs[code].begin(),field.xor_inputs[code].end(),
					                              field.xor_inputs[0].begin(),field.xor_inputs[0].end(),
					                              std::back_inserter(signature[code-1]));
				}
				auto found = ids.find(signature);
				int group;
				if (found == ids.end()) {
					group = GetSize(groups);
					ids[signature] = group;
					groups.emplace_back();
					masks.emplace_back();
				} else {
					group = found->second;
				}
				groups[group].push_back(j);
				masks[group].set(j);
			}
			for (int group = 0; group < GetSize(groups); group++)
				for (int j : groups[group]) pairs[j] = masks[group];
		} else {
			dict<SigBit,std::bitset<128>> index;
			std::bitset<128> usable;
			for (int j = 0; j < GetSize(fields); j++) {
				bool valid = true;
				for (auto bit : fields[j].data) {
					if (--budget < 0) return false;
					if (!exchange_input(bit)) {
						valid = false;
						break;
					}
					index[bit].set(j);
				}
				fields[j].exchange_valid = valid;
				if (valid) {
					usable.set(j);
					eligible++;
				}
			}
			for (int j = 0; j < GetSize(fields); j++) if (fields[j].exchange_valid) {
				for (auto bit : fields[j].data) {
					if (--budget < 0) return false;
					pairs[j] |= index.at(bit);
				}
				pairs[j] &= usable;
			}
		}
		if (budget < 0) return false;
		log_debug("opt_pmuxrel relation_index fields=%d codes=%d eligible=%d xor_sources=%d ff_sources=%d budget=%d\n",
		          GetSize(fields), count, eligible, GetSize(xor_sources), GetSize(exchange_sources), budget);
		return true;
	}
	bool coarse(const std::vector<Table> &tables, Plan &plan) {
		std::vector<Field> fields;
		for (auto &table : tables) {
			const auto &y = netlist.port(table.cell, ID::Y);
			log_assert(GetSize(table.data) == (1 << GetSize(table.control)));
			for (auto &data : table.data) log_assert(GetSize(data) == GetSize(y));
			for (int j = 0; j < GetSize(y); j++) {
				Field field;
				field.y = y[j];
				for (auto &data : table.data)
					field.data.push_back(data[j]);
				fields.push_back(std::move(field));
			}
		}
		if (GetSize(fields) > 128) return false;
		std::vector<std::bitset<128>> pairs;
		if (!relation_pairs(fields,tables[0].control,pairs)) {
			log_debug("opt_pmuxrel budget exhausted during relation index\n");
			return false;
		}
		pool<int> used;
		int comparisons = 0;
		for (int j = 0; j < GetSize(fields); j++) if (!used.count(j)) for (int k = j+1; k < GetSize(fields); k++) if (!used.count(k)) {
			if (!pairs[j].test(k)) continue;
			if (--budget < 0) {
				log_debug("opt_pmuxrel budget exhausted during relation comparison\n");
				return false;
			}
			comparisons++;
			if (parity(fields[j],fields[k],tables[0].control,plan) || exchange(fields[j],fields[k],tables[0].control,plan)) {
				used.insert(j);
				used.insert(k);
				break;
			}
		}
		log_debug("opt_pmuxrel relation_pairs comparisons=%d targets=%d budget=%d\n",
		          comparisons, GetSize(plan.targets), budget);
		if (!plan.targets.empty()) {
			for (auto &table : tables) for (auto cell : table.region) plan.region.insert(cell);
			if (prepare_rewrite(plan) && profitable_relations(plan)) return true;
		}
		if (budget <= 0) return false;
		plan = Plan();
		bool accepted = simple_columns(tables,fields,plan);
		if (budget < 0) log_debug("opt_pmuxrel budget exhausted during simple columns\n");
		return accepted;
	}
	struct TableBits {
		dict<SigBit, std::vector<SigBit>> inputs;
		pool<SigBit> inverted;
		dict<SigBit, uint32_t> masks;
	};
	bool table_inputs(Cell *cell, int offset, const SigSpec &a, const SigSpec &y,
	                  std::vector<SigBit> &inputs, bool &inverted) {
		if (a.empty() || y.empty() || GetSize(a) > 128 || GetSize(y) > 128) return false;
		log_assert(offset >= 0 && offset < GetSize(y));
		auto parameter = [&](IdString name, int expected) {
			return cell->hasParam(name) && cell->getParam(name).is_fully_def() && cell->getParam(name).as_int() == expected;
		};
		bool mux = cell->type.in(ID($mux), ID($_MUX_));
		if (mux) {
			if (GetSize(cell->connections()) != 4 || !cell->hasPort(ID::B) || !cell->hasPort(ID::S)) return false;
			const auto &b = netlist.port(cell, ID::B), &s = netlist.port(cell, ID::S);
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
		    !cell->getParam(ID::A_SIGNED).is_fully_def() || GetSize(cell->getParam(ID::A_SIGNED)) < 1 ||
		    GetSize(cell->getParam(ID::A_SIGNED)) > 32) return false;
		int signed_value = cell->getParam(ID::A_SIGNED).as_int();
		if (signed_value != 0 && signed_value != 1) return false;
		inputs = {netlist.operand(cell, ID::A, offset)};
		inverted = cell->type == ID($not);
		return true;
	}
	bool table_inputs(Cell *cell, int offset, std::vector<SigBit> &inputs, bool &inverted) {
		if (!cell->hasPort(ID::A) || !cell->hasPort(ID::Y)) return false;
		return table_inputs(cell, offset, netlist.port(cell, ID::A), netlist.port(cell, ID::Y), inputs, inverted);
	}
	struct UnarySource {
		dict<SigBit,std::pair<SigBit,bool>> inputs;
		bool valid = false;
	};
	dict<Cell *,UnarySource> unary_sources;
	bool unary_input(Cell *cell, SigBit bit, SigBit &input, bool &inverted) {
		if (!cell->type.in(ID($not),ID($pos),ID($buf),ID($_NOT_),ID($_BUF_))) return false;
		auto found = unary_sources.find(cell);
		if (found == unary_sources.end()) {
			auto &source = unary_sources[cell];
			if (!cell->hasPort(ID::A) || !cell->hasPort(ID::Y)) return false;
			int a_width = GetSize(cell->getPort(ID::A)), y_width = GetSize(cell->getPort(ID::Y));
			if (a_width < 1 || a_width > 128 || y_width < 1 || y_width > 128) return false;
			if ((budget -= a_width + 2*y_width) < 0) return false;
			const auto &a = netlist.port(cell, ID::A), &y = netlist.port(cell, ID::Y);
			for (int j = 0; j < GetSize(y); j++) {
				std::vector<SigBit> inputs;
				bool step_inverted = false;
				if (!table_inputs(cell,j,a,y,inputs,step_inverted) || GetSize(inputs) != 1) return false;
				source.inputs[y[j]] = {inputs[0],step_inverted};
			}
			source.valid = true;
		}
		auto &source = unary_sources.at(cell);
		if (!source.valid || !source.inputs.count(bit)) return false;
		auto relation = source.inputs.at(bit);
		input = relation.first;
		inverted = relation.second;
		return true;
	}
	struct Literal {
		SigBit bit;
		bool inverted;
		bool operator<(const Literal &other) const {
			return bit < other.bit || (bit == other.bit && inverted < other.inverted);
		}
	};
	struct ColumnLiteral {
		Literal value;
		pool<Cell *> region;
	};
	bool normalize_literal(SigBit bit, ColumnLiteral &result) {
		bool inverted = false;
		for (int depth = 0; depth < 4; depth++) {
			if (--budget < 0) return false;
			auto cell = netlist.driver(bit);
			if (!cell) break;
			SigBit input;
			bool step_inverted = false;
			if (!unary_input(cell,bit,input,step_inverted)) {
				if (budget < 0) return false;
				break;
			}
			result.region.insert(cell);
			inverted ^= step_inverted;
			bit = input;
		}
		if (!bit.wire) {
			if (bit != State::S0 && bit != State::S1) return false;
			inverted ^= bit == State::S1;
			bit = State::S0;
		}
		result.value = {bit,inverted};
		return true;
	}
	struct ColumnNetwork {
		struct Unary { SigBit input; bool inverted; };
		dict<SigBit,Unary> unary;
		dict<SigBit,Cube> decoded;
	};
	bool column_network(const std::vector<Table> &tables, const Plan &plan, ColumnNetwork &network) {
		pool<Cell *> selectors;
		for (auto &table : tables) {
			selectors.insert(table.cell);
			const auto &s = netlist.port(table.cell, ID::S);
			log_assert(GetSize(s) == GetSize(table.cubes));
			for (int j = 0; j < GetSize(s); j++) network.decoded[s[j]] = table.cubes[j];
		}
		for (auto cell : plan.region) {
			if (selectors.count(cell)) continue;
			const auto &y = netlist.port(cell, ID::Y);
			if (cell->type.in(ID($eq),ID($logic_not))) {
				log_assert(GetSize(y) == 1 && network.decoded.count(y[0]));
				continue;
			}
			for (auto bit : y) {
				if (--budget < 0) return false;
				SigBit input;
				bool inverted = false;
				if (!netlist.unique(bit) || !unary_input(cell,bit,input,inverted)) return false;
				network.unary[bit] = {input,inverted};
			}
		}
		return true;
	}
	bool column_bit(SigBit bit, const ColumnNetwork &network, PmuxLutGraph &graph,
	                dict<SigBit,int> &roots, dict<SigBit,int> &state, int &root, int depth = 0) {
		if (--budget < 0 || depth > 96 || netlist.uncertain(bit)) return false;
		if (!bit.wire) {
			if (bit != State::S0 && bit != State::S1) return false;
			root = graph.leaf(bit);
			return true;
		}
		if (!netlist.unique(bit)) return false;
		if (state.count(bit)) {
			if (state.at(bit) != 2) return false;
			root = roots.at(bit);
			return true;
		}
		state[bit] = 1;
		auto unary = network.unary.find(bit);
		auto decoded = network.decoded.find(bit);
		if (unary != network.unary.end()) {
			if (!column_bit(unary->second.input,network,graph,roots,state,root,depth+1)) return false;
			if (unary->second.inverted) root = graph.gate({root},0x1);
		} else if (decoded != network.decoded.end()) {
			std::vector<int> inputs;
			int code = 0;
			for (auto &entry : decoded->second.bits) {
				int input;
				if (!column_bit(entry.first,network,graph,roots,state,input,depth+1)) return false;
				if (entry.second) code |= 1 << GetSize(inputs);
				inputs.push_back(input);
			}
			root = graph.lut(inputs,1U << code);
		} else {
			root = graph.leaf(bit);
		}
		roots[bit] = root;
		state[bit] = 2;
		return !graph.overflowed();
	}
	struct ColumnReference {
		PmuxLutGraph graph{PmuxLutGraph::Expansion::Subsets, 24000};
		std::vector<int> roots;
	};
	bool column_reference(const std::vector<Table> &tables, const ColumnNetwork &network,
	                      const std::vector<SigBit> &retained, bool full, ColumnReference &reference) {
		dict<SigBit,int> roots, state;
		auto &graph = reference.graph;
		if (full) for (auto &table : tables) {
			std::vector<int> control;
			for (auto bit : table.control) {
				int root;
				if (!column_bit(bit,network,graph,roots,state,root)) return false;
				control.push_back(root);
			}
			int width = GetSize(table.cell->getPort(ID::Y));
			for (int j = 0; j < width; j++) {
				std::vector<int> data;
				for (auto &branch : table.data) {
					int root;
					if (!column_bit(branch[j],network,graph,roots,state,root)) return false;
					data.push_back(root);
				}
				reference.roots.push_back(graph.select(data,control));
				if (graph.overflowed()) return false;
			}
		}
		for (auto bit : retained) {
			int root;
			if (!column_bit(bit,network,graph,roots,state,root)) return false;
			reference.roots.push_back(root);
		}
		return !graph.overflowed();
	}
	bool simple_columns(const std::vector<Table> &tables, const std::vector<Field> &fields, Plan &plan) {
		dict<SigBit,ColumnLiteral> literals;
		std::map<std::vector<Literal>,std::vector<int>> groups;
		std::vector<bool> inverted(fields.size());
		for (int j = 0; j < GetSize(fields); j++) {
			std::vector<Literal> column, complement;
			for (auto bit : fields[j].data) {
				if (--budget < 0) return false;
				auto found = literals.find(bit);
				if (found == literals.end()) {
					ColumnLiteral literal;
					if (!normalize_literal(bit,literal)) return false;
					literals[bit] = std::move(literal);
				}
				auto literal = literals.at(bit).value;
				column.push_back(literal);
				literal.inverted = !literal.inverted;
				complement.push_back(literal);
			}
			inverted[j] = complement < column;
			groups[inverted[j] ? complement : column].push_back(j);
		}
		for (auto &entry : groups) if (GetSize(entry.second) >= 2) plan.shared_columns += GetSize(entry.second);
		if (!plan.shared_columns) return false;
		plan.columns = true;
		for (auto &table : tables) for (auto cell : table.region) plan.region.insert(cell);
		for (auto &entry : literals) for (auto cell : entry.second.region) plan.region.insert(cell);
		std::vector<int> control, output(fields.size(),-1);
		for (auto bit : tables[0].control) control.push_back(plan.graph.leaf(bit));
		for (auto &entry : groups) {
			std::vector<int> data;
			for (auto literal : entry.first) {
				int root = plan.graph.leaf(literal.bit);
				if (literal.inverted) root = plan.graph.gate({root},0x1);
				data.push_back(root);
			}
			int root = plan.graph.select(data,control);
			for (int j : entry.second) {
				log_assert(output[j] == -1);
				output[j] = inverted[j] ? plan.graph.gate({root},0x1) : root;
			}
			if (plan.graph.overflowed()) return false;
		}
		for (int j = 0; j < GetSize(fields); j++) {
			log_assert(output[j] >= 0);
			plan.targets.append(fields[j].y);
			plan.roots.push_back(output[j]);
		}
		log_assert(GetSize(plan.targets) == GetSize(fields));
		if (!prepare_rewrite(plan)) return false;
		for (auto &table : tables) log_assert(plan.remove.count(table.cell));
		auto leaves = plan.graph.referenced(plan.roots);
		pool<SigBit> retained;
		for (auto cell : plan.region) if (!plan.remove.count(cell)) {
			bool fixed = cell->get_bool_attribute(ID::keep) || !netlist.selected(cell);
			for (auto &port : cell->connections()) if (netlist.cell_output(cell->type,port.first))
				for (auto bit : netlist.port(cell, port.first)) {
					bool needed = fixed || leaves.count(bit) || netlist.protected_bit(bit) || netlist.uncertain(bit);
					for (const auto &user : netlist.users(bit)) if (!plan.remove.count(user.cell)) needed = true;
					if (needed) retained.insert(bit);
				}
		}
		std::vector<SigBit> retained_roots(retained.begin(),retained.end());
		std::sort(retained_roots.begin(),retained_roots.end());
		ColumnNetwork network;
		if (!column_network(tables,plan,network)) return false;
		ColumnReference original, preserved;
		if (!column_reference(tables,network,retained_roots,true,original) ||
		    !column_reference(tables,network,retained_roots,false,preserved)) return false;
		log_assert(GetSize(original.roots) == GetSize(plan.targets) + GetSize(retained_roots));
		log_assert(GetSize(preserved.roots) == GetSize(retained_roots));
		plan.reference = original.graph.cost(original.roots);
		plan.retained_reference = preserved.graph.cost(preserved.roots);
		int cost = plan.graph.cost(plan.roots);
		log_debug("opt_pmuxrel column_cost outputs=%d shared=%d ordinary=%d original=%d retained=%d candidate=%d removable=%d budget=%d\n",
		          GetSize(plan.targets), plan.shared_columns, GetSize(plan.targets)-plan.shared_columns, plan.reference,
		          plan.retained_reference, cost, GetSize(plan.remove), budget);
		return cost + plan.retained_reference < plan.reference;
	}
	bool cone(SigBit bit, pool<SigBit> &leaves, pool<Cell *> &region, dict<SigBit,int> &state, TableBits &bits, int depth = 0) {
		if (--budget < 0 || depth > 32 || GetSize(region) > 128 || netlist.uncertain(bit) || netlist.kept(bit)) return false;
		if (!bit.wire) return bit == State::S0 || bit == State::S1;
		auto source = netlist.source(bit);
		if (!source) return false;
		if (state.count(bit)) return state.at(bit) == 2;
		auto cell = source->cell;
		if (!cell) {
			leaves.insert(bit);
			return GetSize(leaves) <= 5;
		}
		if (!netlist.editable(cell) || source->port != ID::Y) return false;
		std::vector<SigBit> inputs;
		bool inverted = false;
		if (!table_inputs(cell,source->offset,inputs,inverted)) return false;
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
		pool<SigBit> endpoints = netlist.protected_bits();
		for (auto cell : module->cells()) if (StaticCellTypes::categories.is_ff(cell->type) && cell->hasPort(ID::D))
			for (auto bit : netlist.port(cell, ID::D)) endpoints.insert(bit);
		int candidates = 0;
		for (auto cell : module->selected_cells()) {
			if (budget <= 0 || candidates >= 32) break;
			if (cell->type != ID($mux) || !netlist.editable(cell)) continue;
			const auto &y = netlist.port(cell, ID::Y);
			if (GetSize(y) < 2 || GetSize(y) > 128) continue;
			std::vector<SigBit> root_inputs;
			bool root_inverted = false;
			if (!table_inputs(cell,0,root_inputs,root_inverted)) continue;
			bool visible = true;
			for (auto bit : y) if (!endpoints.count(bit)) visible = false;
			if (!visible) continue;
			const auto &s = netlist.port(cell, ID::S);
			if (GetSize(s) != 1) continue;
			auto enable_source = netlist.source(s[0]);
			if (!enable_source || enable_source->cell || netlist.kept(s[0])) continue;
			const auto &a = netlist.port(cell, ID::A), &b = netlist.port(cell, ID::B);
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
					int root = plan.graph.lut({left,right,args[split],enable},active_high ? 0xca00 : 0x00ca);
					int cost = plan.graph.incremental_cost({root}, shared);
					if (cost < bestcost) {
						best = root;
						bestcost = cost;
					}
				}
				log_assert(best >= 0);
				plan.targets.append(y[j]);
				plan.roots.push_back(best);
			}
			if (plan.graph.overflowed()) return false;
			plan.region.insert(cell);
			for (auto source : region)
				plan.region.insert(source);
		}
		if (!prepare_rewrite(plan)) return false;
		int removable_cost = 0;
		for (auto cell : plan.remove)
			removable_cost += cell_cost(cell);
		// 多输出单元的保留位不会贡献可删除成本。
		return plan.graph.cost(plan.roots) < removable_cost;
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
			std::vector<RelationWorker::Plan> plans;
			if (tables) {
				RelationWorker::Plan plan;
				if (worker.tables(plan)) plans.push_back(std::move(plan));
			} else {
				dict<SigSpec,std::vector<RelationWorker::Table>> groups;
				for (auto cell : module->selected_cells()) {
					if (worker.budget <= 0) break;
					RelationWorker::Table table;
					if (worker.table(cell,table)) groups[table.control].push_back(std::move(table));
				}
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
			}
			worker.commit(plans);
		}
	}
} OptPmuxRelPass;

PRIVATE_NAMESPACE_END
