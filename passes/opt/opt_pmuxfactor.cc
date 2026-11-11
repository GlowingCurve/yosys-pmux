// opt_pmuxfactor 提取 PMUX 分支的公共运算并前移归约运算；复用分支表达式与端口映射，减少选择逻辑和重复运算。
#include "kernel/yosys.h"
#include "kernel/utils.h"
#include "passes/opt/pmux_lut_cost.h"
#include "passes/opt/pmux_netlist.h"
#include <deque>
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxFactorWorker {
	using OpBit = std::pair<Cell *, int>;
	using Signature = std::tuple<IdString, SigSpec>;
	Module *module;
	PmuxNetlist netlist;
	PmuxLutCost::ModuleCost module_cost;
	dict<Cell *, bool> pmux_readable;
	dict<Cell *, bool> supported_cells;
	dict<OpBit, SigSpec> expression_cache;
	dict<Signature, std::vector<SigBit>> operators;
	bool operators_built = false;
	int changes = 0;
	int analysis_work = 1048576, cost_work = 1048576;

	struct Plan {
		enum Kind { Existing, Selector, Operation } kind;
		int id;
		int selector = -1; // 唯一 Selector 的编号，-1 表示没有 Selector。
		SigBit result;
		SigSpec values, select;
		IdString type;
		std::vector<const Plan *> args;
	};
	using PlanPtr = const Plan *;
	using PlanKey = std::tuple<IdString, SigSpec, SigSpec, std::vector<int>>;
	dict<PlanKey, PlanPtr> plans;
	// 节点仅追加，Plan 引用在整个 Worker 生命周期内保持有效。
	std::deque<Plan> plan_nodes;
	struct Edit {
		Cell *cell;
		SigSpec a, b, y;
	};
	struct Choice {
		SigSpec select;
		dict<SigSpec, std::vector<SigBit>> exact, undefined_default;
	};
	dict<SigSpec, Choice> choices;
	struct Candidate {
		Cell *cell;
		SigSpec a, b, s, y;
		std::vector<PlanPtr> outputs;
		pool<OpBit> sources;
		pool<int> dependencies;
		bool valid = true;
	};
	struct Estimate {
		bool valid = false;
		int removed = 0, added = 0, retained = 0;
		pool<OpBit> erased;
	};

	PmuxFactorWorker(Module *module, Design *design) : module(module), netlist(module, design), module_cost(netlist) {}

	bool check_supported(Cell *cell)
	{
		if (!cell->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($mux)) || netlist.uncertain_cell(cell)) return false;
		if (!cell->hasPort(ID::A) || !cell->hasPort(ID::B) || !cell->hasPort(ID::Y)) return false;
		int width = GetSize(cell->getPort(ID::Y));
		if (cell->type == ID($mux))
			return cell->hasPort(ID::S) && GetSize(cell->getPort(ID::S)) == 1 && GetSize(cell->getPort(ID::A)) == width &&
				GetSize(cell->getPort(ID::B)) == width && cell->hasParam(ID::WIDTH) && cell->getParam(ID::WIDTH).as_int() == width;
		return cell->hasParam(ID::A_WIDTH) && cell->hasParam(ID::B_WIDTH) && cell->hasParam(ID::Y_WIDTH) &&
			cell->hasParam(ID::A_SIGNED) && cell->hasParam(ID::B_SIGNED) &&
			cell->getParam(ID::A_WIDTH).as_int() == GetSize(cell->getPort(ID::A)) &&
			cell->getParam(ID::B_WIDTH).as_int() == GetSize(cell->getPort(ID::B)) && cell->getParam(ID::Y_WIDTH).as_int() == width;
	}

	bool supported(Cell *cell)
	{
		auto found = supported_cells.find(cell);
		if (found != supported_cells.end()) return found->second;
		bool valid = check_supported(cell);
		supported_cells[cell] = valid;
		return valid;
	}

	void ensure_operators()
	{
		if (operators_built) return;
		log_assert(operators.empty());
		for (auto cell : module->cells()) if (supported(cell)) {
			const auto &y = netlist.port(cell, ID::Y);
			for (int i = 0; i < GetSize(y); i++) {
				auto source = netlist.source(y[i]);
				if (source && source->cell == cell && source->port == ID::Y && source->offset == i)
					operators[signature(cell->type, expression_inputs(cell, i))].push_back(y[i]);
			}
		}
		operators_built = true;
	}

	const SigSpec &expression_inputs(Cell *cell, int offset)
	{
		auto source = OpBit(cell, offset);
		auto found = expression_cache.find(source);
		if (found != expression_cache.end()) return found->second;
		log_assert(supported(cell) && offset >= 0 && offset < GetSize(cell->getPort(ID::Y)));
		SigSpec result;
		if (cell->type == ID($mux)) {
			result.append(netlist.port(cell, ID::A)[offset]);
			result.append(netlist.port(cell, ID::B)[offset]);
			result.append(netlist.port(cell, ID::S));
		} else {
			result.append(netlist.operand(cell, ID::A, offset));
			result.append(netlist.operand(cell, ID::B, offset));
		}
		expression_cache[source] = result;
		return expression_cache.at(source);
	}

	Signature signature(IdString type, SigSpec inputs)
	{
		if (type != ID($mux)) inputs.sort();
		return {type, inputs};
	}

	bool expression(SigBit bit, IdString &type, SigBit &a, SigBit &b)
	{
		auto source = netlist.source(bit);
		if (!source || !source->cell || source->port != ID::Y || !supported(source->cell)) return false;
		auto inputs = expression_inputs(source->cell, source->offset);
		type = source->cell->type;
		a = inputs[0];
		b = inputs[1];
		return true;
	}

	bool check_pmux_shape(Cell *cell)
	{
		if (cell->type != ID($pmux) || netlist.uncertain_cell(cell) || !cell->hasPort(ID::A) || !cell->hasPort(ID::B) ||
			!cell->hasPort(ID::S) || !cell->hasPort(ID::Y) || !cell->hasParam(ID::WIDTH) || !cell->hasParam(ID::S_WIDTH)) return false;
		const auto &a = netlist.port(cell, ID::A), &b = netlist.port(cell, ID::B), &s = netlist.port(cell, ID::S), &y = netlist.port(cell, ID::Y);
		if (GetSize(a) != GetSize(y) || GetSize(b) != int64_t(GetSize(y))*GetSize(s) ||
			cell->getParam(ID::WIDTH).as_int() != GetSize(y) || cell->getParam(ID::S_WIDTH).as_int() != GetSize(s)) return false;
		for (int i = 0; i < GetSize(y); i++) {
			auto source = netlist.source(y[i]);
			if (!source || source->cell != cell || source->port != ID::Y || source->offset != i) return false;
		}
		return true;
	}

	bool readable_pmux(Cell *cell)
	{
		auto found = pmux_readable.find(cell);
		if (found != pmux_readable.end()) return found->second;
		bool valid = check_pmux_shape(cell);
		pmux_readable[cell] = valid;
		return valid;
	}

	bool independent(SigBit bit, SigBit target)
	{
		int budget = std::min(512, analysis_work), initial = budget;
		PmuxNetlist::Dependencies dependency(netlist, {target}, budget);
		bool valid = dependency.visit(bit);
		analysis_work -= initial - budget;
		return valid;
	}

	PlanPtr make_plan(Plan::Kind kind, IdString type, SigSpec values, SigSpec select, std::vector<PlanPtr> args)
	{
		std::vector<int> ids;
		for (auto arg : args) {
			log_assert(arg != nullptr);
			ids.push_back(arg->id);
		}
		if (kind == Plan::Operation && type != ID($mux) && ids[1] < ids[0]) {
			std::swap(ids[0], ids[1]);
			std::swap(args[0], args[1]);
		}
		auto key = std::make_tuple(type, values, select, ids);
		auto found = plans.find(key);
		if (found != plans.end()) {
			log_assert(found->second->kind == kind);
			return found->second;
		}
		if (GetSize(plan_nodes) >= 65536) return nullptr;
		plan_nodes.emplace_back();
		auto plan = &plan_nodes.back();
		plan->kind = kind;
		plan->id = GetSize(plan_nodes)-1;
		plan->type = type;
		plan->values = values;
		plan->select = select;
		plan->args = std::move(args);
		if (kind == Plan::Selector) plan->selector = plan->id;
		else for (auto arg : plan->args) if (arg->selector >= 0) plan->selector = arg->selector;
		if (kind == Plan::Existing) {
			log_assert(GetSize(values) == 1);
			plan->result = values[0];
		}
		plans[key] = plan;
		return plan;
	}

	PlanPtr direct(SigBit bit)
	{
		return make_plan(Plan::Existing, IdString(), SigSpec(bit), SigSpec(), {});
	}

	void collect_plans(PlanPtr plan, pool<int> &nodes, pool<SigBit> &roots)
	{
		log_assert(plan != nullptr);
		if (!nodes.insert(plan->id).second) return;
		if (plan->kind == Plan::Existing) roots.insert(plan->result);
		else if (plan->kind == Plan::Selector) {
			log_assert(plan->args.empty() && GetSize(plan->values) == GetSize(plan->select)+1);
			for (auto bit : plan->values) roots.insert(bit);
			for (auto bit : plan->select) roots.insert(bit);
		} else {
			log_assert(plan->kind == Plan::Operation && GetSize(plan->args) == (plan->type == ID($mux) ? 3 : 2));
			for (auto arg : plan->args) collect_plans(arg, nodes, roots);
		}
	}

	PlanPtr operation(IdString type, std::vector<PlanPtr> args, SigBit avoid)
	{
		SigSpec inputs;
		bool existing = true;
		for (auto arg : args) {
			log_assert(arg != nullptr);
			if (arg->kind != Plan::Existing) existing = false;
			else inputs.append(arg->result);
		}
		if (existing) {
			ensure_operators();
			auto found = operators.find(signature(type, inputs));
			if (found != operators.end()) for (auto result : found->second)
				if (independent(result, avoid)) return direct(result);
		}
		int selector = -1;
		for (auto arg : args) if (arg->selector >= 0) {
			if (selector >= 0 && selector != arg->selector) return nullptr;
			selector = arg->selector;
		}
		return make_plan(Plan::Operation, type, SigSpec(), SigSpec(), std::move(args));
	}

	PlanPtr lookup(Choice &choice, const SigSpec &values, SigBit avoid)
	{
		log_assert(GetSize(values) == GetSize(choice.select)+1);
		auto exact = choice.exact.find(values);
		if (exact != choice.exact.end()) for (auto result : exact->second) if (independent(result, avoid)) return direct(result);
		if (values[0] == State::Sx) {
			auto found = choice.undefined_default.find(values.extract(1, GetSize(values)-1));
			if (found != choice.undefined_default.end()) for (auto result : found->second)
				if (independent(result, avoid)) return direct(result);
		}
		SigBit same = values[0] == State::Sx ? values[1] : values[0];
		for (auto bit : values) if (bit != same && bit != State::Sx) return nullptr;
		return independent(same, avoid) ? direct(same) : nullptr;
	}

	PlanPtr lift(Choice &choice, const SigSpec &values, SigBit avoid, int depth, pool<OpBit> &sources, bool root = false)
	{
		if (--analysis_work < 0) return nullptr;
		if (!root) {
			auto existing = lookup(choice, values, avoid);
			if (existing) return existing;
		}
		if (depth > 0) {
			IdString common;
			SigSpec aa, bb, ss;
			bool match = true;
			SigBit first_a, first_b;
			for (int i = 0; i < GetSize(values); i++) {
				if (--analysis_work < 0) return nullptr;
				if (i == 0 && values[i] == State::Sx) {
					aa.append(State::Sx);
					bb.append(State::Sx);
					ss.append(State::Sx);
					continue;
				}
				IdString type;
				SigBit a, b;
				if (!expression(values[i], type, a, b) || (!common.empty() && type != common)) {
					match = false;
					break;
				}
				auto source = netlist.source(values[i]);
				log_assert(source && source->cell && source->port == ID::Y);
				sources.insert({source->cell, source->offset});
				if (common.empty()) {
					common = type;
					first_a = a;
					first_b = b;
				}
				if (type != ID($mux) && a == first_b && b != first_b) std::swap(a, b);
				aa.append(a);
				bb.append(b);
				if (type == ID($mux)) ss.append(netlist.port(source->cell, ID::S));
			}
			if (match && !common.empty()) {
				if (common == ID($mux)) {
					auto pa = lookup(choice, aa, avoid), pb = lookup(choice, bb, avoid);
					bool defined = (first_a.wire || first_a == State::S0 || first_a == State::S1) &&
						(first_b.wire || first_b == State::S0 || first_b == State::S1);
					if (defined && pa && pb && pa->kind == Plan::Existing && pb->kind == Plan::Existing && pa->result == first_a && pb->result == first_b) {
						auto select = lift(choice, ss, avoid, depth-1, sources);
						if (select) return operation(common, {pa, pb, select}, avoid);
					}
				} else {
					auto a = lift(choice, aa, avoid, depth-1, sources), b = lift(choice, bb, avoid, depth-1, sources);
					if (a && b) {
						auto result = operation(common, {a, b}, avoid);
						if (result) return result;
					}
				}
			}
		}
		if (root) return nullptr;
		return make_plan(Plan::Selector, ID($pmux), values, choice.select, {});
	}

	SigBit materialize(PlanPtr plan, dict<int, SigBit> &emitted)
	{
		log_assert(plan != nullptr);
		auto found = emitted.find(plan->id);
		if (found != emitted.end()) return found->second;
		if (plan->kind == Plan::Existing) return plan->result;
		auto output = module->addWire(NEW_ID);
		if (plan->kind == Plan::Selector) {
			log_assert(GetSize(plan->values) == GetSize(plan->select)+1);
			module->addPmux(NEW_ID, plan->values[0], plan->values.extract(1, GetSize(plan->select)), plan->select, output);
		} else {
			log_assert(plan->kind == Plan::Operation && GetSize(plan->args) == (plan->type == ID($mux) ? 3 : 2));
			auto a = materialize(plan->args[0], emitted), b = materialize(plan->args[1], emitted);
			if (plan->type == ID($mux)) module->addMux(NEW_ID, a, b, materialize(plan->args[2], emitted), output);
			else {
				auto cell = module->addCell(NEW_ID, plan->type);
				cell->setParam(ID::A_WIDTH, 1);
				cell->setParam(ID::B_WIDTH, 1);
				cell->setParam(ID::Y_WIDTH, 1);
				cell->setParam(ID::A_SIGNED, false);
				cell->setParam(ID::B_SIGNED, false);
				cell->setPort(ID::A, a);
				cell->setPort(ID::B, b);
				cell->setPort(ID::Y, output);
			}
		}
		emitted[plan->id] = SigBit(output);
		return SigBit(output);
	}

	void xor_terms(SigBit bit, pool<SigBit> &terms, int depth)
	{
		IdString type;
		SigBit a, b;
		if (depth && expression(bit, type, a, b) && type == ID($xor)) {
			xor_terms(a, terms, depth-1);
			xor_terms(b, terms, depth-1);
		} else if (bit != State::S0) {
			if (terms.count(bit)) terms.erase(bit); else terms.insert(bit);
		}
	}

	void simplify_xors()
	{
		std::vector<Cell *> removed;
		std::vector<Edit> edits;
		for (auto cell : module->cells().to_vector()) {
			if (cell->type != ID($xor) || !netlist.editable(cell)) continue;
			const auto &y = netlist.port(cell, ID::Y);
			SigSpec a, b, remaining;
			for (int i = 0; i < GetSize(y); i++) {
				pool<SigBit> terms;
				xor_terms(netlist.operand(cell, ID::A, i), terms, 3);
				xor_terms(netlist.operand(cell, ID::B, i), terms, 3);
				if (GetSize(terms) <= 1) {
					module->connect(y[i], terms.empty() ? SigBit(State::S0) : *terms.begin());
					changes++;
				} else {
					a.append(netlist.operand(cell, ID::A, i));
					b.append(netlist.operand(cell, ID::B, i));
					remaining.append(y[i]);
				}
			}
			if (GetSize(remaining) == GetSize(y)) continue;
			if (remaining.empty()) removed.push_back(cell);
			else edits.push_back({cell, a, b, remaining});
		}
		for (auto &edit : edits) {
			edit.cell->setPort(ID::A, edit.a);
			edit.cell->setPort(ID::B, edit.b);
			edit.cell->setPort(ID::Y, edit.y);
			edit.cell->setParam(ID::A_WIDTH, GetSize(edit.a));
			edit.cell->setParam(ID::B_WIDTH, GetSize(edit.b));
			edit.cell->setParam(ID::Y_WIDTH, GetSize(edit.y));
			edit.cell->setParam(ID::A_SIGNED, false);
			edit.cell->setParam(ID::B_SIGNED, false);
		}
		for (auto cell : removed) module->remove(cell);
	}

	SigSpec branch_values(const Candidate &candidate, int offset)
	{
		log_assert(offset >= 0 && offset < GetSize(candidate.y));
		SigSpec values(candidate.a[offset]);
		for (int i = 0; i < GetSize(candidate.s); i++) values.append(candidate.b[i*GetSize(candidate.y)+offset]);
		return values;
	}

	std::vector<SigBit> check_candidates(std::vector<Candidate> &candidates)
	{
		dict<SigBit, int> owners, degree;
		dict<SigBit, std::vector<SigBit>> consumers;
		pool<SigBit> stops;
		for (int i = 0; i < GetSize(candidates); i++) for (int j = 0; j < GetSize(candidates[i].y); j++)
			if (candidates[i].outputs[j]) {
				stops.insert(candidates[i].y[j]);
				owners[candidates[i].y[j]] = i;
			}
		for (auto &candidate : candidates) {
			for (int j = 0; j < GetSize(candidate.y); j++) if (candidate.outputs[j]) {
				pool<int> plan_ids;
				pool<SigBit> inputs, references;
				collect_plans(candidate.outputs[j], plan_ids, inputs);
				SigSpec original;
				if (!netlist.combinational_inputs(candidate.y[j], original)) candidate.valid = false;
				for (auto bit : original) inputs.insert(bit);
				int budget = std::min(512, analysis_work), initial = budget;
				PmuxNetlist::Dependencies dependency(netlist, stops, budget, false, &references);
				for (auto bit : inputs) if (!dependency.visit(bit)) candidate.valid = false;
				analysis_work -= initial - budget;
				degree[candidate.y[j]] = GetSize(references);
				for (auto reference : references) {
					consumers[reference].push_back(candidate.y[j]);
					candidate.dependencies.insert(owners.at(reference));
				}
			}
		}
		std::vector<SigBit> order;
		for (auto &entry : degree) if (!entry.second && candidates[owners.at(entry.first)].valid) order.push_back(entry.first);
		for (int i = 0; i < GetSize(order); i++) if (consumers.count(order[i])) for (auto user : consumers.at(order[i])) {
			log_assert(degree.at(user) > 0);
			if (--degree.at(user) == 0 && candidates[owners.at(user)].valid) order.push_back(user);
		}
		pool<SigBit> ordered;
		for (auto bit : order) ordered.insert(bit);
		for (auto bit : stops) if (!ordered.count(bit)) candidates[owners.at(bit)].valid = false;
		return order;
	}

	bool add_region(SigBit bit, pool<OpBit> &region)
	{
		std::vector<SigBit> pending = {bit};
		for (int i = 0; i < GetSize(pending); i++) {
			IdString type;
			SigBit a, b;
			if (!expression(pending[i], type, a, b)) continue;
			auto driver = netlist.source(pending[i]);
			log_assert(driver && driver->cell && driver->port == ID::Y);
			OpBit source(driver->cell, driver->offset);
			if (!region.insert(source).second) continue;
			if (--cost_work < 0 || GetSize(region) > 65536) return false;
			for (auto input : expression_inputs(source.first, source.second)) pending.push_back(input);
		}
		return true;
	}

	bool retained(const pool<OpBit> &region, const dict<Cell *, pool<int>> &rewritten, const pool<SigBit> &plan_roots,
		pool<OpBit> &kept, pool<SigBit> &external_roots)
	{
		pool<Cell *> source_cells;
		dict<SigBit, OpBit> source_bits;
		for (auto source : region) {
			if (--cost_work < 0) return false;
			auto bit = netlist.port(source.first, ID::Y)[source.second];
			source_cells.insert(source.first);
			source_bits[bit] = source;
			if (netlist.protected_bit(bit) || !netlist.editable_bit(source.first, ID::Y, source.second)) external_roots.insert(bit);
		}
		for (auto source : region) {
			auto bit = netlist.port(source.first, ID::Y)[source.second];
			for (const auto &user : netlist.users(bit)) {
				if (--cost_work < 0) return false;
				if (!source_cells.count(user.cell) && !rewritten.count(user.cell)) external_roots.insert(bit);
			}
		}
		for (auto cell : source_cells) {
			const auto &y = netlist.port(cell, ID::Y);
			for (int i = 0; i < GetSize(y); i++) if (!region.count({cell, i}))
				for (auto bit : expression_inputs(cell, i)) {
					if (--cost_work < 0) return false;
					if (source_bits.count(bit)) external_roots.insert(bit);
				}
		}
		for (auto &entry : rewritten) {
			auto cell = entry.first;
			const auto &a = netlist.port(cell, ID::A), &b = netlist.port(cell, ID::B), &s = netlist.port(cell, ID::S), &y = netlist.port(cell, ID::Y);
			if (GetSize(entry.second) == GetSize(y)) continue;
			for (auto bit : s) if (source_bits.count(bit)) external_roots.insert(bit);
			for (int j = 0; j < GetSize(y); j++) if (!entry.second.count(j)) {
				if (source_bits.count(a[j])) external_roots.insert(a[j]);
				for (int i = 0; i < GetSize(s); i++) {
					if (--cost_work < 0) return false;
					auto bit = b[i*GetSize(y)+j];
					if (source_bits.count(bit)) external_roots.insert(bit);
				}
			}
		}
		std::vector<OpBit> pending;
		for (auto bit : external_roots) if (source_bits.count(bit)) pending.push_back(source_bits.at(bit));
		for (auto bit : plan_roots) if (source_bits.count(bit)) pending.push_back(source_bits.at(bit));
		for (int i = 0; i < GetSize(pending); i++) {
			auto source = pending[i];
			if (!kept.insert(source).second) continue;
			if (--cost_work < 0) return false;
			for (auto bit : expression_inputs(source.first, source.second)) if (source_bits.count(bit)) pending.push_back(source_bits.at(bit));
		}
		return true;
	}

	static uint16_t operation_table(IdString type)
	{
		if (type == ID($mux)) return 0xca;
		if (type == ID($and)) return 8;
		if (type == ID($or)) return 14;
		if (type == ID($xor)) return 6;
		log_assert(type == ID($xnor));
		return 9;
	}

	using PlanCost = dict<std::pair<int, int>, PmuxLutCost::Signal>;
	PmuxLutCost::Signal cost_plan(PlanPtr node, PmuxLutCost::Builder &builder, int depth, PlanCost &memo)
	{
		log_assert(node);
		if (depth <= 0) return builder.fail(PmuxLutCost::CostStatus::DepthLimit);
		if (!builder.spend()) return builder.fail(PmuxLutCost::CostStatus::BudgetExhausted);
		auto key = std::make_pair(node->id, depth);
		auto cached = memo.find(key);
		if (cached != memo.end()) return cached->second;
		PmuxLutCost::Signal result;
		if (node->kind == Plan::Existing) result = builder.bit(node->result, depth);
		else if (node->kind == Plan::Selector) {
			log_assert(GetSize(node->values) == GetSize(node->select) + 1);
			auto fallback = builder.bit(node->values[0], depth - 1);
			std::vector<PmuxLutCost::Signal> data, controls;
			for (int i = 0; i < GetSize(node->select); i++) {
				data.push_back(builder.bit(node->values[i + 1], depth - 1));
				controls.push_back(builder.bit(node->select[i], depth - 1));
			}
			result = builder.pmux(fallback, data, controls);
		} else {
			std::vector<PmuxLutCost::Signal> args;
			for (auto arg : node->args) args.push_back(cost_plan(arg, builder, depth - 1, memo));
			result = builder.operation(operation_table(node->type), args);
		}
		return memo[key] = result;
	}

	Estimate estimate(const std::vector<Candidate> &candidates, const std::vector<int> &accepted, const pool<SigBit> &extra_roots)
	{
		Estimate result;
		PmuxLutCost::Request request;
		PlanCost memo;
		pool<OpBit> region, after_kept;
		pool<int> nodes;
		pool<SigBit> roots;
		dict<Cell *, pool<int>> rewritten;
		for (int index : accepted) {
			const auto &candidate = candidates[index];
			for (auto source : candidate.sources)
				if (!add_region(netlist.port(source.first, ID::Y)[source.second], region)) return result;
			for (int j = 0; j < GetSize(candidate.y); j++) if (auto plan = candidate.outputs[j]) {
				collect_plans(plan, nodes, roots);
				rewritten[candidate.cell].insert(j);
				request.replacements[candidate.y[j]] = [this, plan, &memo](PmuxLutCost::Builder &builder, int depth) {
					return cost_plan(plan, builder, depth, memo);
				};
			}
		}
		for (auto bit : roots) if (!add_region(bit, region)) return result;
		for (auto source : region) {
			if (--cost_work < 0) return result;
			auto bit = netlist.port(source.first, ID::Y)[source.second];
			if (extra_roots.count(bit) && !roots.count(bit)) request.roots.insert(bit);
		}
		if (!retained(region, rewritten, roots, after_kept, request.roots)) return result;
		for (auto source : region) if (!after_kept.count(source)) {
			log_assert(netlist.editable_bit(source.first, ID::Y, source.second));
			result.erased.insert(source);
			request.removed.insert(netlist.port(source.first, ID::Y)[source.second]);
		}
		auto cost = module_cost.estimate(request, cost_work);
		result.valid = cost.status == PmuxLutCost::CostStatus::Profitable || cost.status == PmuxLutCost::CostStatus::NoGain;
		result.removed = cost.removed;
		result.added = cost.added;
		result.retained = cost.retained;
		return result;
	}

	bool collect_sources(const pool<SigBit> &roots, const pool<SigBit> &stops, pool<SigBit> &sources)
	{
		std::vector<SigBit> pending(roots.begin(), roots.end());
		pool<SigBit> seen;
		for (int i = 0; i < GetSize(pending); i++) {
			if (--cost_work < 0) return false;
			auto bit = pending[i];
			if (!bit.wire || stops.count(bit) || !seen.insert(bit).second) continue;
			auto source = netlist.source(bit);
			if (!source || !source->cell || !netlist.editable_bit(source->cell, source->port, source->offset)) continue;
			SigSpec inputs;
			if (!module_cost.modeled_inputs(bit, inputs, cost_work)) {
				if (cost_work < 0) return false;
				continue;
			}
			if (sources.insert(bit).second && GetSize(sources) > 65536) return false;
			for (auto input : inputs) {
				if (--cost_work < 0) return false;
				pending.push_back(input);
			}
		}
		return true;
	}

	std::vector<std::vector<int>> related_candidates(const std::vector<Candidate> &candidates, int accepted_count)
	{
		if (GetSize(candidates) < 2) return {};
		int valid_count = 0;
		for (const auto &candidate : candidates) {
			if (--cost_work < 0) return {};
			if (candidate.valid) valid_count++;
		}
		if (valid_count < 2 || valid_count == accepted_count) return {};
		struct Ownership {
			std::vector<int> readers;
			bool retained = false;
		};
		std::vector<int> parent(GetSize(candidates)), sizes(GetSize(candidates), 1);
		for (int i = 0; i < GetSize(parent); i++) {
			if (--cost_work < 0) return {};
			parent[i] = i;
		}
		int components = valid_count;
		auto find = [&](int index) {
			while (parent[index] != index) {
				parent[index] = parent[parent[index]];
				index = parent[index];
			}
			return index;
		};
		auto join = [&](int a, int b) {
			a = find(a);
			b = find(b);
			if (a == b) return;
			if (sizes[a] < sizes[b] || (sizes[a] == sizes[b] && a > b)) std::swap(a, b);
			parent[b] = a;
			sizes[a] += sizes[b];
			components--;
		};
		dict<SigBit, Ownership> ownership;
		dict<int, int> plan_owner;
		pool<SigBit> modeled, replaced;
		for (int i = 0; i < GetSize(candidates); i++) {
			const auto &candidate = candidates[i];
			if (!candidate.valid) continue;
			pool<int> nodes;
			pool<SigBit> roots, outputs;
			for (int j = 0; j < GetSize(candidate.y); j++) {
				if (--cost_work < 0) return {};
				if (candidate.outputs[j]) {
					collect_plans(candidate.outputs[j], nodes, roots);
					outputs.insert(candidate.y[j]);
				}
			}
			for (int dependency : candidate.dependencies) {
				if (--cost_work < 0) return {};
				if (candidates[dependency].valid) join(i, dependency);
			}
			for (int id : nodes) {
				const auto *plan = &plan_nodes[id];
				cost_work -= 1 + GetSize(plan->args) + GetSize(plan->values) + GetSize(plan->select);
				if (cost_work < 0) return {};
				if (plan->kind == Plan::Existing) continue;
				auto found = plan_owner.find(id);
				if (found == plan_owner.end()) plan_owner[id] = i;
				else join(i, found->second);
			}
			pool<SigBit> before, after;
			if (!collect_sources(outputs, {}, before) || !collect_sources(roots, outputs, after)) return {};
			for (auto source : before) {
				if (--cost_work < 0) return {};
				auto &owner = ownership[source];
				owner.readers.push_back(i);
				owner.retained |= after.count(source);
				modeled.insert(source);
				if (GetSize(modeled) > 65536) return {};
			}
			for (auto source : after) {
				if (--cost_work < 0) return {};
				modeled.insert(source);
				if (GetSize(modeled) > 65536) return {};
			}
			for (auto bit : outputs) {
				if (--cost_work < 0) return {};
				replaced.insert(bit);
			}
		}
		if (components > 1) {
			bool possible = false;
			dict<Signature, int> equivalent;
			for (auto &entry : ownership) {
				if (--cost_work < 0) return {};
				auto bit = entry.first;
				const auto &owner = entry.second;
				if (owner.retained || netlist.protected_bit(bit)) continue;
				auto source = netlist.source(bit);
				log_assert(source && source->cell);
				for (int reader : owner.readers) {
					if (--cost_work < 0) return {};
					if (find(reader) != find(owner.readers.front())) possible = true;
				}
				if (possible) break;
				if (supported(source->cell)) {
					auto key = signature(source->cell->type, expression_inputs(source->cell, source->offset));
					auto found = equivalent.find(key);
					if (found == equivalent.end()) equivalent[key] = owner.readers.front();
					else if (find(found->second) != find(owner.readers.front())) {
						possible = true;
						break;
					}
				}
			}
			if (possible) {
				pool<SigBit> external_roots, external_kept;
				for (auto bit : modeled) {
					if (--cost_work < 0) return {};
					if (module_cost.observed_outside(bit, modeled, replaced, cost_work)) external_roots.insert(bit);
					if (cost_work < 0) return {};
				}
				if (!collect_sources(external_roots, replaced, external_kept)) return {};
				equivalent.clear();
				for (auto &entry : ownership) {
					if (--cost_work < 0) return {};
					auto bit = entry.first;
					const auto &owner = entry.second;
					if (owner.retained || external_kept.count(bit) || netlist.protected_bit(bit)) continue;
					auto source = netlist.source(bit);
					log_assert(source && source->cell);
					int first = owner.readers.front();
					for (int reader : owner.readers) {
						if (--cost_work < 0) return {};
						join(first, reader);
					}
					if (supported(source->cell)) {
						auto key = signature(source->cell->type, expression_inputs(source->cell, source->offset));
						auto found = equivalent.find(key);
						if (found == equivalent.end()) equivalent[key] = first;
						else join(first, found->second);
					}
				}
			}
		}
		if (components == valid_count) return {};
		std::vector<std::vector<int>> groups(GetSize(candidates)), result;
		for (int i = 0; i < GetSize(candidates); i++) if (candidates[i].valid) {
			if (--cost_work < 0) return {};
			groups[find(i)].push_back(i);
		}
		for (int i = 0; i < GetSize(candidates); i++) if (candidates[i].valid) {
			if (--cost_work < 0) return {};
			auto &group = groups[find(i)];
			if (GetSize(group) > 1 && group.front() == i) result.push_back(std::move(group));
		}
		return result;
	}

	void commit(const std::vector<Candidate> &candidates, const std::vector<int> &accepted, const std::vector<SigBit> &order, const Estimate &cost)
	{
		std::vector<Edit> edits;
		pool<Cell *> removed, source_cells;
		dict<SigBit, PlanPtr> replacements;
		pool<int> nodes;
		pool<SigBit> roots;
		for (int index : accepted) {
			const auto &candidate = candidates[index];
			log_assert(netlist.port(candidate.cell, ID::A) == candidate.a && netlist.port(candidate.cell, ID::B) == candidate.b &&
				netlist.port(candidate.cell, ID::S) == candidate.s && netlist.port(candidate.cell, ID::Y) == candidate.y);
			SigSpec a, b, y;
			std::vector<int> remaining;
			for (int j = 0; j < GetSize(candidate.y); j++) {
				if (candidate.outputs[j]) {
					replacements[candidate.y[j]] = candidate.outputs[j];
					collect_plans(candidate.outputs[j], nodes, roots);
				} else {
					remaining.push_back(j);
					a.append(candidate.a[j]);
					y.append(candidate.y[j]);
				}
			}
			for (int i = 0; i < GetSize(candidate.s); i++) for (int j : remaining) b.append(candidate.b[i*GetSize(candidate.y)+j]);
			if (y.empty()) removed.insert(candidate.cell);
			else edits.push_back({candidate.cell, a, b, y});
		}
		for (auto bit : roots) {
			auto source = netlist.source(bit);
			if (source && source->cell && source->port == ID::Y) log_assert(!cost.erased.count({source->cell, source->offset}));
		}
		for (auto source : cost.erased) {
			log_assert(netlist.editable_bit(source.first, ID::Y, source.second));
			source_cells.insert(source.first);
		}
		for (auto cell : source_cells) {
			SigSpec a, b, y;
			const auto &original_y = netlist.port(cell, ID::Y);
			for (int i = 0; i < GetSize(original_y); i++) if (!cost.erased.count({cell, i})) {
				auto inputs = expression_inputs(cell, i);
				a.append(inputs[0]);
				b.append(inputs[1]);
				y.append(original_y[i]);
			}
			if (y.empty()) removed.insert(cell);
			else edits.push_back({cell, a, b, y});
		}
		// 原始索引的全部查询在此结束；提交仅使用已经确认的连接与端口内容。
		dict<int, SigBit> emitted;
		int connected = 0;
		for (auto bit : order) if (replacements.count(bit)) {
			module->connect(bit, materialize(replacements.at(bit), emitted));
			connected++;
		}
		log_assert(connected == GetSize(replacements));
		for (auto &edit : edits) {
			edit.cell->setPort(ID::A, edit.a);
			edit.cell->setPort(ID::B, edit.b);
			edit.cell->setPort(ID::Y, edit.y);
			if (edit.cell->type.in(ID($mux), ID($pmux))) edit.cell->setParam(ID::WIDTH, GetSize(edit.y));
			else {
				edit.cell->setParam(ID::A_WIDTH, GetSize(edit.a));
				edit.cell->setParam(ID::B_WIDTH, GetSize(edit.b));
				edit.cell->setParam(ID::Y_WIDTH, GetSize(edit.y));
				edit.cell->setParam(ID::A_SIGNED, false);
				edit.cell->setParam(ID::B_SIGNED, false);
			}
			log_assert(GetSize(edit.a) == GetSize(edit.y) && GetSize(edit.b) == GetSize(edit.y)*(edit.cell->type == ID($pmux) ? GetSize(edit.cell->getPort(ID::S)) : 1));
		}
		for (auto cell : removed) module->remove(cell);
		changes += connected;
		log("Factored %d PMUX output bits in %s; estimated local cost %d -> %d, removed %d source operation bits.\n",
			connected, log_id(module), cost.retained+cost.removed, cost.retained+cost.added, GetSize(cost.erased));
	}

	void factor()
	{
		std::vector<Cell *> pmuxes;
		for (auto cell : module->cells()) if (cell->type == ID($pmux) && readable_pmux(cell) && GetSize(netlist.port(cell, ID::S)) >= 3) {
			const auto &a = netlist.port(cell, ID::A), &b = netlist.port(cell, ID::B), &s = netlist.port(cell, ID::S), &y = netlist.port(cell, ID::Y);
			auto &choice = choices[s];
			choice.select = s;
			for (int j = 0; j < GetSize(y); j++) {
				SigSpec values(a[j]);
				for (int i = 0; i < GetSize(s); i++) values.append(b[i*GetSize(y)+j]);
				choice.exact[values].push_back(y[j]);
				choice.undefined_default[values.extract(1, GetSize(s))].push_back(y[j]);
			}
			if (netlist.editable(cell)) pmuxes.push_back(cell);
		}
		if (pmuxes.empty()) return;
		std::vector<Candidate> candidates;
		int output_count = 0;
		for (auto cell : pmuxes) {
			Candidate candidate;
			candidate.cell = cell;
			candidate.a = netlist.port(cell, ID::A);
			candidate.b = netlist.port(cell, ID::B);
			candidate.s = netlist.port(cell, ID::S);
			candidate.y = netlist.port(cell, ID::Y);
			bool found = false;
			for (int j = 0; j < GetSize(candidate.y); j++) {
				PlanPtr plan = nullptr;
				if (output_count < 8192 && analysis_work > 0)
					plan = lift(choices.at(candidate.s), branch_values(candidate, j), candidate.y[j], 3, candidate.sources, true);
				candidate.outputs.push_back(plan);
				if (plan) {
					found = true;
					output_count++;
				}
			}
			if (found) candidates.push_back(candidate);
		}
		if (candidates.empty()) return;
		decltype(choices)().swap(choices);
		decltype(plans)().swap(plans);
		auto order = check_candidates(candidates);
		pool<int> all_nodes;
		pool<SigBit> initial_roots;
		for (auto &candidate : candidates) for (auto plan : candidate.outputs) if (plan) collect_plans(plan, all_nodes, initial_roots);
		std::vector<int> accepted;
		for (int i = 0; i < GetSize(candidates); i++) {
			if (cost_work <= 0) break;
			if (!candidates[i].valid) {
				log_debug("Rejecting PMUX %s: dependency or analysis boundary.\n", log_id(candidates[i].cell));
				continue;
			}
			auto cost = estimate(candidates, {i}, initial_roots);
			if (cost.valid && cost.removed > cost.added) accepted.push_back(i);
			else log_debug("Rejecting PMUX %s: estimated gain %d, cost budget valid %d.\n", log_id(candidates[i].cell), cost.removed-cost.added, cost.valid);
		}
		Estimate cost;
		if (!accepted.empty()) {
			cost = estimate(candidates, accepted, {});
			if (!cost.valid || cost.removed <= cost.added) {
				log_debug("Rejecting factor transaction: final cost or work boundary.\n");
				return;
			}
		}
		if (cost_work > 0) for (auto &group : related_candidates(candidates, GetSize(accepted))) {
			if (cost_work <= 0) break;
			std::vector<int> proposed;
			std::set_union(accepted.begin(), accepted.end(), group.begin(), group.end(), std::back_inserter(proposed));
			cost_work -= GetSize(accepted) + GetSize(group) + GetSize(proposed);
			if (cost_work < 0) break;
			if (proposed == accepted) continue;
			auto joint = estimate(candidates, proposed, {});
			if (!joint.valid || joint.removed <= joint.added || joint.removed-joint.added <= cost.removed-cost.added) continue;
			accepted.swap(proposed);
			cost = std::move(joint);
		}
		if (accepted.empty()) return;
		log_assert(cost.valid && cost.removed > cost.added);
		for (int index : accepted) {
			const auto &candidate = candidates[index];
			int count = 0;
			for (auto plan : candidate.outputs) if (plan) count++;
			log("Factoring %d output bits of %s.%s.\n", count, log_id(module), log_id(candidate.cell));
		}
		commit(candidates, accepted, order, cost);
	}

	void reductions()
	{
		std::vector<Cell *> removed;
		for (auto reduce : module->cells().to_vector()) {
			if (!reduce->type.in(ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor)) ||
				!netlist.editable(reduce) || GetSize(reduce->getPort(ID::Y)) != 1) continue;
			const auto &input = netlist.port(reduce, ID::A);
			if (GetSize(input) < 4) continue;
			auto pmux = netlist.driver(input[0]);
			if (!pmux || pmux->type != ID($pmux) || !netlist.editable(pmux) || input != netlist.port(pmux, ID::Y) ||
				!netlist.private_signal(input, {reduce})) continue;
			const auto &a = netlist.port(pmux, ID::A), &b = netlist.port(pmux, ID::B), &s = netlist.port(pmux, ID::S);
			if (s.empty()) continue;
			std::vector<SigSpec> branches;
			branches.push_back(a);
			for (int i = 0; i < GetSize(s); i++) branches.push_back(b.extract(i*GetSize(a), GetSize(a)));
			pool<SigSpec> unique;
			for (auto &branch : branches) {
				branch.sort();
				unique.insert(branch);
			}
			if (GetSize(unique)*(GetSize(a)-1)+GetSize(s) >= GetSize(a)*(GetSize(s)+1)) continue;
			dict<SigSpec, SigBit> results;
			SigSpec reduced;
			for (auto branch : branches) {
				if (!results.count(branch)) {
					auto wire = module->addWire(NEW_ID);
					auto cell = module->addCell(NEW_ID, reduce->type);
					cell->setParam(ID::A_WIDTH, GetSize(branch));
					cell->setParam(ID::Y_WIDTH, 1);
					cell->setParam(ID::A_SIGNED, false);
					cell->setPort(ID::A, branch);
					cell->setPort(ID::Y, wire);
					results[branch] = SigBit(wire);
				}
				reduced.append(results.at(branch));
			}
			bool same_defined = true;
			for (int i = 2; i < GetSize(reduced); i++) if (reduced[i] != reduced[1]) same_defined = false;
			if (GetSize(unique) == 1 || (a.is_fully_undef() && same_defined))
				module->connect(reduce->getPort(ID::Y), reduced[1]);
			else module->addPmux(NEW_ID, reduced[0], reduced.extract(1, GetSize(s)), s, reduce->getPort(ID::Y));
			removed.push_back(reduce);
			removed.push_back(pmux);
			changes++;
		}
		for (auto cell : removed) module->remove(cell);
	}
};

struct OptPmuxFactorPass : public Pass {
	OptPmuxFactorPass() : Pass("opt_pmuxfactor", "exchange PMUX selection and shared operations") {}
	void help() override {
		log("    opt_pmuxfactor [selection]\n");
		log("\n");
		log("Factor shared bitwise operations and common-data muxes across PMUXes.\n");
		log("Move private reductions before PMUXes, sharing permuted reductions.\n");
		log("Undefined input regions may be refined. Explicit defaults are preserved.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		extra_args(args, 1, design);
		for (auto module : design->selected_modules()) {
			bool has_pmux = false;
			for (auto cell : module->selected_cells())
				if (cell->type == ID($pmux) && cell->hasPort(ID::Y) && !cell->get_bool_attribute(ID::keep)) {
					has_pmux = true;
					break;
				}
			if (!has_pmux) continue;
			bool whole_module = design->selected_whole_module(module);
			int changes;
			bool rebuild;
			{
				PmuxFactorWorker worker(module, design);
				worker.reductions();
				rebuild = worker.changes != 0;
				if (!rebuild) worker.factor();
				changes = worker.changes;
			}
			if (rebuild) {
				PmuxFactorWorker worker(module, design);
				worker.factor();
				changes += worker.changes;
			}
			if (changes) {
				{
					PmuxFactorWorker xors(module, design);
					xors.simplify_xors();
				}
				if (whole_module) {
					Pass::call_on_module(design, module, "opt_expr -fine");
					Pass::call_on_module(design, module, "opt_merge");
					Pass::call_on_module(design, module, "opt_clean");
				}
			}
		}
	}
} OptPmuxFactorPass;

PRIVATE_NAMESPACE_END
