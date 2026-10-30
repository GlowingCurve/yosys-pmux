// opt_pmuxfactor 提取 PMUX 分支的公共运算并前移归约运算；复用分支表达式与端口映射，减少选择逻辑和重复运算。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/utils.h"
#include "passes/opt/pmux_celltypes.h"
#include "passes/opt/pmux_lut_cost.h"
#include <deque>
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using LutCostGraph = PmuxLutCost::LutCostGraph;

struct PmuxFactorWorker {
	using OpBit = std::pair<Cell *, int>;
	using Signature = std::tuple<IdString, SigSpec>;
	Module *module;
	SigMap sigmap;
	PmuxCellTypes types;
	dict<SigBit, OpBit> drivers;
	dict<SigBit, std::vector<Cell *>> users;
	bool users_built = false;
	dict<std::pair<Cell *, IdString>, const SigSpec *> ports;
	std::deque<SigSpec> port_signals;
	dict<Cell *, bool> pmux_readable;
	dict<Cell *, bool> supported_cells;
	dict<OpBit, SigSpec> expression_cache;
	dict<SigBit, std::pair<bool, SigSpec>> input_cache;
	struct LutExpression {
		SigSpec inputs;
		uint16_t table;
	};
	dict<OpBit, LutExpression> lut_expressions;
	pool<OpBit> lut_boundaries;
	pool<SigBit> protected_bits, kept_bits, uncertain_bits;
	pool<SigBit> live_bits;
	bool live_built = false;
	pool<Cell *> selected, uncertain_cells;
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
		bool valid = true;
		int removed = 0, added = 0, retained = 0;
		pool<OpBit> erased;
	};

	PmuxFactorWorker(Module *module, Design *design) : module(module), sigmap(module), types(module, design)
	{
		for (auto wire : module->wires()) {
			bool keep = wire->get_bool_attribute(ID::keep);
			if (!wire->port_input && !wire->port_output && !keep) continue;
			for (auto bit : sigmap(wire)) {
				if (wire->port_input) drivers[bit] = {nullptr, 0};
				if (wire->port_output || keep) {
					protected_bits.insert(bit);
					if (keep) kept_bits.insert(bit);
				}
			}
		}
		for (auto cell : module->cells()) {
			if (design->selected(module, cell)) selected.insert(cell);
			bool keep = cell->get_bool_attribute(ID::keep);
			for (auto &port : cell->connections()) {
				auto signal = sigmap(port.second);
				auto direction = types.cell_port_dir(cell->type, port.first);
				bool unknown = direction == RTLIL::PD_UNKNOWN || direction == RTLIL::PD_INOUT;
				if (unknown) uncertain_cells.insert(cell);
				bool output = unknown || direction == RTLIL::PD_OUTPUT;
				for (int i = 0; i < GetSize(signal); i++) {
					if (unknown) uncertain_bits.insert(signal[i]);
					if (output) {
						if (drivers.count(signal[i])) {
							drivers[signal[i]] = {nullptr, 0};
							uncertain_bits.insert(signal[i]);
						} else drivers[signal[i]] = {cell, i};
					}
					if (keep) {
						protected_bits.insert(signal[i]);
						kept_bits.insert(signal[i]);
					}
				}
			}
		}
	}

	void ensure_users()
	{
		if (users_built) return;
		for (auto cell : module->cells()) for (auto &port : cell->connections()) {
			auto direction = types.cell_port_dir(cell->type, port.first);
			if (direction != RTLIL::PD_UNKNOWN && direction != RTLIL::PD_INOUT && direction != RTLIL::PD_INPUT) continue;
			for (auto bit : sigmap(port.second)) {
				auto &list = users[bit];
				if (list.empty() || list.back() != cell) list.push_back(cell);
			}
		}
		users_built = true;
	}

	bool check_supported(Cell *cell)
	{
		if (!cell->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($mux)) || uncertain_cells.count(cell)) return false;
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
			const auto &y = port(cell, ID::Y);
			for (int i = 0; i < GetSize(y); i++)
				if (!uncertain_bits.count(y[i]) && drivers.count(y[i]) && drivers.at(y[i]) == OpBit(cell, i))
					operators[signature(cell->type, expression_inputs(cell, i))].push_back(y[i]);
		}
		operators_built = true;
	}

	bool editable(Cell *cell)
	{
		if (!cell->hasPort(ID::Y) || !selected.count(cell) || cell->get_bool_attribute(ID::keep) || uncertain_cells.count(cell)) return false;
		pool<SigBit> seen;
		auto y = sigmap(cell->getPort(ID::Y));
		for (int i = 0; i < GetSize(y); i++)
			if (!y[i].wire || !seen.insert(y[i]).second || kept_bits.count(y[i]) || uncertain_bits.count(y[i]) ||
				!drivers.count(y[i]) || drivers.at(y[i]) != OpBit(cell, i)) return false;
		return true;
	}

	const SigSpec &port(Cell *cell, IdString name)
	{
		auto key = std::make_pair(cell, name);
		auto found = ports.find(key);
		if (found != ports.end()) return *found->second;
		log_assert(cell->hasPort(name));
		port_signals.push_back(sigmap(cell->getPort(name)));
		ports[key] = &port_signals.back();
		return port_signals.back();
	}

	bool can_remove(OpBit source)
	{
		auto cell = source.first;
		log_assert(source.second >= 0 && source.second < GetSize(cell->getPort(ID::Y)));
		auto bit = port(cell, ID::Y)[source.second];
		return selected.count(cell) && !cell->get_bool_attribute(ID::keep) && !kept_bits.count(bit) &&
			!uncertain_bits.count(bit) && bit.wire && drivers.count(bit) && drivers.at(bit) == source;
	}

	SigBit operand(Cell *cell, IdString port, int index)
	{
		const auto &signal = this->port(cell, port);
		bool sign = cell->getParam(ID::A_SIGNED).as_bool();
		if (cell->hasPort(ID::B)) sign &= cell->getParam(ID::B_SIGNED).as_bool();
		if (index < GetSize(signal)) return signal[index];
		return sign && !signal.empty() ? signal.back() : SigBit(State::S0);
	}

	const SigSpec &expression_inputs(Cell *cell, int offset)
	{
		auto source = OpBit(cell, offset);
		auto found = expression_cache.find(source);
		if (found != expression_cache.end()) return found->second;
		log_assert(supported(cell) && offset >= 0 && offset < GetSize(cell->getPort(ID::Y)));
		SigSpec result;
		if (cell->type == ID($mux)) {
			result.append(port(cell, ID::A)[offset]);
			result.append(port(cell, ID::B)[offset]);
			result.append(port(cell, ID::S));
		} else {
			result.append(operand(cell, ID::A, offset));
			result.append(operand(cell, ID::B, offset));
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
		auto found = drivers.find(bit);
		if (found == drivers.end() || !found->second.first || uncertain_bits.count(bit)) return false;
		auto source = found->second;
		if (!supported(source.first)) return false;
		auto inputs = expression_inputs(source.first, source.second);
		type = source.first->type;
		a = inputs[0];
		b = inputs[1];
		return true;
	}

	bool check_pmux_shape(Cell *cell)
	{
		if (cell->type != ID($pmux) || uncertain_cells.count(cell) || !cell->hasPort(ID::A) || !cell->hasPort(ID::B) ||
			!cell->hasPort(ID::S) || !cell->hasPort(ID::Y) || !cell->hasParam(ID::WIDTH) || !cell->hasParam(ID::S_WIDTH)) return false;
		const auto &a = port(cell, ID::A), &b = port(cell, ID::B), &s = port(cell, ID::S), &y = port(cell, ID::Y);
		if (GetSize(a) != GetSize(y) || GetSize(b) != GetSize(y)*GetSize(s) ||
			cell->getParam(ID::WIDTH).as_int() != GetSize(y) || cell->getParam(ID::S_WIDTH).as_int() != GetSize(s)) return false;
		pool<SigBit> seen;
		for (int i = 0; i < GetSize(y); i++) if (!y[i].wire || !seen.insert(y[i]).second || uncertain_bits.count(y[i]) ||
			!drivers.count(y[i]) || drivers.at(y[i]) != OpBit(cell, i)) return false;
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

	bool read_original_inputs(SigBit bit, SigSpec &inputs)
	{
		if (!bit.wire) return true;
		if (uncertain_bits.count(bit)) return false;
		auto found = drivers.find(bit);
		if (found == drivers.end() || !found->second.first) return true;
		auto source = found->second;
		auto cell = source.first;
		if (uncertain_cells.count(cell)) return false;
		if (StaticCellTypes::categories.is_ff(cell->type)) return true;
		if (supported(cell)) {
			inputs = expression_inputs(cell, source.second);
			return true;
		}
		if (cell->type == ID($pmux)) {
			if (!readable_pmux(cell)) return false;
			const auto &a = port(cell, ID::A), &b = port(cell, ID::B), &s = port(cell, ID::S), &y = port(cell, ID::Y);
			log_assert(source.second >= 0 && source.second < GetSize(y) && y[source.second] == bit);
			inputs.append(a[source.second]);
			inputs.append(s);
			for (int i = 0; i < GetSize(s); i++) inputs.append(b[i*GetSize(y)+source.second]);
			return true;
		}
		if (!types.cell_evaluable(cell->type)) return false;
		for (auto &connection : cell->connections()) if (types.cell_input(cell->type, connection.first)) inputs.append(port(cell, connection.first));
		return true;
	}

	bool original_inputs(SigBit bit, SigSpec &inputs)
	{
		auto found = input_cache.find(bit);
		if (found == input_cache.end()) {
			SigSpec result;
			bool valid = read_original_inputs(bit, result);
			input_cache[bit] = {valid, result};
			found = input_cache.find(bit);
		}
		inputs = found->second.second;
		return found->second.first;
	}

	bool build_live_bits()
	{
		if (live_built) return cost_work >= 0;
		live_built = true;
		std::vector<SigBit> pending(protected_bits.begin(), protected_bits.end());
		for (auto cell : module->cells())
			if (!selected.count(cell) || uncertain_cells.count(cell) ||
				(!types.cell_evaluable(cell->type) && !StaticCellTypes::categories.is_ff(cell->type)))
				for (auto &connection : cell->connections()) for (auto bit : port(cell, connection.first)) {
					if (--cost_work < 0) return false;
					pending.push_back(bit);
				}
		pool<Cell *> expanded_full;
		for (int i = 0; i < GetSize(pending); i++) {
			auto bit = pending[i];
			if (!bit.wire || !live_bits.insert(bit).second) continue;
			if (--cost_work < 0) return false;
			auto found = drivers.find(bit);
			if (found == drivers.end() || !found->second.first) continue;
			auto cell = found->second.first;
			SigSpec inputs;
			if (!supported(cell) && !(cell->type == ID($pmux) && readable_pmux(cell))) {
				if (!expanded_full.insert(cell).second) continue;
				for (auto &connection : cell->connections()) if (types.cell_input(cell->type, connection.first))
					inputs.append(port(cell, connection.first));
			} else if (supported(cell)) inputs = expression_inputs(cell, found->second.second);
			else {
				const auto &a = port(cell, ID::A), &b = port(cell, ID::B), &s = port(cell, ID::S), &y = port(cell, ID::Y);
				inputs.append(a[found->second.second]);
				inputs.append(s);
				for (int j = 0; j < GetSize(s); j++) inputs.append(b[j*GetSize(y)+found->second.second]);
			}
			for (auto input : inputs) {
				if (--cost_work < 0) return false;
				pending.push_back(input);
			}
		}
		return true;
	}

	bool dependencies(SigBit bit, const pool<SigBit> &stops, pool<SigBit> &references, pool<SigBit> &seen,
		pool<SigBit> &active, int &budget, int &work)
	{
		if (!bit.wire) return true;
		if (stops.count(bit)) {
			references.insert(bit);
			return true;
		}
		if (active.count(bit)) return false;
		if (!seen.insert(bit).second) return true;
		if (--budget < 0 || --work < 0) return false;
		SigSpec inputs;
		if (!original_inputs(bit, inputs)) return false;
		active.insert(bit);
		for (auto input : inputs) if (!dependencies(input, stops, references, seen, active, budget, work)) return false;
		active.erase(bit);
		return true;
	}

	bool independent(SigBit bit, SigBit target)
	{
		pool<SigBit> stops, references, seen, active;
		stops.insert(target);
		int budget = 512;
		return dependencies(bit, stops, references, seen, active, budget, analysis_work) && references.empty();
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
				auto source = drivers.at(values[i]);
				sources.insert(source);
				if (common.empty()) {
					common = type;
					first_a = a;
					first_b = b;
				}
				if (type != ID($mux) && a == first_b && b != first_b) std::swap(a, b);
				aa.append(a);
				bb.append(b);
				if (type == ID($mux)) ss.append(port(source.first, ID::S));
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
		auto found = drivers.find(bit);
		if (depth && found != drivers.end() && found->second.first && found->second.first->type == ID($xor) &&
			expression(bit, type, a, b)) {
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
			if (cell->type != ID($xor) || !editable(cell)) continue;
			auto y = sigmap(cell->getPort(ID::Y));
			SigSpec a, b, remaining;
			for (int i = 0; i < GetSize(y); i++) {
				pool<SigBit> terms;
				xor_terms(operand(cell, ID::A, i), terms, 3);
				xor_terms(operand(cell, ID::B, i), terms, 3);
				if (GetSize(terms) <= 1) {
					module->connect(y[i], terms.empty() ? SigBit(State::S0) : *terms.begin());
					changes++;
				} else {
					a.append(operand(cell, ID::A, i));
					b.append(operand(cell, ID::B, i));
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
				pool<SigBit> inputs, references, seen, active;
				collect_plans(candidate.outputs[j], plan_ids, inputs);
				SigSpec original;
				if (!original_inputs(candidate.y[j], original)) candidate.valid = false;
				for (auto bit : original) inputs.insert(bit);
				int budget = 512;
				for (auto bit : inputs) if (!dependencies(bit, stops, references, seen, active, budget, analysis_work)) candidate.valid = false;
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
			auto source = drivers.at(pending[i]);
			if (!region.insert(source).second) continue;
			if (--cost_work < 0 || GetSize(region) > 65536) return false;
			for (auto input : expression_inputs(source.first, source.second)) pending.push_back(input);
		}
		return true;
	}

	bool retained(const pool<OpBit> &region, const dict<Cell *, pool<int>> &rewritten, const pool<SigBit> &plan_roots,
		pool<OpBit> &kept, pool<SigBit> *external_roots = nullptr)
	{
		pool<Cell *> source_cells;
		dict<SigBit, OpBit> source_bits;
		pool<SigBit> roots;
		for (auto source : region) {
			if (--cost_work < 0) return false;
			auto bit = port(source.first, ID::Y)[source.second];
			source_cells.insert(source.first);
			source_bits[bit] = source;
			if (protected_bits.count(bit) || !can_remove(source)) roots.insert(bit);
		}
		if (!region.empty()) ensure_users();
		for (auto source : region) {
			auto bit = port(source.first, ID::Y)[source.second];
			if (users.count(bit)) for (auto user : reversed(users.at(bit))) {
				if (--cost_work < 0) return false;
				if (!source_cells.count(user) && !rewritten.count(user)) roots.insert(bit);
			}
		}
		for (auto cell : source_cells) {
			const auto &y = port(cell, ID::Y);
			for (int i = 0; i < GetSize(y); i++) if (!region.count({cell, i}))
				for (auto bit : expression_inputs(cell, i)) {
					if (--cost_work < 0) return false;
					if (source_bits.count(bit)) roots.insert(bit);
				}
		}
		for (auto &entry : rewritten) {
			auto cell = entry.first;
			const auto &a = port(cell, ID::A), &b = port(cell, ID::B), &s = port(cell, ID::S), &y = port(cell, ID::Y);
			if (GetSize(entry.second) == GetSize(y)) continue;
			for (auto bit : s) if (source_bits.count(bit)) roots.insert(bit);
			for (int j = 0; j < GetSize(y); j++) if (!entry.second.count(j)) {
				if (source_bits.count(a[j])) roots.insert(a[j]);
				for (int i = 0; i < GetSize(s); i++) {
					if (--cost_work < 0) return false;
					auto bit = b[i*GetSize(y)+j];
					if (source_bits.count(bit)) roots.insert(bit);
				}
			}
		}
		if (external_roots) *external_roots = roots;
		for (auto source : region) {
			auto bit = port(source.first, ID::Y)[source.second];
			if (plan_roots.count(bit)) roots.insert(bit);
		}
		std::vector<OpBit> pending;
		for (auto bit : roots) if (source_bits.count(bit)) pending.push_back(source_bits.at(bit));
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

	bool lut_expression(OpBit source, LutExpression &result)
	{
		auto found = lut_expressions.find(source);
		if (found != lut_expressions.end()) {
			result = found->second;
			return true;
		}
		if (lut_boundaries.count(source)) return false;
		auto cell = source.first;
		if (supported(cell)) {
			result.inputs = expression_inputs(cell, source.second);
			result.table = operation_table(cell->type);
		} else {
			pool<SigBit> inputs;
			int connections = 0;
			bool usable = types.cell_evaluable(cell->type) && cell->hasPort(ID::Y) && GetSize(cell->getPort(ID::Y)) == 1;
			for (auto &connection : cell->connections()) {
				connections += GetSize(connection.second);
				if (connections > 64) {
					lut_boundaries.insert(source);
					return false;
				}
				if (connection.first == ID::Y) continue;
				if (!connection.first.in(ID::A, ID::B)) usable = false;
				for (auto bit : port(cell, connection.first)) {
					if (--cost_work < 0) return false;
					if (bit.wire) inputs.insert(bit);
					else if (bit != State::S0 && bit != State::S1) usable = false;
				}
			}
			if (!usable || connections > 64 || GetSize(inputs) > 4) {
				lut_boundaries.insert(source);
				return false;
			}
			result.inputs = SigSpec(std::vector<SigBit>(inputs.begin(), inputs.end()));
			result.inputs.sort();
			dict<SigBit, int> positions;
			for (int i = 0; i < GetSize(result.inputs); i++) positions[result.inputs[i]] = i;
			result.table = 0;
			for (int assignment = 0; assignment < (1 << GetSize(result.inputs)); assignment++) {
				Const a, b;
				for (auto name : {ID::A, ID::B}) if (cell->hasPort(name)) for (auto bit : port(cell, name)) {
					if (--cost_work < 0) return false;
					State value = bit.wire ? ((assignment >> positions.at(bit)) & 1 ? State::S1 : State::S0) : bit.data;
					(name == ID::A ? a : b).append(Const(value, 1));
				}
				if (--cost_work < 0) return false;
				bool error = false;
				auto value = CellTypes::eval(cell, a, b, &error);
				if (error || source.second >= GetSize(value) || (value[source.second] != State::S0 && value[source.second] != State::S1)) {
					lut_boundaries.insert(source);
					return false;
				}
				if (value[source.second] == State::S1) result.table |= 1 << assignment;
			}
		}
		lut_expressions[source] = result;
		return true;
	}

	struct CostSignal {
		int value, care;
	};

	struct CostBuilder {
		PmuxFactorWorker &worker;
		LutCostGraph &graph;
		const dict<SigBit, PlanPtr> &replacements;
		bool changed;
		dict<SigBit, CostSignal> bits;
		dict<int, CostSignal> plans;
		pool<SigBit> active;
		pool<OpBit> expanded;

		CostBuilder(PmuxFactorWorker &worker, LutCostGraph &graph, const dict<SigBit, PlanPtr> &replacements, bool changed) :
			worker(worker), graph(graph), replacements(replacements), changed(changed) {}

		CostSignal operation(uint16_t table, const std::vector<CostSignal> &args)
		{
			std::vector<int> values, care;
			for (auto arg : args) {
				values.push_back(arg.value);
				care.push_back(arg.care);
			}
			return {graph.gate(table, values), graph.reduce(8, care, 1)};
		}

		CostSignal choice(const SigSpec &values, const SigSpec &select)
		{
			log_assert(GetSize(values) == GetSize(select)+1);
			auto fallback = bit(values[0]);
			int enabled = 0, collision = 0;
			std::vector<int> terms, care;
			for (int i = 0; i < GetSize(select); i++) {
				auto control = bit(select[i]), data = bit(values[i+1]);
				terms.push_back(graph.gate(8, {data.value, control.value}));
				care.push_back(data.care);
				care.push_back(control.care);
				collision = graph.gate(14, {collision, graph.gate(8, {enabled, control.value})});
				enabled = graph.gate(14, {enabled, control.value});
			}
			int selected = graph.reduce(14, terms, 0);
			int value = fallback.value == 0 ? selected : graph.gate(0xca, {fallback.value, selected, enabled});
			care.push_back(graph.gate(1, {collision}));
			care.push_back(graph.gate(14, {enabled, fallback.care}));
			return {value, graph.reduce(8, care, 1)};
		}

		CostSignal bit(SigBit value)
		{
			if (!graph.spend()) return {0, 0};
			if (!value.wire) return {value == State::S1 ? 1 : 0, value == State::S0 || value == State::S1 ? 1 : 0};
			auto found = bits.find(value);
			if (found != bits.end()) return found->second;
			if (!active.insert(value).second) {
				graph.valid = false;
				return {0, 0};
			}
			CostSignal result;
			if (changed && replacements.count(value)) result = plan(replacements.at(value));
			else {
				auto driver = worker.drivers.find(value);
				if (driver == worker.drivers.end() || !driver->second.first || worker.uncertain_bits.count(value) ||
					StaticCellTypes::categories.is_ff(driver->second.first->type)) result = {graph.leaf(value), 1};
				else {
					auto source = driver->second;
					auto cell = source.first;
					bool fixed = !worker.selected.count(cell) || cell->get_bool_attribute(ID::keep) || worker.kept_bits.count(value);
					if (cell->type == ID($pmux) && fixed) result = {graph.leaf(value), 1};
					else if (cell->type == ID($pmux) && worker.readable_pmux(cell)) {
						expanded.insert(source);
						const auto &y = worker.port(cell, ID::Y), &s = worker.port(cell, ID::S), &b = worker.port(cell, ID::B);
						SigSpec values(worker.port(cell, ID::A)[source.second]);
						for (int i = 0; i < GetSize(s); i++) values.append(b[i*GetSize(y)+source.second]);
						result = choice(values, s);
					} else {
						LutExpression expression;
						if (worker.lut_expression(source, expression)) {
							if (fixed) {
								graph.fixed_bits.insert(value);
								result = {graph.leaf(value), 1};
							} else {
								expanded.insert(source);
								std::vector<CostSignal> args;
								for (auto input : expression.inputs) args.push_back(bit(input));
								result = operation(expression.table, args);
							}
						} else result = {graph.leaf(value), 1};
					}
				}
			}
			active.erase(value);
			bits[value] = result;
			return result;
		}

		CostSignal plan(PlanPtr node)
		{
			auto found = plans.find(node->id);
			if (found != plans.end()) return found->second;
			CostSignal result;
			if (node->kind == Plan::Existing) result = bit(node->result);
			else if (node->kind == Plan::Selector) result = choice(node->values, node->select);
			else {
				std::vector<CostSignal> args;
				for (auto arg : node->args) args.push_back(plan(arg));
				result = operation(operation_table(node->type), args);
			}
			plans[node->id] = result;
			return result;
		}
	};

	bool observed_outside(OpBit source, const pool<OpBit> &modeled, dict<Cell *, bool> &generic_observers)
	{
		auto bit = port(source.first, ID::Y)[source.second];
		if (!live_bits.count(bit)) return false;
		if (protected_bits.count(bit)) return true;
		ensure_users();
		if (!users.count(bit)) return false;
		for (auto user : reversed(users.at(bit))) {
			if (!supported(user) && !(user->type == ID($pmux) && readable_pmux(user))) {
				auto found = generic_observers.find(user);
				if (found == generic_observers.end()) {
					bool observed = !selected.count(user) || user->get_bool_attribute(ID::keep) || uncertain_cells.count(user) ||
						(!types.cell_evaluable(user->type) && !StaticCellTypes::categories.is_ff(user->type));
					for (auto &connection : user->connections()) if (types.cell_output(user->type, connection.first)) {
						const auto &output = port(user, connection.first);
						for (int i = 0; i < GetSize(output); i++) {
							if (--cost_work < 0) return false;
							if (live_bits.count(output[i]) && (connection.first != ID::Y || !modeled.count({user, i}))) observed = true;
						}
					}
					generic_observers[user] = observed;
					found = generic_observers.find(user);
				}
				if (found->second) return true;
				continue;
			}
			const auto &y = port(user, ID::Y);
			for (int i = 0; i < GetSize(y); i++) if (live_bits.count(y[i]) && !modeled.count({user, i})) {
				if (--cost_work < 0) return false;
				SigSpec inputs;
				if (!original_inputs(y[i], inputs)) return true;
				for (auto input : inputs) {
					if (--cost_work < 0) return false;
					if (input == bit) return true;
				}
			}
		}
		return false;
	}

	Estimate estimate(const std::vector<Candidate> &candidates, const std::vector<int> &accepted, const pool<SigBit> &extra_roots)
	{
		Estimate result;
		if (!build_live_bits()) {
			result.valid = false;
			return result;
		}
		pool<OpBit> region, after_kept;
		pool<int> nodes;
		pool<SigBit> roots, external_roots, extra_kept;
		dict<Cell *, pool<int>> rewritten;
		dict<SigBit, PlanPtr> replacements;
		for (int index : accepted) {
			const auto &candidate = candidates[index];
			for (auto source : candidate.sources) if (!add_region(port(source.first, ID::Y)[source.second], region)) result.valid = false;
			for (int j = 0; j < GetSize(candidate.y); j++) if (candidate.outputs[j]) {
				collect_plans(candidate.outputs[j], nodes, roots);
				rewritten[candidate.cell].insert(j);
				replacements[candidate.y[j]] = candidate.outputs[j];
			}
		}
		for (auto bit : roots) if (!add_region(bit, region)) result.valid = false;
		for (auto source : region) {
			if (--cost_work < 0) result.valid = false;
			auto bit = port(source.first, ID::Y)[source.second];
			if (extra_roots.count(bit) && !roots.count(bit)) {
				roots.insert(bit);
				extra_kept.insert(bit);
			}
		}
		if (!result.valid || !retained(region, rewritten, roots, after_kept, &external_roots)) {
			result.valid = false;
			return result;
		}
		for (auto bit : extra_kept) external_roots.insert(bit);
		for (auto source : region) if (!after_kept.count(source) && can_remove(source)) result.erased.insert(source);
		pool<Signature> checked;
		pool<OpBit> shared, extended = region;
		for (auto source : region) {
			if (--cost_work < 0) {
				result.valid = false;
				return result;
			}
			auto cell = source.first;
			auto inputs = expression_inputs(cell, source.second);
			auto original_key = signature(cell->type, inputs);
			if (!checked.insert(original_key).second) continue;
			ensure_operators();
			auto found = operators.find(original_key);
			log_assert(found != operators.end());
			for (auto other : found->second) {
				if (--cost_work < 0) {
					result.valid = false;
					return result;
				}
				auto outside = drivers.at(other);
				if (!region.count(outside) && live_bits.count(other)) {
					shared.insert(outside);
					extended.insert(outside);
				}
			}
		}
		if (!shared.empty()) {
			pool<OpBit> live_shared;
			if (!retained(extended, rewritten, roots, live_shared)) {
				result.valid = false;
				return result;
			}
			for (auto source : shared) if (live_shared.count(source)) external_roots.insert(port(source.first, ID::Y)[source.second]);
		}
		LutCostGraph graph(cost_work);
		CostBuilder before(*this, graph, replacements, false), after(*this, graph, replacements, true);
		std::vector<CostSignal> old_signals, new_signals;
		for (auto bit : external_roots) {
			auto old_signal = before.bit(bit), new_signal = after.bit(bit);
			old_signals.push_back(old_signal);
			new_signals.push_back(new_signal);
		}
		for (auto &entry : replacements) {
			old_signals.push_back(before.bit(entry.first));
			new_signals.push_back(after.bit(entry.first));
		}
		pool<OpBit> modeled = before.expanded;
		for (auto source : after.expanded) modeled.insert(source);
		dict<Cell *, bool> generic_observers;
		for (auto source : modeled) if (observed_outside(source, modeled, generic_observers)) {
			auto bit = port(source.first, ID::Y)[source.second];
			if (!external_roots.insert(bit).second) continue;
			old_signals.push_back(before.bit(bit));
			new_signals.push_back(after.bit(bit));
		}
		std::vector<int> old_roots, new_roots;
		for (auto signal : old_signals) {
			graph.prepare_certificate(signal.value, signal.care);
			old_roots.push_back(signal.value);
		}
		for (auto signal : new_signals) {
			graph.prepare_certificate(signal.value, signal.care);
			new_roots.push_back(signal.value);
		}
		auto old_cover = graph.cover(old_roots);
		dict<int, PmuxLutCost::Cut> old_cuts;
		if (ys_debug(1)) for (int id : old_cover) old_cuts[id] = graph.nodes[id].best_cut();
		auto new_cover = graph.cover(new_roots);
		result.valid = graph.valid && cost_work >= 0;
		if (!result.valid) return result;
		for (int id : old_cover) {
			if (new_cover.count(id)) result.retained++;
			else result.removed++;
		}
		for (int id : new_cover) if (!old_cover.count(id)) result.added++;
		result.retained += GetSize(graph.fixed_bits);
		log_debug("LUT4 cover in %s: %d -> %d, %d graph nodes, certificates 5/6/7=%d/%d/%d, partial functions %d, work remaining %d.\n",
			log_id(module), result.retained+result.removed, result.retained+result.added, GetSize(graph.nodes),
			graph.certificate_widths[5], graph.certificate_widths[6], graph.certificate_widths[7], graph.partial_functions, cost_work);
		if (ys_debug(1)) {
			int diagnostic_work = 16384;
			for (int index : accepted) log_debug("Cost target %s.\n", log_id(candidates[index].cell));
			for (auto &entry : replacements) log_debug("Cost replacement %s plan %d.\n", log_signal(entry.first), entry.second->id);
			for (auto bit : external_roots) log_debug("Cost mandatory %s.\n", log_signal(bit));
			for (auto source : region) {
				if (--diagnostic_work < 0) break;
				log_debug("Cost source %s offset %d erased %d.\n", log_id(source.first), source.second, result.erased.count(source));
			}
			for (int id : nodes) {
				if (--diagnostic_work < 0) break;
				const auto *plan = &plan_nodes[id];
				log_debug("Cost plan %d kind %d type %s values %s select %s.", id, plan->kind, log_id(plan->type), log_signal(plan->values), log_signal(plan->select));
				for (auto arg : plan->args) log_debug(" arg %d", arg->id);
				log_debug("\n");
			}
			for (auto &entry : before.bits) log_debug("Cost before bit %s value %d care %d.\n", log_signal(entry.first), entry.second.value, entry.second.care);
			for (auto &entry : after.bits) log_debug("Cost after bit %s value %d care %d.\n", log_signal(entry.first), entry.second.value, entry.second.care);
			for (auto signal : old_signals) log_debug("Cost before root %d care %d.\n", signal.value, signal.care);
			for (auto signal : new_signals) log_debug("Cost after root %d care %d.\n", signal.value, signal.care);
			for (int id = 0; id < GetSize(graph.nodes); id++) {
				if (--diagnostic_work < 0) break;
				const auto &node = graph.nodes[id];
				log_debug("Cost node %d table %u leaf %d before %d after %d inputs", id, unsigned(node.table), node.leaf, old_cover.count(id), new_cover.count(id));
				for (int input : node.inputs) log_debug(" %d", input);
				log_debug(" old_cut");
				if (old_cuts.count(id)) for (int input : old_cuts.at(id)) log_debug(" %d", input);
				log_debug(" new_cut");
				if (new_cover.count(id)) for (int input : node.best_cut()) log_debug(" %d", input);
				log_debug("\n");
			}
		}
		return result;
	}

	bool collect_sources(const pool<SigBit> &roots, const pool<SigBit> &stops, pool<OpBit> &sources)
	{
		std::vector<SigBit> pending(roots.begin(), roots.end());
		pool<SigBit> seen;
		for (int i = 0; i < GetSize(pending); i++) {
			if (--cost_work < 0) return false;
			auto bit = pending[i];
			if (!bit.wire || stops.count(bit) || !seen.insert(bit).second) continue;
			auto found = drivers.find(bit);
			if (found == drivers.end() || !found->second.first || uncertain_bits.count(bit)) continue;
			auto source = found->second;
			auto cell = source.first;
			if (!selected.count(cell) || cell->get_bool_attribute(ID::keep) || kept_bits.count(bit) ||
				StaticCellTypes::categories.is_ff(cell->type)) continue;
			SigSpec inputs;
			if (cell->type == ID($pmux) && readable_pmux(cell)) {
				if (!original_inputs(bit, inputs)) return false;
			} else {
				LutExpression expression;
				if (!lut_expression(source, expression)) {
					if (cost_work < 0) return false;
					continue;
				}
				inputs = expression.inputs;
			}
			if (sources.insert(source).second && GetSize(sources) > 65536) return false;
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
		dict<OpBit, Ownership> ownership;
		dict<int, int> plan_owner;
		pool<OpBit> modeled;
		pool<SigBit> replaced;
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
			pool<OpBit> before, after;
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
				auto source = entry.first;
				const auto &owner = entry.second;
				auto bit = port(source.first, ID::Y)[source.second];
				if (owner.retained || protected_bits.count(bit) || !can_remove(source)) continue;
				for (int reader : owner.readers) {
					if (--cost_work < 0) return {};
					if (find(reader) != find(owner.readers.front())) possible = true;
				}
				if (possible) break;
				if (supported(source.first)) {
					auto key = signature(source.first->type, expression_inputs(source.first, source.second));
					auto found = equivalent.find(key);
					if (found == equivalent.end()) equivalent[key] = owner.readers.front();
					else if (find(found->second) != find(owner.readers.front())) {
						possible = true;
						break;
					}
				}
			}
			if (possible) {
				pool<SigBit> external_roots;
				pool<OpBit> external_kept;
				dict<Cell *, bool> generic_observers;
				for (auto source : modeled) {
					if (--cost_work < 0) return {};
					if (observed_outside(source, modeled, generic_observers)) external_roots.insert(port(source.first, ID::Y)[source.second]);
				}
				if (!collect_sources(external_roots, replaced, external_kept)) return {};
				equivalent.clear();
				for (auto &entry : ownership) {
					if (--cost_work < 0) return {};
					auto source = entry.first;
					const auto &owner = entry.second;
					auto bit = port(source.first, ID::Y)[source.second];
					if (owner.retained || external_kept.count(source) ||
						protected_bits.count(bit) || !can_remove(source)) continue;
					int first = owner.readers.front();
					for (int reader : owner.readers) {
						if (--cost_work < 0) return {};
						join(first, reader);
					}
					if (supported(source.first)) {
						auto key = signature(source.first->type, expression_inputs(source.first, source.second));
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
			log_assert(sigmap(candidate.cell->getPort(ID::A)) == candidate.a && sigmap(candidate.cell->getPort(ID::B)) == candidate.b &&
				sigmap(candidate.cell->getPort(ID::S)) == candidate.s && sigmap(candidate.cell->getPort(ID::Y)) == candidate.y);
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
		for (auto bit : roots) if (drivers.count(bit)) log_assert(!cost.erased.count(drivers.at(bit)));
		for (auto source : cost.erased) {
			log_assert(can_remove(source));
			source_cells.insert(source.first);
		}
		for (auto cell : source_cells) {
			SigSpec a, b, y;
			const auto &original_y = port(cell, ID::Y);
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
		for (auto cell : module->cells()) if (cell->type == ID($pmux) && readable_pmux(cell) && GetSize(port(cell, ID::S)) >= 3) {
			const auto &a = port(cell, ID::A), &b = port(cell, ID::B), &s = port(cell, ID::S), &y = port(cell, ID::Y);
			auto &choice = choices[s];
			choice.select = s;
			for (int j = 0; j < GetSize(y); j++) {
				SigSpec values(a[j]);
				for (int i = 0; i < GetSize(s); i++) values.append(b[i*GetSize(y)+j]);
				choice.exact[values].push_back(y[j]);
				choice.undefined_default[values.extract(1, GetSize(s))].push_back(y[j]);
			}
			if (editable(cell)) pmuxes.push_back(cell);
		}
		if (pmuxes.empty()) return;
		std::vector<Candidate> candidates;
		int output_count = 0;
		for (auto cell : pmuxes) {
			Candidate candidate;
			candidate.cell = cell;
			candidate.a = port(cell, ID::A);
			candidate.b = port(cell, ID::B);
			candidate.s = port(cell, ID::S);
			candidate.y = port(cell, ID::Y);
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
			if (!reduce->type.in(ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor)) || !editable(reduce) || GetSize(reduce->getPort(ID::Y)) != 1) continue;
			auto input = sigmap(reduce->getPort(ID::A));
			if (GetSize(input) < 4 || !drivers.count(input[0]) || !drivers.at(input[0]).first) continue;
			auto pmux = drivers.at(input[0]).first;
			if (pmux->type != ID($pmux) || !editable(pmux) || input != sigmap(pmux->getPort(ID::Y))) continue;
			ensure_users();
			bool private_output = true;
			for (auto bit : input) {
				if (protected_bits.count(bit)) private_output = false;
				for (auto user : reversed(users[bit])) if (user != reduce) private_output = false;
			}
			if (!private_output) continue;
			auto a = sigmap(pmux->getPort(ID::A)), b = sigmap(pmux->getPort(ID::B)), s = sigmap(pmux->getPort(ID::S));
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
