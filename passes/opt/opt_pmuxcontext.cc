// opt_pmuxcontext 按选择条件化简有界逻辑锥，并利用加法截断与模同余关系消除重复选择和运算。
// 复用端口分类，在局部化简后按结构成本提交变换。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/pmux_celltypes.h"
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ContextAnalysisScope {
	static bool active;
	int first = autoidx;
	GarbageCollectionGuard gc_guard{false};
	ContextAnalysisScope() {
		log_assert(!active && !Multithreading::active());
		active = true;
	}
	ContextAnalysisScope(const ContextAnalysisScope &) = delete;
	ContextAnalysisScope &operator=(const ContextAnalysisScope &) = delete;
	void persistent(IdString id) const { log_assert(id.index_ > -first); }
	~ContextAnalysisScope() {
		log_assert(active && !Multithreading::active() && !GarbageCollectionGuard::is_enabled());
		int last = autoidx;
		log_assert(last >= first);
		// 局部 Design 与全部映射已析构，释放本次临时自动名称。
		for (int index = first; index < last; index++) {
			log_assert(!IdString::global_refcount_storage_.count(-index));
			IdString::global_autoidx_id_storage_.erase(-index);
		}
		autoidx = Autoidx(first);
		active = false;
		log_debug("PMUX context analysis: first=%d temporary=%d restored=%d.\n", first, last-first, int(autoidx));
	}
};
bool ContextAnalysisScope::active = false;

struct ContextPlan {
	struct Bit { SigBit external; int local = -1; };
	struct CellData {
		IdString type;
		dict<IdString, Const> parameters, attributes;
		std::vector<std::pair<IdString, std::vector<Bit>>> ports;
	};
	std::vector<CellData> cells;
	std::vector<Bit> outputs;
	int local_bits = 0;
};

struct PmuxContextWorker {
	Module *module;
	SigMap sigmap;
	PmuxCellTypes types;
	dict<SigBit, Cell *> drivers;
	dict<SigBit, pool<Cell *>> users;
	bool users_built = false;
	pool<SigBit> protected_bits, kept_bits;
	pool<Cell *> selected, removed;
	dict<std::pair<SigBit, bool>, dict<SigBit, State>> condition_cache;
	struct ConeSummary {
		std::vector<SigBit> dependencies;
		int work = 0;
	};
	dict<SigSpec, ConeSummary> cone_cache;
	int cached_cone_bits = 0;
	int cached_facts = 0, cache_hits = 0, cache_insertions = 0, cache_clears = 0;
	int changes = 0, copies = 0, total_budget = 262144;
	static constexpr int max_bits = 4096, max_cells = 64, max_depth = 16;

	PmuxContextWorker(Module *module, Design *design) : module(module), sigmap(module), types(module, design)
	{
		for (auto wire : module->wires()) {
			bool keep = wire->get_bool_attribute(ID::keep);
			if (!wire->port_input && !wire->port_output && !keep) continue;
			for (auto bit : sigmap(wire)) {
				if (wire->port_input) drivers[bit] = nullptr;
				if (wire->port_output || keep) protected_bits.insert(bit);
				if (keep) kept_bits.insert(bit);
			}
		}
		for (auto cell : module->cells()) {
			if (design->selected(module, cell)) selected.insert(cell);
			bool keep = cell->get_bool_attribute(ID::keep);
			for (auto &port : cell->connections()) {
				auto direction = types.cell_port_dir(cell->type, port.first);
				bool input = direction == RTLIL::PD_INPUT || direction == RTLIL::PD_INOUT;
				bool output = direction == RTLIL::PD_OUTPUT || direction == RTLIL::PD_INOUT;
				for (auto bit : sigmap(port.second)) {
					if (output) {
						if (drivers.count(bit)) drivers[bit] = nullptr;
						else drivers[bit] = cell;
					}
					if ((!input && !output) || keep) {
						protected_bits.insert(bit);
						kept_bits.insert(bit);
						if (!input && !output) drivers[bit] = nullptr;
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
			bool input = direction == RTLIL::PD_INPUT || direction == RTLIL::PD_INOUT;
			bool output = direction == RTLIL::PD_OUTPUT || direction == RTLIL::PD_INOUT;
			if (input || !output)
				for (auto bit : sigmap(port.second)) users[bit].insert(cell);
		}
		users_built = true;
	}

	Cell *driver(SigBit bit)
	{
		if (!bit.wire) return nullptr;
		auto found = drivers.find(bit);
		if (found == drivers.end()) return nullptr;
		auto cell = found->second;
		return removed.count(cell) ? nullptr : cell;
	}

	struct Eligibility { dict<Cell *, bool> editable, supported; };
	bool editable(Cell *cell, Eligibility *eligibility = nullptr)
	{
		if (!cell) return false;
		if (eligibility && eligibility->editable.count(cell)) return eligibility->editable.at(cell);
		auto check = [&]() {
			if (removed.count(cell) || !selected.count(cell) || cell->get_bool_attribute(ID::keep) || !cell->hasPort(ID::Y)) return false;
			for (auto original : cell->getPort(ID::Y)) {
				auto bit = sigmap(original);
				if (kept_bits.count(bit) || driver(bit) != cell) return false;
			}
			return true;
		};
		bool result = check();
		if (eligibility) eligibility->editable[cell] = result;
		return result;
	}

	bool supported(Cell *cell, Eligibility &eligibility)
	{
		if (!cell) return false;
		if (eligibility.supported.count(cell)) return eligibility.supported.at(cell);
		bool result = cell->hasPort(ID::Y) && GetSize(cell->getPort(ID::Y)) <= max_bits &&
			editable(cell, &eligibility) && cell->type.in(ID($mux), ID($pmux), ID($add), ID($sub), ID($and), ID($or), ID($xor), ID($xnor),
			ID($not), ID($pos), ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and),
			ID($logic_or), ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor));
		eligibility.supported[cell] = result;
		return result;
	}

	int cost(Cell *cell)
	{
		int width = GetSize(cell->getPort(ID::Y));
		if (cell->type == ID($pmux)) return width * GetSize(cell->getPort(ID::S));
		if (cell->type.in(ID($add), ID($sub))) return width * 2;
		if (cell->type.in(ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge)))
			return std::max(GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::B)));
		if (cell->type.in(ID($logic_not), ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor)))
			return GetSize(cell->getPort(ID::A));
		return width;
	}

	bool spend(int &budget, int amount = 1)
	{
		budget -= amount;
		total_budget -= amount;
		return budget >= 0 && total_budget >= 0;
	}

	bool spend_ports(Cell *cell, int &budget)
	{
		for (auto port : {ID::A, ID::B, ID::S, ID::Y}) if (cell->hasPort(port)) {
			int width = GetSize(cell->getPort(port));
			if (width > max_bits || !spend(budget, width)) return false;
		}
		return true;
	}

	bool fact(dict<SigBit, State> &facts, SigBit bit, State value)
	{
		if (!bit.wire) return bit.data == value;
		auto found = facts.find(bit);
		if (found != facts.end()) return found->second == value;
		facts[bit] = value;
		return true;
	}

	bool condition(SigBit bit, bool value, dict<SigBit, State> &facts, int &budget, int depth = 0)
	{
		if (depth > 8 || !spend(budget)) return false;
		if (!fact(facts, bit, value ? State::S1 : State::S0)) return false;
		if (!bit.wire) return true;
		auto cell = driver(bit);
		if (!cell || !cell->hasPort(ID::Y) || sigmap(cell->getPort(ID::Y)) != SigSpec(bit)) return true;
		if (!cell->type.in(ID($logic_not), ID($not), ID($reduce_or), ID($reduce_bool), ID($reduce_and),
			ID($eq), ID($ne), ID($logic_and), ID($logic_or), ID($and), ID($or), ID($xor), ID($xnor))) return true;
		if (!spend(budget, GetSize(cell->getPort(ID::A)))) return false;
		auto a = sigmap(cell->getPort(ID::A));
		if (GetSize(a) == 1) {
			if (cell->type.in(ID($not), ID($logic_not)))
				return condition(a[0], !value, facts, budget, depth + 1);
			if (cell->type.in(ID($reduce_or), ID($reduce_bool), ID($reduce_and)))
				return condition(a[0], value, facts, budget, depth + 1);
		}
		if ((cell->type == ID($logic_not) && value) || (cell->type.in(ID($reduce_or), ID($reduce_bool)) && !value) ||
			(cell->type == ID($reduce_and) && value)) {
			State v = cell->type == ID($reduce_and) ? State::S1 : State::S0;
			for (auto input : a) if (!fact(facts, input, v)) return false;
			return true;
		}
		if (cell->type.in(ID($eq), ID($ne))) {
			if (!spend(budget, GetSize(cell->getPort(ID::B)))) return false;
			auto b = sigmap(cell->getPort(ID::B));
			if (a.is_fully_const()) std::swap(a, b);
			if (GetSize(a) == 1 && GetSize(b) == 1 && b.is_fully_def()) {
				bool equal = cell->type == ID($eq) ? value : !value;
				bool expected = equal ? b[0] == State::S1 : b[0] == State::S0;
				return condition(a[0], expected, facts, budget, depth + 1);
			}
			if (!((cell->type == ID($eq) && value) || (cell->type == ID($ne) && !value))) return true;
			if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool()) return true;
			if (!b.is_fully_def()) return true;
			int width = std::max(GetSize(a), GetSize(b));
			a.extend_u0(width);
			b.extend_u0(width);
			for (int i = 0; i < width; i++) if (!fact(facts, a[i], b[i].data)) return false;
			return true;
		}
		if (cell->type.in(ID($logic_and), ID($logic_or), ID($and), ID($or), ID($xor), ID($xnor))) {
			if (!spend(budget, GetSize(cell->getPort(ID::B)))) return false;
			auto b = sigmap(cell->getPort(ID::B));
			if (GetSize(a) != 1 || GetSize(b) != 1) return true;
			if (a.is_fully_const()) std::swap(a, b);
			if (b.is_fully_def()) {
				bool fixed = b[0] == State::S1;
				if (cell->type.in(ID($and), ID($logic_and))) {
					if (!fixed) return !value;
				} else if (cell->type.in(ID($or), ID($logic_or))) {
					if (fixed) return value;
				} else if (cell->type == ID($xor)) {
					value ^= fixed;
				} else {
				log_assert(cell->type == ID($xnor));
					value ^= !fixed;
				}
				return condition(a[0], value, facts, budget, depth + 1);
			}
			if ((cell->type.in(ID($and), ID($logic_and)) && value) ||
				(cell->type.in(ID($or), ID($logic_or)) && !value))
				return condition(a[0], value, facts, budget, depth + 1) && condition(b[0], value, facts, budget, depth + 1);
		}
		return true;
	}

	bool condition_facts(SigBit bit, bool value, dict<SigBit, State> &facts, int &budget)
	{
		log_assert(facts.empty());
		bit = sigmap(bit);
		auto key = std::make_pair(bit, value);
		auto found = condition_cache.find(key);
		if (found != condition_cache.end()) {
			if (!spend(budget, 1 + GetSize(found->second))) return false;
			facts = found->second;
			cache_hits++;
			return true;
		}
		if (!condition(bit, value, facts, budget)) return false;
		int count = GetSize(facts);
		if (GetSize(condition_cache) < 64 && cached_facts + count <= 4096 && count <= budget && count <= total_budget) {
			bool available = spend(budget, count);
			log_assert(available);
			condition_cache[key] = facts;
			cached_facts += count;
			cache_insertions++;
		}
		return true;
	}

	void invalidate_caches()
	{
		condition_cache.clear();
		cached_facts = 0;
		cone_cache.clear();
		cached_cone_bits = 0;
		cache_clears++;
	}

	struct ConeTrace {
		pool<SigBit> dependencies;
		int limit;
		bool complete = true;
		ConeTrace(int limit) : limit(limit) {}
		void record(SigBit bit)
		{
			if (!complete || dependencies.count(bit)) return;
			if (GetSize(dependencies) >= limit) {
				complete = false;
				dependencies.clear();
				return;
			}
			dependencies.insert(bit);
		}
	};

	bool cone(SigBit bit, const dict<SigBit, State> &facts, pool<Cell *> &cells, pool<Cell *> &active,
		pool<SigBit> &leaves, bool &affected, int &budget, Eligibility &eligibility, ConeTrace *trace = nullptr, int depth = 0)
	{
		if (!spend(budget) || depth > max_depth) return false;
		if (!bit.wire) return true;
		if (trace) trace->record(bit);
		if (facts.count(bit)) {
			affected = true;
			return true;
		}
		auto cell = driver(bit);
		if (!supported(cell, eligibility)) {
			leaves.insert(bit);
			return true;
		}
		if (active.count(cell)) return false;
		if (cells.count(cell)) return true;
		if (GetSize(cells) >= max_cells) return false;
		if (!spend(budget, GetSize(cell->getPort(ID::Y)))) return false;
		active.insert(cell);
		for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first))
			for (auto input : port.second) if (!cone(sigmap(input), facts, cells, active, leaves, affected, budget, eligibility, trace, depth+1)) return false;
		active.erase(cell);
		cells.insert(cell);
		return true;
	}

	pool<Cell *> deletable(const pool<Cell *> &cells, Cell *consumer, IdString port, int offset, int width,
		const pool<SigBit> &retained, int &budget, Eligibility *eligibility = nullptr)
	{
		auto result = cells;
		if (!result.empty()) ensure_users();
		bool changed;
		do {
			changed = false;
			for (auto cell : std::vector<Cell *>(result.begin(), result.end())) {
				bool keep = !editable(cell, eligibility);
				for (auto original : cell->getPort(ID::Y)) {
					auto bit = sigmap(original);
					if (!spend(budget)) return {};
					if (protected_bits.count(bit) || retained.count(bit)) keep = true;
					auto found = users.find(bit);
					if (found == users.end()) continue;
					for (auto user : found->second) {
						if (!spend(budget)) return {};
						if (removed.count(user) || result.count(user)) continue;
						for (auto &use : user->connections()) if (!types.cell_output(user->type, use.first)) {
							auto &signal = use.second;
							if (!spend(budget, GetSize(signal))) return {};
							for (int i = 0; i < GetSize(signal); i++) if (sigmap(signal[i]) == bit &&
								!(user == consumer && use.first == port && i >= offset && i < offset+width)) keep = true;
						}
					}
				}
				if (keep) {
					result.erase(cell);
					changed = true;
				}
			}
		} while (changed);
		return result;
	}

	void index_inputs(Cell *cell)
	{
		log_assert(users_built);
		for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first))
			for (auto bit : sigmap(port.second)) users[bit].insert(cell);
	}

	std::unique_ptr<ContextPlan> analyze(const SigSpec &original, const pool<Cell *> &cells,
		const pool<SigBit> &leaves, const dict<SigBit, State> &facts, int old_cost)
	{
		ContextAnalysisScope scope;
		Design local_design;
		auto local = local_design.addModule(NEW_ID);
		dict<SigBit, SigBit> mapping, reverse;
		auto mapbit = [&](SigBit bit) -> SigBit {
			if (!bit.wire) return bit;
			if (facts.count(bit)) return SigBit(facts.at(bit));
			if (!mapping.count(bit)) {
				auto wire = local->addWire(NEW_ID);
				mapping[bit] = SigBit(wire);
				if (leaves.count(bit)) {
					wire->port_input = true;
					reverse[SigBit(wire)] = bit;
				}
			}
			return mapping.at(bit);
		};
		for (auto cell : cells) {
			auto copy = local->addCell(NEW_ID, cell);
			copy->attributes.clear();
			for (auto &port : cell->connections()) {
				SigSpec signal;
				for (auto bit : sigmap(port.second)) {
					if (types.cell_output(cell->type, port.first) && facts.count(bit)) signal.append(local->addWire(NEW_ID));
					else signal.append(mapbit(bit));
				}
				copy->setPort(port.first, signal);
			}
		}
		auto output = local->addWire(NEW_ID, GetSize(original));
		output->port_output = true;
		SigSpec result;
		for (auto bit : original) result.append(mapbit(bit));
		local->connect(output, result);
		local->fixup_ports();
		copies++;
		Pass::call_on_module(&local_design, local, "opt_expr -fine");
		Pass::call_on_module(&local_design, local, "opt_reduce");
		Pass::call_on_module(&local_design, local, "opt_expr -fine");
		Pass::call_on_module(&local_design, local, "opt_clean");
		SigMap local_map(local);
		dict<SigBit, SigBit> imported;
		for (auto &leaf : reverse) imported[local_map(leaf.first)] = leaf.second;
		int new_cost = 0;
		for (auto cell : local->cells()) new_cost += cost(cell);
		if (new_cost >= old_cost) return nullptr;
		auto plan = std::make_unique<ContextPlan>();
		plan->cells.reserve(local->cells_size());
		dict<SigBit, int> local_bits;
		auto exportbit = [&](SigBit bit) -> ContextPlan::Bit {
			bit = local_map(bit);
			if (!bit.wire) return {bit, -1};
			auto found = imported.find(bit);
			if (found != imported.end()) {
				log_assert(!found->second.wire || module->wire(found->second.wire->name) == found->second.wire);
				return {found->second, -1};
			}
			if (!local_bits.count(bit)) local_bits[bit] = plan->local_bits++;
			return {SigBit(State::Sx), local_bits.at(bit)};
		};
		for (auto cell : local->cells()) {
			scope.persistent(cell->type);
			plan->cells.emplace_back();
			auto &record = plan->cells.back();
			record.type = cell->type;
			for (auto &entry : cell->parameters) { scope.persistent(entry.first); record.parameters[entry.first] = entry.second; }
			for (auto &entry : cell->attributes) { scope.persistent(entry.first); record.attributes[entry.first] = entry.second; }
			for (auto &p : cell->connections()) {
				scope.persistent(p.first);
				record.ports.emplace_back(p.first, std::vector<ContextPlan::Bit>());
				for (auto bit : p.second) record.ports.back().second.push_back(exportbit(bit));
			}
		}
		for (auto bit : SigSpec(output)) plan->outputs.push_back(exportbit(bit));
		log_debug("PMUX context plan: original=%d candidate=%d cells=%d local_bits=%d.\n", old_cost, new_cost, GetSize(plan->cells), plan->local_bits);
		return plan;
	}

	void specialize(Cell *consumer, IdString port, int offset, int width, dict<SigBit, State> &facts)
	{
		if (facts.empty() || copies >= 64 || total_budget <= 0) return;
		int budget = max_bits;
		auto original = sigmap(consumer->getPort(port).extract(offset, width));
		auto cached = cone_cache.find(original);
		// 完整遍历的消耗必须同时满足两个预算，才能省略逐次扣费。
		if (cached != cone_cache.end() && cached->second.work <= budget && cached->second.work <= total_budget) {
			bool intersects = false;
			for (auto &entry : facts)
				if (std::binary_search(cached->second.dependencies.begin(), cached->second.dependencies.end(), entry.first)) {
					intersects = true;
					break;
				}
			if (!intersects) {
				bool available = spend(budget, cached->second.work);
				log_assert(available);
				return;
			}
		}
		bool record = cached == cone_cache.end() && GetSize(cone_cache) < 64 && cached_cone_bits + GetSize(original) <= max_bits;
		ConeTrace trace(record ? max_bits - cached_cone_bits - GetSize(original) : 0);
		pool<Cell *> cells, active, deleted;
		pool<SigBit> leaves;
		{
			Eligibility eligibility;
			bool affected = false, has_pmux = false;
			for (auto bit : original) if (!cone(bit, facts, cells, active, leaves, affected, budget, eligibility, record ? &trace : nullptr)) return;
			if (!affected) {
				if (record && trace.complete) {
					ConeSummary summary;
					summary.dependencies.assign(trace.dependencies.begin(), trace.dependencies.end());
					std::sort(summary.dependencies.begin(), summary.dependencies.end());
					summary.work = max_bits - budget;
					cached_cone_bits += GetSize(original) + GetSize(summary.dependencies);
					cone_cache[original] = std::move(summary);
				}
				return;
			}
			for (auto cell : cells) if (cell->type == ID($pmux)) has_pmux = true;
			if (!has_pmux) return;
			deleted = deletable(cells, consumer, port, offset, width, leaves, budget, &eligibility);
		}
		int old_cost = 0;
		for (auto cell : deleted) old_cost += cost(cell);
		if (!old_cost || budget < 0) return;
		auto plan = analyze(original, cells, leaves, facts, old_cost);
		if (!plan) return;
		log_assert(!ContextAnalysisScope::active);
		std::vector<SigBit> imported(plan->local_bits);
		auto importbit = [&](const ContextPlan::Bit &bit) -> SigBit {
			if (bit.local < 0) {
				log_assert(!bit.external.wire || module->wire(bit.external.wire->name) == bit.external.wire);
				return bit.external;
			}
			log_assert(bit.local < plan->local_bits && !bit.external.wire);
			auto &result = imported[bit.local];
			if (!result.wire) result = SigBit(module->addWire(NEW_ID));
			return result;
		};
		for (auto &record : plan->cells) {
			auto copy = module->addCell(NEW_ID, record.type);
			copy->parameters = record.parameters;
			copy->attributes = record.attributes;
			for (auto &p : record.ports) {
				SigSpec signal;
				for (auto &bit : p.second) signal.append(importbit(bit));
				copy->setPort(p.first, signal);
			}
			index_inputs(copy);
		}
		SigSpec replacement;
		for (auto &bit : plan->outputs) replacement.append(importbit(bit));
		log_assert(GetSize(replacement) == width);
		auto signal = consumer->getPort(port);
		signal.replace(offset, replacement);
		consumer->setPort(port, signal);
		index_inputs(consumer);
		for (auto cell : deleted) removed.insert(cell);
		changes++;
		invalidate_caches();
	}

	struct Relation {
		bool valid = false, selection = false;
		SigSpec base;
		Const residue, upper;
		pool<Cell *> cells;
	};

	SigSpec trim(SigSpec signal)
	{
		while (GetSize(signal) > 1 && signal.back() == State::S0) signal.remove(GetSize(signal)-1);
		return signal;
	}

	Const maximum(const SigSpec &signal)
	{
		Const result(State::S0, GetSize(signal));
		for (int i = 0; i < GetSize(signal); i++) if (signal[i] != State::S0) result.set(i, State::S1);
		return result;
	}

	bool zero(const Const &value) { return value.is_fully_def() && value.is_fully_zero(); }

	Relation relation(SigSpec signal, const Const &modulus, pool<Cell *> &active, int &budget, int depth = 0)
	{
		Relation result;
		if (depth > max_depth || !spend(budget, GetSize(signal)) || signal.empty()) return result;
		signal = trim(sigmap(signal));
		auto cell = driver(signal[0]);
		if (cell && cell->hasPort(ID::Y) && GetSize(cell->getPort(ID::Y)) > max_bits) return result;
		bool supported_type = cell && cell->type.in(ID($add), ID($pos), ID($mux), ID($pmux));
		if (supported_type && !spend_ports(cell, budget)) return result;
		if (!supported_type || !editable(cell) || sigmap(cell->getPort(ID::Y)) != signal) {
			if (!signal.is_fully_def() && signal.is_fully_const()) return result;
			result.valid = true;
			result.base = signal;
			result.residue = Const(State::S0, GetSize(modulus));
			result.upper = maximum(signal);
			return result;
		}
		if (!active.insert(cell).second || GetSize(active) > max_cells) return result;
		if (cell->type.in(ID($add), ID($pos))) {
			if (cell->getParam(ID::A_SIGNED).as_bool() || (cell->hasPort(ID::B) && cell->getParam(ID::B_SIGNED).as_bool())) {
				active.erase(cell);
				return result;
			}
			auto a = sigmap(cell->getPort(ID::A));
			SigSpec b = cell->hasPort(ID::B) ? sigmap(cell->getPort(ID::B)) : SigSpec(State::S0);
			if (a.is_fully_const()) std::swap(a, b);
			if (!b.is_fully_def()) {
				active.erase(cell);
				return result;
			}
			result = relation(a, modulus, active, budget, depth+1);
			if (result.valid) {
				int width = GetSize(signal), calc_width = std::max({width, GetSize(a), GetSize(b), GetSize(result.upper), GetSize(modulus)})+2;
				auto sum = const_add(result.upper, b.as_const(), false, false, calc_width);
				Const capacity(State::S0, calc_width);
				capacity.set(width, State::S1);
				bool no_overflow = const_lt(sum, capacity, false, false, 1).as_bool();
				if (!no_overflow && !zero(const_mod(capacity, modulus, false, false, calc_width))) result.valid = false;
				else {
					result.upper = no_overflow ? sum : Const(State::S1, width);
					result.residue = const_mod(const_add(result.residue, b.as_const(), false, false, calc_width), modulus, false, false, GetSize(modulus));
					result.cells.insert(cell);
				}
			}
		} else {
			auto s = sigmap(cell->getPort(ID::S)), a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B));
			int count = cell->type == ID($mux) ? 1 : GetSize(s);
			if (count > 16) {
				active.erase(cell);
				return result;
			}
			std::vector<SigSpec> branches;
			if (!a.is_fully_undef()) branches.push_back(a);
			for (int i = 0; i < count; i++) branches.push_back(b.extract(i*GetSize(a), GetSize(a)));
			bool first = true;
			for (auto branch : branches) {
				auto next = relation(branch, modulus, active, budget, depth+1);
				if (!next.valid || (!first && (result.base != next.base || result.residue != next.residue))) {
					result.valid = false;
					break;
				}
				if (first) {
					result = next;
					first = false;
				}
				else {
					result.cells.insert(next.cells.begin(), next.cells.end());
					if (const_lt(result.upper, next.upper, false, false, 1).as_bool()) result.upper = next.upper;
				}
			}
			if (first) result.valid = false;
			if (result.valid) {
				result.selection = true;
				result.cells.insert(cell);
			}
		}
		active.erase(cell);
		if (GetSize(result.cells) > max_cells) result.valid = false;
		return result;
	}

	void modulo(Cell *cell)
	{
		if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool()) return;
		int budget = max_bits;
		if (!spend_ports(cell, budget) || !editable(cell)) return;
		auto modulus = sigmap(cell->getPort(ID::B));
		if (!modulus.is_fully_def() || modulus.empty() || modulus.is_fully_zero() || GetSize(modulus) > max_bits) return;
		pool<Cell *> active;
		auto old = sigmap(cell->getPort(ID::A));
		auto result = relation(old, modulus.as_const(), active, budget);
		if (!result.valid || !result.selection || !zero(result.residue) || result.base == old) return;
		pool<SigBit> retained;
		for (auto bit : result.base) retained.insert(bit);
		auto deleted = deletable(result.cells, cell, ID::A, 0, GetSize(old), retained, budget);
		int old_cost = 0;
		for (auto old_cell : deleted) old_cost += cost(old_cell);
		if (!old_cost || budget < 0 || GetSize(result.base) > GetSize(old)) return;
		cell->setPort(ID::A, result.base);
		cell->setParam(ID::A_WIDTH, GetSize(result.base));
		index_inputs(cell);
		for (auto old_cell : deleted) removed.insert(old_cell);
		changes++;
		invalidate_caches();
	}

	void run()
	{
		std::vector<Cell *> candidates;
		for (auto cell : module->cells())
			if (cell->type.in(ID($mux), ID($pmux), ID($mod), ID($modfloor))) candidates.push_back(cell);
		for (auto cell : candidates) {
			if (total_budget <= 0) break;
			if (cell->type.in(ID($mod), ID($modfloor))) {
				modulo(cell);
				continue;
			}
			if (!editable(cell)) continue;
			auto s = sigmap(cell->getPort(ID::S));
			int width = GetSize(cell->getPort(ID::A));
			if (GetSize(s) > 16 || width > max_bits) continue;
			bool mux = cell->type == ID($mux);
			int count = mux ? 2 : GetSize(s);
			for (int index = 0; index < count; index++) {
				bool value = !mux || index != 0;
				auto bit = s[mux ? 0 : index];
				dict<SigBit, State> facts;
				int budget = max_bits;
				if (condition_facts(bit, value, facts, budget))
					specialize(cell, value ? ID::B : ID::A, mux ? 0 : index*width, width, facts);
			}
		}
		for (auto cell : removed) module->remove(cell);
		if (cache_hits || cache_insertions || cache_clears)
			log("opt_pmuxcontext %s: condition_cache_hits=%d insertions=%d clears=%d commits=%d.\n",
				log_id(module), cache_hits, cache_insertions, cache_clears, changes);
	}
};

struct OptPmuxContextPass : public Pass {
	OptPmuxContextPass() : Pass("opt_pmuxcontext", "specialize observed PMUX cones and constant modulo relations") {}
	void help() override {
		log("    opt_pmuxcontext [selection]\n\n");
		log("Specialize bounded PMUX cones under constant input facts from their observation conditions.\n");
		log("Reduce unsigned constant-modulus PMUX inputs after proving every addition's truncation.\n");
		log("Only strictly cheaper private structures are replaced. Undefined regions may be refined.\n");
	}
	void execute(std::vector<std::string> args, Design *design) override {
		extra_args(args, 1, design);
		for (auto module : design->selected_modules()) {
			bool candidate = false;
			for (auto cell : module->selected_cells()) if (cell->type.in(ID($pmux), ID($mod), ID($modfloor))) {
				candidate = true;
				break;
			}
			if (!candidate) continue;
			bool whole = design->selected_whole_module(module);
			int changes;
			{
				PmuxContextWorker worker(module, design);
				worker.run();
				changes = worker.changes;
			}
			if (changes && whole) {
				Pass::call_on_module(design, module, "opt_expr -fine");
				Pass::call_on_module(design, module, "opt_clean");
			}
		}
	}
} OptPmuxContextPass;

PRIVATE_NAMESPACE_END
