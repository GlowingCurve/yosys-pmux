// opt_pmuxcontext 按选择条件化简有界逻辑锥，并利用加法截断与模同余关系消除重复选择和运算。
// 复用端口分类，在局部化简后按结构成本提交变换。
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/pmux_decoder.h"
#include "passes/opt/pmux_netlist.h"
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
	PmuxNetlist netlist;
	PmuxDecoder decoder;
	pool<Cell *> removed;
	struct ConeSummary {
		std::vector<SigBit> dependencies;
		int work = 0;
	};
	dict<SigSpec, ConeSummary> cone_cache;
	int cached_cone_bits = 0;
	int changes = 0, copies = 0, total_budget = 262144;
	static constexpr int max_bits = 4096, max_cells = 64, max_depth = 16;

	PmuxContextWorker(Module *module, Design *design) : module(module), netlist(module, design), decoder(netlist) {}

	bool supported(Cell *cell, dict<Cell *, bool> &eligibility)
	{
		log_assert(cell);
		auto cached = eligibility.find(cell);
		if (cached != eligibility.end()) return cached->second;
		bool result = cell->hasPort(ID::Y) && GetSize(cell->getPort(ID::Y)) <= max_bits &&
			netlist.editable(cell) && cell->type.in(ID($mux), ID($pmux), ID($add), ID($sub), ID($and), ID($or), ID($xor), ID($xnor),
			ID($not), ID($pos), ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and),
			ID($logic_or), ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor));
		eligibility[cell] = result;
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
		pool<SigBit> &leaves, bool &affected, int &budget, dict<Cell *, bool> &eligibility, ConeTrace *trace, int depth = 0)
	{
		if (!spend(budget) || depth > max_depth) return false;
		if (!bit.wire) return true;
		if (trace) trace->record(bit);
		if (facts.count(bit)) {
			affected = true;
			return true;
		}
		auto cell = netlist.driver(bit);
		if (!cell || !supported(cell, eligibility)) {
			leaves.insert(bit);
			return true;
		}
		if (active.count(cell)) return false;
		if (cells.count(cell)) return true;
		if (GetSize(cells) >= max_cells) return false;
		if (!spend(budget, GetSize(cell->getPort(ID::Y)))) return false;
		active.insert(cell);
		for (auto &port : cell->connections()) if (netlist.cell_input(cell->type, port.first))
			for (auto input : netlist.port(cell, port.first))
				if (!cone(input, facts, cells, active, leaves, affected, budget, eligibility, trace, depth+1)) return false;
		active.erase(cell);
		cells.insert(cell);
		return true;
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
				for (auto bit : netlist.port(cell, port.first)) {
					if (netlist.cell_output(cell->type, port.first) && facts.count(bit)) signal.append(local->addWire(NEW_ID));
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

	void specialize(Cell *consumer, IdString port, int offset, int width, const dict<SigBit, State> &facts)
	{
		if (facts.empty() || copies >= 64 || total_budget <= 0) return;
		int budget = max_bits;
		auto original = netlist.port(consumer, port).extract(offset, width);
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
			dict<Cell *, bool> eligibility;
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
			int pruning_budget = std::min(budget, total_budget), initial_budget = pruning_budget;
			deleted = netlist.private_cells(cells, {}, {}, leaves, &pruning_budget, {consumer, port, offset, width});
			spend(budget, initial_budget - pruning_budget);
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
			netlist.register_cell(copy);
		}
		SigSpec replacement;
		for (auto &bit : plan->outputs) replacement.append(importbit(bit));
		log_assert(GetSize(replacement) == width);
		auto signal = consumer->getPort(port);
		signal.replace(offset, replacement);
		netlist.set_port(consumer, port, signal);
		for (auto cell : deleted) {
			netlist.forget_cell(cell);
			removed.insert(cell);
		}
		changes++;
		cone_cache.clear();
		cached_cone_bits = 0;
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
		signal = trim(signal);
		auto cell = netlist.driver(signal[0]);
		if (cell && cell->hasPort(ID::Y) && GetSize(cell->getPort(ID::Y)) > max_bits) return result;
		bool supported_type = cell && cell->type.in(ID($add), ID($pos), ID($mux), ID($pmux));
		if (supported_type && !spend_ports(cell, budget)) return result;
		if (!supported_type || !netlist.editable(cell) || netlist.port(cell, ID::Y) != signal) {
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
			auto a = netlist.port(cell, ID::A);
			SigSpec b = cell->hasPort(ID::B) ? netlist.port(cell, ID::B) : SigSpec(State::S0);
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
			const auto &s = netlist.port(cell, ID::S), &a = netlist.port(cell, ID::A), &b = netlist.port(cell, ID::B);
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
		if (!spend_ports(cell, budget) || !netlist.editable(cell)) return;
		const auto &modulus = netlist.port(cell, ID::B);
		if (!modulus.is_fully_def() || modulus.empty() || modulus.is_fully_zero() || GetSize(modulus) > max_bits) return;
		pool<Cell *> active;
		auto old = netlist.port(cell, ID::A);
		auto result = relation(old, modulus.as_const(), active, budget);
		if (!result.valid || !result.selection || !zero(result.residue) || result.base == old) return;
		pool<SigBit> retained;
		for (auto bit : result.base) retained.insert(bit);
		int pruning_budget = std::min(budget, total_budget), initial_budget = pruning_budget;
		auto deleted = netlist.private_cells(result.cells, {}, {}, retained, &pruning_budget, {cell, ID::A, 0, GetSize(old)});
		spend(budget, initial_budget - pruning_budget);
		int old_cost = 0;
		for (auto old_cell : deleted) old_cost += cost(old_cell);
		if (!old_cost || budget < 0 || GetSize(result.base) > GetSize(old)) return;
		netlist.set_port(cell, ID::A, result.base);
		cell->setParam(ID::A_WIDTH, GetSize(result.base));
		for (auto old_cell : deleted) {
			netlist.forget_cell(old_cell);
			removed.insert(old_cell);
		}
		changes++;
		cone_cache.clear();
		cached_cone_bits = 0;
	}

	void run()
	{
		std::vector<Cell *> candidates;
		for (auto cell : module->cells())
			if (cell->type.in(ID($mux), ID($pmux), ID($mod), ID($modfloor))) candidates.push_back(cell);
		for (auto cell : candidates) {
			if (total_budget <= 0) break;
			if (removed.count(cell)) continue;
			if (cell->type.in(ID($mod), ID($modfloor))) {
				modulo(cell);
				continue;
			}
			if (!netlist.editable(cell)) continue;
			auto s = netlist.port(cell, ID::S);
			int width = GetSize(cell->getPort(ID::A));
			if (GetSize(s) > 16 || width > max_bits) continue;
			bool mux = cell->type == ID($mux);
			int count = mux ? 2 : GetSize(s);
			for (int index = 0; index < count; index++) {
				bool value = !mux || index != 0;
				auto bit = s[mux ? 0 : index];
				dict<SigBit, State> facts;
				int budget = std::min(max_bits, total_budget), initial_budget = budget;
				bool valid = decoder.condition(bit, value, facts, budget);
				total_budget -= initial_budget - budget;
				if (valid)
					specialize(cell, value ? ID::B : ID::A, mux ? 0 : index*width, width, facts);
			}
		}
		for (auto cell : removed) module->remove(cell);
		if (changes)
			log("opt_pmuxcontext %s: specialized %d cones.\n", log_id(module), changes);
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
