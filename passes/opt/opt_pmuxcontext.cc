#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
// opt_pmuxcontext 按选择条件化简有界逻辑锥并消除可证明的模运算冗余；复用端口分类，仅提交成本下降的变换。
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxContextWorker {
	Module *module;
	Design *design;
	SigMap sigmap;
	CellTypes types;
	dict<SigBit, Cell *> drivers;
	dict<SigBit, pool<Cell *>> users;
	pool<SigBit> protected_bits, kept_bits;
	pool<Cell *> selected, removed;
	int changes = 0, copies = 0, total_budget = 262144;
	static constexpr int max_bits = 4096, max_cells = 64, max_depth = 16;

	PmuxContextWorker(Module *module, Design *design) : module(module), design(design), sigmap(module), types(design)
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
				bool input = types.cell_input(cell->type, port.first), output = types.cell_output(cell->type, port.first);
				for (auto bit : sigmap(port.second)) {
					if (output) {
						if (drivers.count(bit)) drivers[bit] = nullptr;
						else drivers[bit] = cell;
					}
					if (input || !output) users[bit].insert(cell);
					if ((!input && !output) || keep) {
						protected_bits.insert(bit); kept_bits.insert(bit);
						if (!input && !output) drivers[bit] = nullptr;
					}
				}
			}
		}
	}

	Cell *driver(SigBit bit)
	{
		if (!bit.wire) return nullptr;
		auto found = drivers.find(bit);
		if (found == drivers.end()) return nullptr;
		auto cell = found->second;
		return removed.count(cell) ? nullptr : cell;
	}

	bool editable(Cell *cell)
	{
		if (!cell || removed.count(cell) || !selected.count(cell) || cell->get_bool_attribute(ID::keep) || !cell->hasPort(ID::Y)) return false;
		for (auto bit : sigmap(cell->getPort(ID::Y))) if (kept_bits.count(bit) || driver(bit) != cell) return false;
		return true;
	}

	bool supported(Cell *cell)
	{
		if (!cell || !cell->hasPort(ID::Y) || GetSize(cell->getPort(ID::Y)) > max_bits) return false;
		return editable(cell) && cell->type.in(ID($mux), ID($pmux), ID($add), ID($sub), ID($and), ID($or), ID($xor), ID($xnor),
			ID($not), ID($pos), ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and),
			ID($logic_or), ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor));
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
		budget -= amount; total_budget -= amount;
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
		if (facts.count(bit)) return facts.at(bit) == value;
		facts[bit] = value;
		return true;
	}

	bool condition(SigBit bit, bool value, dict<SigBit, State> &facts, int &budget, int depth = 0)
	{
		if (depth > 8 || !spend(budget)) return false;
		if (!bit.wire) return bit.data == (value ? State::S1 : State::S0);
		auto cell = driver(bit);
		if (!cell || !cell->hasPort(ID::Y) || sigmap(cell->getPort(ID::Y)) != SigSpec(bit)) return true;
		if (!cell->type.in(ID($logic_not), ID($not), ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($eq), ID($ne), ID($logic_and), ID($logic_or))) return true;
		if (!spend(budget, GetSize(cell->getPort(ID::A)))) return false;
		auto a = sigmap(cell->getPort(ID::A));
		if ((cell->type == ID($logic_not) && value) || (cell->type.in(ID($reduce_or), ID($reduce_bool)) && !value) ||
			(cell->type == ID($reduce_and) && value)) {
			State v = cell->type == ID($reduce_and) ? State::S1 : State::S0;
			for (auto input : a) if (!fact(facts, input, v)) return false;
		} else if ((cell->type == ID($not) || cell->type == ID($logic_not)) && GetSize(a) == 1)
			return condition(a[0], !value, facts, budget, depth+1);
		else if ((cell->type == ID($eq) && value) || (cell->type == ID($ne) && !value)) {
			if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool()) return true;
			if (!spend(budget, GetSize(cell->getPort(ID::B)))) return false;
			auto b = sigmap(cell->getPort(ID::B));
			if (a.is_fully_const()) std::swap(a, b);
			if (!b.is_fully_def()) return true;
			int width = std::max(GetSize(a), GetSize(b));
			a.extend_u0(width); b.extend_u0(width);
			for (int i = 0; i < width; i++) if (!fact(facts, a[i], b[i].data)) return false;
		} else if ((cell->type == ID($logic_and) && value) || (cell->type == ID($logic_or) && !value)) {
			auto b = sigmap(cell->getPort(ID::B));
			if (GetSize(a) == 1 && GetSize(b) == 1)
				return condition(a[0], value, facts, budget, depth+1) && condition(b[0], value, facts, budget, depth+1);
		}
		return true;
	}

	bool cone(SigBit bit, const dict<SigBit, State> &facts, pool<Cell *> &cells, pool<Cell *> &active,
		pool<SigBit> &leaves, bool &affected, int &budget, int depth = 0)
	{
		if (!spend(budget) || depth > max_depth) return false;
		if (!bit.wire) return true;
		if (facts.count(bit)) { affected = true; return true; }
		auto cell = driver(bit);
		if (!supported(cell)) { leaves.insert(bit); return true; }
		if (active.count(cell)) return false;
		if (cells.count(cell)) return true;
		if (GetSize(cells) >= max_cells) return false;
		if (!spend(budget, GetSize(cell->getPort(ID::Y)))) return false;
		active.insert(cell);
		for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first))
			for (auto input : sigmap(port.second)) if (!cone(input, facts, cells, active, leaves, affected, budget, depth+1)) return false;
		active.erase(cell); cells.insert(cell);
		return true;
	}

	pool<Cell *> deletable(const pool<Cell *> &cells, Cell *consumer, IdString port, int offset, int width,
		const pool<SigBit> &retained, int &budget)
	{
		auto result = cells;
		bool changed;
		do {
			changed = false;
			for (auto cell : std::vector<Cell *>(result.begin(), result.end())) {
				bool keep = !editable(cell);
				for (auto bit : sigmap(cell->getPort(ID::Y))) {
					if (!spend(budget)) return {};
					if (protected_bits.count(bit) || retained.count(bit)) keep = true;
					for (auto user : users[bit]) {
						if (!spend(budget)) return {};
						if (removed.count(user) || result.count(user)) continue;
						for (auto &use : user->connections()) if (!types.cell_output(user->type, use.first)) {
							auto signal = sigmap(use.second);
							if (!spend(budget, GetSize(signal))) return {};
							for (int i = 0; i < GetSize(signal); i++) if (signal[i] == bit &&
								!(user == consumer && use.first == port && i >= offset && i < offset+width)) keep = true;
						}
					}
				}
				if (keep) { result.erase(cell); changed = true; }
			}
		} while (changed);
		return result;
	}

	void index_inputs(Cell *cell)
	{
		for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first))
			for (auto bit : sigmap(port.second)) users[bit].insert(cell);
	}

	void specialize(Cell *consumer, IdString port, int offset, int width, dict<SigBit, State> &facts)
	{
		if (facts.empty() || copies >= 64 || total_budget <= 0) return;
		int budget = max_bits;
		auto original = sigmap(consumer->getPort(port)).extract(offset, width);
		pool<Cell *> cells, active;
		pool<SigBit> leaves;
		bool affected = false, has_pmux = false;
		for (auto bit : original) if (!cone(bit, facts, cells, active, leaves, affected, budget)) return;
		for (auto cell : cells) if (cell->type == ID($pmux)) has_pmux = true;
		if (!affected || !has_pmux) return;
		auto deleted = deletable(cells, consumer, port, offset, width, leaves, budget);
		int old_cost = 0;
		for (auto cell : deleted) old_cost += cost(cell);
		if (!old_cost || budget < 0) return;

		Design local_design;
		auto local = local_design.addModule(NEW_ID);
		dict<SigBit, SigBit> mapping, reverse;
		auto mapbit = [&](SigBit bit) -> SigBit {
			if (!bit.wire) return bit;
			if (facts.count(bit)) return SigBit(facts.at(bit));
			if (!mapping.count(bit)) {
				auto wire = local->addWire(NEW_ID);
				mapping[bit] = SigBit(wire);
				if (leaves.count(bit)) { wire->port_input = true; reverse[SigBit(wire)] = bit; }
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
		auto output = local->addWire(NEW_ID, width); output->port_output = true;
		SigSpec result;
		for (auto bit : original) result.append(mapbit(bit));
		local->connect(output, result); local->fixup_ports(); copies++;
		Pass::call_on_module(&local_design, local, "opt_expr -fine");
		Pass::call_on_module(&local_design, local, "opt_reduce");
		Pass::call_on_module(&local_design, local, "opt_expr -fine");
		Pass::call_on_module(&local_design, local, "opt_clean");
		SigMap local_map(local);
		dict<SigBit, SigBit> imported;
		for (auto &leaf : reverse) imported[local_map(leaf.first)] = leaf.second;
		int new_cost = 0;
		for (auto cell : local->cells()) new_cost += cost(cell);
		if (new_cost >= old_cost) return;
		auto importbit = [&](SigBit bit) -> SigBit {
			bit = local_map(bit);
			if (!bit.wire) return bit;
			if (!imported.count(bit)) imported[bit] = SigBit(module->addWire(NEW_ID));
			return imported.at(bit);
		};
		for (auto cell : local->cells()) {
			auto copy = module->addCell(NEW_ID, cell);
			for (auto &p : cell->connections()) {
				SigSpec signal;
				for (auto bit : p.second) signal.append(importbit(bit));
				copy->setPort(p.first, signal);
			}
			index_inputs(copy);
		}
		SigSpec replacement;
		for (auto bit : SigSpec(output)) replacement.append(importbit(bit));
		auto signal = consumer->getPort(port); signal.replace(offset, replacement);
		consumer->setPort(port, signal); index_inputs(consumer);
		for (auto cell : deleted) removed.insert(cell);
		log("Specialized PMUX context at %s.%s in %s (private cost %d -> %d).\n", log_id(consumer), log_id(port), log_id(module), old_cost, new_cost);
		changes++;
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

	Const maximum(SigSpec signal)
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
			result.valid = true; result.base = signal; result.residue = Const(State::S0, GetSize(modulus)); result.upper = maximum(signal);
			return result;
		}
		if (!active.insert(cell).second || GetSize(active) > max_cells) return result;
		if (cell->type.in(ID($add), ID($pos))) {
			if (cell->getParam(ID::A_SIGNED).as_bool() || (cell->hasPort(ID::B) && cell->getParam(ID::B_SIGNED).as_bool())) { active.erase(cell); return result; }
			auto a = sigmap(cell->getPort(ID::A));
			SigSpec b = cell->hasPort(ID::B) ? sigmap(cell->getPort(ID::B)) : SigSpec(State::S0);
			if (a.is_fully_const()) std::swap(a, b);
			if (!b.is_fully_def()) { active.erase(cell); return result; }
			result = relation(a, modulus, active, budget, depth+1);
			if (result.valid) {
				int width = GetSize(signal), calc_width = std::max({width, GetSize(a), GetSize(b), GetSize(result.upper), GetSize(modulus)})+2;
				auto sum = const_add(result.upper, b.as_const(), false, false, calc_width);
				Const capacity(State::S0, calc_width); capacity.set(width, State::S1);
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
			if (count > 16) { active.erase(cell); return result; }
			std::vector<SigSpec> branches;
			if (!a.is_fully_undef()) branches.push_back(a);
			for (int i = 0; i < count; i++) branches.push_back(b.extract(i*GetSize(a), GetSize(a)));
			bool first = true;
			for (auto branch : branches) {
				auto next = relation(branch, modulus, active, budget, depth+1);
				if (!next.valid || (!first && (result.base != next.base || result.residue != next.residue))) { result.valid = false; break; }
				if (first) { result = next; first = false; }
				else {
					result.cells.insert(next.cells.begin(), next.cells.end());
					if (const_lt(result.upper, next.upper, false, false, 1).as_bool()) result.upper = next.upper;
				}
			}
			if (first) result.valid = false;
			if (result.valid) { result.selection = true; result.cells.insert(cell); }
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
		cell->setPort(ID::A, result.base); cell->setParam(ID::A_WIDTH, GetSize(result.base)); index_inputs(cell);
		for (auto old_cell : deleted) removed.insert(old_cell);
		log("Reduced PMUX modulo input at %s in %s (private cost %d -> 0).\n", log_id(cell), log_id(module), old_cost);
		changes++;
	}

	void run()
	{
		auto candidates = module->cells().to_vector();
		for (auto cell : candidates) {
			if (total_budget <= 0) continue;
			if (cell->type.in(ID($mod), ID($modfloor))) { modulo(cell); continue; }
			if (!editable(cell)) continue;
			if (!cell->type.in(ID($mux), ID($pmux))) continue;
			auto s = sigmap(cell->getPort(ID::S));
			int width = GetSize(cell->getPort(ID::A));
			if (GetSize(s) > 16 || width > max_bits) continue;
			if (cell->type == ID($mux)) {
				for (int value = 0; value < 2; value++) {
					dict<SigBit, State> facts; int budget = max_bits;
					if (condition(s[0], value, facts, budget)) specialize(cell, value ? ID::B : ID::A, 0, width, facts);
				}
			} else {
				for (int index = 0; index < GetSize(s); index++) {
					dict<SigBit, State> facts; int budget = max_bits;
					if (condition(s[index], true, facts, budget)) specialize(cell, ID::B, index*width, width, facts);
				}
			}
		}
		for (auto cell : removed) module->remove(cell);
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
		log_header(design, "Executing OPT_PMUXCONTEXT pass.\n");
		extra_args(args, 1, design);
		for (auto module : design->selected_modules()) {
			bool candidate = false;
			for (auto cell : module->selected_cells()) if (cell->type.in(ID($mux), ID($pmux), ID($mod), ID($modfloor))) { candidate = true; break; }
			if (!candidate) continue;
			bool whole = design->selected_whole_module(module);
			PmuxContextWorker worker(module, design); worker.run();
			if (worker.changes && whole) {
				Pass::call_on_module(design, module, "opt_expr -fine");
				Pass::call_on_module(design, module, "opt_clean");
			}
		}
	}
} OptPmuxContextPass;

PRIVATE_NAMESPACE_END
