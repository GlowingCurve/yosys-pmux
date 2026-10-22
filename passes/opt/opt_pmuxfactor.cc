#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
// opt_pmuxfactor 提取 PMUX 分支的公共运算并前移归约运算；复用分支表达式与端口映射，减少选择逻辑和重复运算。
USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PmuxFactorWorker {
	Module *module;
	SigMap sigmap;
	CellTypes types;
	dict<SigBit, std::pair<Cell *, int>> drivers;
	dict<SigBit, pool<Cell *>> users;
	pool<SigBit> protected_bits;
	pool<SigBit> kept_bits;
	pool<Cell *> selected;
	dict<std::tuple<IdString, SigBit, SigBit>, SigBit> operators;
	int changes = 0;

	PmuxFactorWorker(Module *module, Design *design) : module(module), sigmap(module), types(design)
	{
		for (auto wire : module->wires()) if (wire->port_input)
			for (auto bit : sigmap(wire)) drivers[bit] = {nullptr, 0};
		for (auto wire : module->wires())
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(wire)) {
					protected_bits.insert(bit);
					if (wire->get_bool_attribute(ID::keep)) kept_bits.insert(bit);
				}
		for (auto cell : module->cells()) {
			if (design->selected(module, cell)) selected.insert(cell);
			bool keep = cell->get_bool_attribute(ID::keep);
			for (auto &port : cell->connections()) {
				auto signal = sigmap(port.second);
				bool output = types.cell_output(cell->type, port.first);
				for (int i = 0; i < GetSize(signal); i++) {
					if (output) {
						if (drivers.count(signal[i])) drivers[signal[i]] = {nullptr, 0};
						else drivers[signal[i]] = {cell, i};
					} else users[signal[i]].insert(cell);
					if (keep) { protected_bits.insert(signal[i]); kept_bits.insert(signal[i]); }
				}
			}
		}
		for (auto cell : module->cells()) if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor)) && editable(cell)) {
			auto y = sigmap(cell->getPort(ID::Y));
			auto aa = sigmap(cell->getPort(ID::A)), bb = sigmap(cell->getPort(ID::B));
			bool sign = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
			for (int i = 0; i < GetSize(y); i++) {
				auto a = i < GetSize(aa) ? aa[i] : sign && !aa.empty() ? aa.back() : SigBit(State::S0);
				auto b = i < GetSize(bb) ? bb[i] : sign && !bb.empty() ? bb.back() : SigBit(State::S0);
				if (b < a) std::swap(a, b);
				operators[std::make_tuple(cell->type, a, b)] = y[i];
			}
		}
	}

	bool editable(Cell *cell)
	{
		if (!cell->hasPort(ID::Y) || !selected.count(cell) || cell->get_bool_attribute(ID::keep)) return false;
		for (auto bit : sigmap(cell->getPort(ID::Y)))
			if (kept_bits.count(bit) || !drivers.count(bit) || drivers.at(bit).first != cell) return false;
		return true;
	}

	SigBit operand(Cell *cell, IdString port, int index)
	{
		auto signal = sigmap(cell->getPort(port));
		bool sign = cell->getParam(ID::A_SIGNED).as_bool();
		if (cell->hasPort(ID::B)) sign &= cell->getParam(ID::B_SIGNED).as_bool();
		if (index < GetSize(signal)) return signal[index];
		return sign && !signal.empty() ? signal.back() : SigBit(State::S0);
	}

	bool expression(SigBit bit, IdString &type, SigBit &a, SigBit &b)
	{
		if (!drivers.count(bit) || !drivers.at(bit).first) return false;
		auto entry = drivers.at(bit);
		auto cell = entry.first;
		if (!editable(cell)) return false;
		type = cell->type;
		if (type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
			a = operand(cell, ID::A, entry.second);
			b = operand(cell, ID::B, entry.second);
			return true;
		}
		if (type == ID($mux)) {
			a = sigmap(cell->getPort(ID::A))[entry.second];
			b = sigmap(cell->getPort(ID::B))[entry.second];
			return true;
		}
		return false;
	}

	struct Plan {
		SigBit result;
		SigSpec values;
		IdString type;
		std::shared_ptr<Plan> a, b;
		int selectors = 0;
		int operations = 0;
		bool direct = false;
	};
	using PlanPtr = std::shared_ptr<Plan>;
	struct Edit {
		Cell *cell;
		SigSpec a, b, y;
	};

	struct Choice {
		SigSpec select;
		dict<SigSpec, SigBit> exact, undefined_default;
	};

	PlanPtr direct(SigBit bit)
	{
		auto plan = std::make_shared<Plan>();
		plan->direct = true;
		plan->result = bit;
		return plan;
	}

	bool depends(SigBit bit, SigBit target, pool<SigBit> &seen, int &budget)
	{
		if (bit == target) return true;
		if (!seen.insert(bit).second || !drivers.count(bit) || !drivers.at(bit).first) return false;
		if (--budget <= 0) return true;
		auto entry = drivers.at(bit); auto cell = entry.first;
		SigSpec inputs;
		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
			inputs.append(operand(cell, ID::A, entry.second)); inputs.append(operand(cell, ID::B, entry.second));
		} else if (cell->type.in(ID($mux), ID($pmux))) {
			auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), s = sigmap(cell->getPort(ID::S));
			inputs.append(a[entry.second]); inputs.append(s);
			for (int i = 0; i < (cell->type == ID($mux) ? 1 : GetSize(s)); i++) inputs.append(b[i*GetSize(a)+entry.second]);
		} else {
			for (auto &port : cell->connections()) if (types.cell_input(cell->type, port.first)) inputs.append(sigmap(port.second));
		}
		for (auto input : inputs) if (depends(input, target, seen, budget)) return true;
		return false;
	}

	bool independent(SigBit bit, SigBit target)
	{
		pool<SigBit> seen; int budget = 512;
		return !depends(bit, target, seen, budget);
	}

	PlanPtr lookup(Choice &choice, SigSpec values, SigBit avoid)
	{
		if (choice.exact.count(values) && independent(choice.exact.at(values), avoid))
			return direct(choice.exact.at(values));
		if (values[0] == State::Sx) {
			auto branches = values.extract(1, GetSize(values)-1);
			if (choice.undefined_default.count(branches) && independent(choice.undefined_default.at(branches), avoid))
				return direct(choice.undefined_default.at(branches));
		}
		SigBit same = values[0];
		if (same == State::Sx) same = values[1];
		for (int i = 0; i < GetSize(values); i++)
			if (values[i] != same && values[i] != State::Sx) return nullptr;
		return direct(same);
	}

	PlanPtr lift(Choice &choice, SigSpec values, SigBit avoid, int depth, bool root = false)
	{
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
				if (i == 0 && values[i] == State::Sx) {
					aa.append(State::Sx); bb.append(State::Sx); ss.append(State::Sx);
					continue;
				}
				IdString type;
				SigBit a, b;
				if (!expression(values[i], type, a, b) || (!common.empty() && type != common)) { match = false; break; }
				if (common.empty()) { common = type; first_a = a; first_b = b; }
				if (type != ID($mux) && a == first_b && b != first_b) std::swap(a, b);
				aa.append(a); bb.append(b);
				if (type == ID($mux)) ss.append(sigmap(drivers.at(values[i]).first->getPort(ID::S)));
			}
			if (match && !common.empty()) {
				PlanPtr a, b;
				if (common == ID($mux)) {
					auto pa = lookup(choice, aa, avoid), pb = lookup(choice, bb, avoid);
					bool defined_data = (first_a.wire || first_a.data == State::S0 || first_a.data == State::S1) &&
						(first_b.wire || first_b.data == State::S0 || first_b.data == State::S1);
					if (defined_data && pa && pb && pa->direct && pb->direct && pa->result == first_a && pb->result == first_b) {
						a = direct(first_a); b = lift(choice, ss, avoid, depth-1);
					}
				} else {
					a = lift(choice, aa, avoid, depth-1);
					b = lift(choice, bb, avoid, depth-1);
				}
				if (a && b && a->selectors + b->selectors <= 1) {
					auto plan = std::make_shared<Plan>();
					plan->type = common; plan->a = a; plan->b = b;
					if (common == ID($mux)) plan->values.append(first_b);
					plan->selectors = a->selectors + b->selectors;
					plan->operations = 1 + a->operations + b->operations;
					return plan;
				}
			}
		}
		if (root) return nullptr;
		auto plan = std::make_shared<Plan>();
		plan->values = values; plan->selectors = 1;
		return plan;
	}

	SigBit materialize(Choice &choice, PlanPtr plan, SigBit avoid)
	{
		if (plan->direct) return plan->result;
		if (plan->type.empty()) {
			auto output = module->addWire(NEW_ID);
			module->addPmux(NEW_ID, plan->values[0], plan->values.extract(1, GetSize(plan->values)-1), choice.select, output);
			return SigBit(output);
		} else {
			auto a = materialize(choice, plan->a, avoid), b = materialize(choice, plan->b, avoid);
			if (plan->type != ID($mux) && b < a) std::swap(a, b);
			auto key = std::make_tuple(plan->type, a, b);
			if (plan->type != ID($mux) && operators.count(key) && independent(operators.at(key), avoid)) return operators.at(key);
			auto output = module->addWire(NEW_ID);
			Cell *cell;
			if (plan->type == ID($mux)) cell = module->addMux(NEW_ID, a, plan->values[0], b, output);
			else {
				cell = module->addCell(NEW_ID, plan->type);
				cell->setParam(ID::A_WIDTH, 1); cell->setParam(ID::B_WIDTH, 1); cell->setParam(ID::Y_WIDTH, 1);
				cell->setParam(ID::A_SIGNED, false); cell->setParam(ID::B_SIGNED, false);
				cell->setPort(ID::A, a); cell->setPort(ID::B, b); cell->setPort(ID::Y, output);
			}
			if (plan->type != ID($mux)) operators[key] = SigBit(output);
			return SigBit(output);
		}
	}

	void xor_terms(SigBit bit, pool<SigBit> &terms, int depth)
	{
		IdString type; SigBit a, b;
		if (depth && expression(bit, type, a, b) && type == ID($xor)) {
			xor_terms(a, terms, depth-1); xor_terms(b, terms, depth-1);
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
				xor_terms(operand(cell, ID::A, i), terms, 3); xor_terms(operand(cell, ID::B, i), terms, 3);
				if (GetSize(terms) <= 1) {
					module->connect(y[i], terms.empty() ? SigBit(State::S0) : *terms.begin()); changes++;
				} else { a.append(operand(cell, ID::A, i)); b.append(operand(cell, ID::B, i)); remaining.append(y[i]); }
			}
			if (GetSize(remaining) == GetSize(y)) continue;
			if (remaining.empty()) removed.push_back(cell);
			else edits.push_back({cell, a, b, remaining});
		}
		for (auto &edit : edits) {
			edit.cell->setPort(ID::A, edit.a); edit.cell->setPort(ID::B, edit.b); edit.cell->setPort(ID::Y, edit.y);
			edit.cell->setParam(ID::A_WIDTH, GetSize(edit.a)); edit.cell->setParam(ID::B_WIDTH, GetSize(edit.b)); edit.cell->setParam(ID::Y_WIDTH, GetSize(edit.y));
			edit.cell->setParam(ID::A_SIGNED, false); edit.cell->setParam(ID::B_SIGNED, false);
		}
		for (auto cell : removed) module->remove(cell);
	}

	bool private_branches(Cell *pmux, const SigSpec &values, int operations)
	{
		pool<Cell *> roots;
		pool<SigBit> selectors;
		for (auto bit : sigmap(pmux->getPort(ID::S))) selectors.insert(bit);
		for (auto bit : values) {
			if (bit == State::Sx) continue;
			if (!drivers.count(bit) || !drivers.at(bit).first) return false;
			auto cell = drivers.at(bit).first;
			for (auto y : sigmap(cell->getPort(ID::Y))) {
				if (protected_bits.count(y) || selectors.count(y)) return false;
				for (auto user : users[y]) if (user != pmux) return false;
			}
			roots.insert(cell);
		}
		return GetSize(roots) > operations && GetSize(roots) >= 3;
	}

	bool boolean_support(SigBit bit, pool<SigBit> &support, pool<SigBit> &seen, int &budget)
	{
		if (!bit.wire || !seen.insert(bit).second) return true;
		if (--budget <= 0) return false;
		if (drivers.count(bit) && drivers.at(bit).first) {
			auto entry = drivers.at(bit);
			auto cell = entry.first;
			SigSpec inputs;
			if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
				inputs.append(operand(cell, ID::A, entry.second)); inputs.append(operand(cell, ID::B, entry.second));
			} else if (cell->type == ID($not)) {
				inputs.append(operand(cell, ID::A, entry.second));
			} else if (cell->type.in(ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge),
					ID($logic_not), ID($logic_and), ID($logic_or), ID($reduce_and), ID($reduce_or),
					ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor))) {
				inputs.append(sigmap(cell->getPort(ID::A)));
				if (cell->hasPort(ID::B)) inputs.append(sigmap(cell->getPort(ID::B)));
			}
			if (!inputs.empty()) {
				for (auto input : inputs) if (!boolean_support(input, support, seen, budget)) return false;
				return true;
			}
		}
		support.insert(bit);
		return true;
	}

	bool independent_selector_branches(PlanPtr plan)
	{
		if (plan->direct) return true;
		if (!plan->type.empty()) return independent_selector_branches(plan->a) && independent_selector_branches(plan->b);
		// 新建选择器的分支需要具有独立支持，避免把共享控制逻辑计作可删除的独立成本。
		pool<SigBit> used;
		for (int i = 0; i < GetSize(plan->values); i++) {
			if (i == 0 && plan->values[i] == State::Sx) continue;
			pool<SigBit> support, seen;
			int budget = 512;
			if (!boolean_support(plan->values[i], support, seen, budget) || support.empty()) return false;
			for (auto bit : support) if (!used.insert(bit).second) return false;
		}
		return true;
	}

	void factor()
	{
		dict<SigSpec, Choice> choices;
		std::vector<Cell *> pmuxes;
		std::vector<Cell *> removed;
		std::vector<Edit> edits;
		for (auto cell : module->cells()) if (cell->type == ID($pmux) && editable(cell)) {
			auto s = sigmap(cell->getPort(ID::S));
			if (GetSize(s) < 3) continue;
			auto &choice = choices[s]; choice.select = s;
			auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), y = sigmap(cell->getPort(ID::Y));
			for (int j = 0; j < GetSize(y); j++) {
				SigSpec values(a[j]);
				for (int i = 0; i < GetSize(s); i++) values.append(b[i*GetSize(y)+j]);
				choice.exact[values] = y[j];
				choice.undefined_default[values.extract(1, GetSize(s))] = y[j];
			}
			pmuxes.push_back(cell);
		}
		for (auto cell : pmuxes) {
			auto s = sigmap(cell->getPort(ID::S)); auto &choice = choices[s];
			auto a = sigmap(cell->getPort(ID::A)), b = sigmap(cell->getPort(ID::B)), y = sigmap(cell->getPort(ID::Y));
			SigSpec remaining_a, remaining_b, remaining_y;
			std::vector<int> remaining;
			std::vector<SigSpec> branch_values;
			std::vector<PlanPtr> plans;
			int count = 0;
			for (int j = 0; j < GetSize(y); j++) {
				SigSpec values(a[j]);
				for (int i = 0; i < GetSize(s); i++) values.append(b[i*GetSize(y)+j]);
				auto plan = lift(choice, values, y[j], 3, true);
				if (plan && !private_branches(cell, values, plan->operations)) plan = nullptr;
				if (plan && !independent_selector_branches(plan)) plan = nullptr;
				plans.push_back(plan); branch_values.push_back(values);
			}
			bool invalidated;
			do {
				invalidated = false;
				pool<Cell *> retained;
				for (int j = 0; j < GetSize(y); j++) if (!plans[j])
					for (auto bit : branch_values[j]) if (drivers.count(bit) && drivers.at(bit).first) retained.insert(drivers.at(bit).first);
				for (int j = 0; j < GetSize(y); j++) if (plans[j])
					for (auto bit : branch_values[j]) if (drivers.count(bit) && retained.count(drivers.at(bit).first)) {
						plans[j] = nullptr; invalidated = true; break;
					}
			} while (invalidated);
			for (int j = 0; j < GetSize(y); j++) {
				if (!plans[j]) { remaining.push_back(j); continue; }
				module->connect(y[j], materialize(choice, plans[j], y[j])); count++;
			}
			if (!count) continue;
			for (int j : remaining) { remaining_a.append(a[j]); remaining_y.append(y[j]); }
			for (int i = 0; i < GetSize(s); i++) for (int j : remaining) remaining_b.append(b[i*GetSize(y)+j]);
			if (remaining.empty()) removed.push_back(cell);
			else edits.push_back({cell, remaining_a, remaining_b, remaining_y});
			changes += count;
		}
		for (auto &edit : edits) {
			edit.cell->setPort(ID::A, edit.a); edit.cell->setPort(ID::B, edit.b); edit.cell->setPort(ID::Y, edit.y);
			edit.cell->setParam(ID::WIDTH, GetSize(edit.y));
		}
		for (auto cell : removed) module->remove(cell);
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
			bool private_output = true;
			for (auto bit : input) {
				if (protected_bits.count(bit)) private_output = false;
				for (auto user : users[bit]) if (user != reduce) private_output = false;
			}
			if (!private_output) continue;
			auto a = sigmap(pmux->getPort(ID::A)), b = sigmap(pmux->getPort(ID::B)), s = sigmap(pmux->getPort(ID::S));
			if (s.empty()) continue;
			std::vector<SigSpec> branches;
			branches.push_back(a);
			for (int i = 0; i < GetSize(s); i++) branches.push_back(b.extract(i*GetSize(a), GetSize(a)));
			pool<SigSpec> unique;
			for (auto &branch : branches) { branch.sort(); unique.insert(branch); }
			if (GetSize(unique)*(GetSize(a)-1)+GetSize(s) >= GetSize(a)*(GetSize(s)+1)) continue;
			dict<SigSpec, SigBit> results;
			SigSpec reduced;
			for (auto branch : branches) {
				if (!results.count(branch)) {
					auto wire = module->addWire(NEW_ID);
					auto cell = module->addCell(NEW_ID, reduce->type);
					cell->setParam(ID::A_WIDTH, GetSize(branch)); cell->setParam(ID::Y_WIDTH, 1); cell->setParam(ID::A_SIGNED, false);
					cell->setPort(ID::A, branch); cell->setPort(ID::Y, wire); results[branch] = SigBit(wire);
				}
				reduced.append(results.at(branch));
			}
			bool same_defined = true;
			for (int i = 2; i < GetSize(reduced); i++) if (reduced[i] != reduced[1]) same_defined = false;
			if (GetSize(unique) == 1 || (a.is_fully_undef() && same_defined))
				module->connect(reduce->getPort(ID::Y), reduced[1]);
			else module->addPmux(NEW_ID, reduced[0], reduced.extract(1, GetSize(s)), s, reduce->getPort(ID::Y));
			removed.push_back(reduce); removed.push_back(pmux); changes++;
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
		log_header(design, "Executing OPT_PMUXFACTOR pass.\n");
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
				PmuxFactorWorker worker(module, design); worker.reductions();
				rebuild = worker.changes != 0;
				if (!rebuild) worker.factor();
				changes = worker.changes;
			}
			if (rebuild) {
				PmuxFactorWorker worker(module, design); worker.factor();
				changes += worker.changes;
			}
			if (changes) {
				{
					PmuxFactorWorker xors(module, design); xors.simplify_xors();
				}
				log("Changed %d PMUX output bits/reductions in %s.\n", changes, log_id(module));
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
