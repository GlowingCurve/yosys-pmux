#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MuxCombineWorker
{
	Module *module;
	CellTypes &types;
	SigMap sigmap;
	dict<SigSpec, IdString> drivers;
	dict<SigBit, int> uses, output_drivers;
	dict<SigBit, pool<IdString>> users;
	std::vector<IdString> pending;
	pool<IdString> queued;
	int combinations = 0, variants = 0;
	int removed_mux_bits = 0, added_select_gates = 0;

	MuxCombineWorker(Module *module, CellTypes &types) : module(module), types(types), sigmap(module) {}

	bool is_mux(Cell *cell)
	{
		return cell->type.in(ID($mux), ID($_MUX_)) && GetSize(cell->getPort(ID::S)) == 1;
	}

	SigSpec port(Cell *cell, IdString name) { return sigmap(cell->getPort(name)); }

	void enqueue(IdString name)
	{
		auto cell = module->cell(name);
		if (cell && module->selected(cell) && is_mux(cell) && queued.insert(name).second)
			pending.push_back(name);
	}

	void update(Cell *cell, int delta, bool notify = true)
	{
		for (auto &connection : cell->connections())
			for (auto bit : sigmap(connection.second)) {
				if (!bit.wire) continue;
				bool output = types.cell_output(cell->type, connection.first);
				bool affected = output;
				if (output) output_drivers[bit] += delta;
				else {
					affected = uses[bit] == 1 || uses[bit] + delta == 1;
					uses[bit] += delta;
					if (delta > 0) users[bit].insert(cell->name);
					else users[bit].erase(cell->name);
				}
				if (notify && affected)
					for (auto name : users[bit]) enqueue(name);
			}
		if (is_mux(cell)) {
			auto signal = port(cell, ID::Y);
			if (delta > 0) drivers[signal] = cell->name;
			else if (drivers.count(signal) && drivers.at(signal) == cell->name) drivers.erase(signal);
			if (delta > 0 && notify) enqueue(cell->name);
		}
	}

	void remove(Cell *cell)
	{
		update(cell, -1);
		module->remove(cell);
	}

	void index()
	{
		drivers.clear();
		uses.clear();
		output_drivers.clear();
		for (auto wire : module->wires())
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(wire)) uses[bit]++;
		for (auto cell : module->cells()) update(cell, 1, false);
		for (auto cell : module->selected_cells()) enqueue(cell->name);
	}

	Cell *child(SigSpec signal, Cell *root)
	{
		auto it = drivers.find(signal);
		if (it == drivers.end()) return nullptr;
		auto cell = module->cell(it->second);
		if (!cell || cell == root || !module->selected(cell) || cell->get_bool_attribute(ID::keep)) return nullptr;
		for (auto bit : signal)
			if (!bit.wire || output_drivers.at(bit) != 1) return nullptr;
		return cell;
	}

	bool removable(Cell *cell, int root_uses = 1)
	{
		for (auto bit : port(cell, ID::Y))
			if (uses[bit] != root_uses) return false;
		return true;
	}

	SigSpec invert(SigSpec signal, bool gate)
	{
		auto result = module->addWire(NEW_ID);
		Cell *cell;
		if (gate) cell = module->addNotGate(NEW_ID, signal[0], SigBit(result));
		else cell = module->addNot(NEW_ID, signal, result);
		update(cell, 1);
		return result;
	}

	SigSpec logic(SigSpec a, SigSpec b, bool use_or, bool gate)
	{
		auto result = module->addWire(NEW_ID);
		Cell *cell;
		if (gate) {
			if (use_or) cell = module->addOrGate(NEW_ID, a[0], b[0], SigBit(result));
			else cell = module->addAndGate(NEW_ID, a[0], b[0], SigBit(result));
		} else {
			if (use_or) cell = module->addOr(NEW_ID, a, b, result);
			else cell = module->addAnd(NEW_ID, a, b, result);
		}
		update(cell, 1);
		return result;
	}

	bool rewrite(Cell *root)
	{
		auto a = port(root, ID::A), b = port(root, ID::B), s = port(root, ID::S);
		auto left = child(a, root), right = child(b, root);
		bool gate = root->type == ID($_MUX_);
		if (left && right && left != right) {
			auto la = port(left, ID::A), lb = port(left, ID::B);
			auto ra = port(right, ID::A), rb = port(right, ID::B);
			bool same = la == ra && lb == rb, reverse = la == rb && lb == ra;
			bool remove_left = removable(left), remove_right = removable(right);
			if ((same || reverse) && (remove_left || remove_right) &&
			    (GetSize(a) > 1 || (remove_left && remove_right))) {
				auto rs = port(right, ID::S);
				if (!same) rs = invert(rs, gate);
				auto select = module->addWire(NEW_ID);
				Cell *selector;
				if (gate) selector = module->addMuxGate(NEW_ID, port(left, ID::S)[0], rs[0], s[0], SigBit(select));
				else selector = module->addMux(NEW_ID, port(left, ID::S), rs, s, select);
				update(selector, 1);
				update(root, -1);
				root->setPort(ID::A, la);
				root->setPort(ID::B, lb);
				root->setPort(ID::S, select);
				update(root, 1);
				removed_mux_bits += GetSize(a) * (int(remove_left) + int(remove_right)) - 1;
				added_select_gates += !same;
				if (remove_left) remove(left);
				if (remove_right) remove(right);
				combinations++;
				return true;
			}
		}
		for (int side = 0; side < 2; side++) {
			auto nested = side ? right : left;
			if (!nested || !removable(nested)) continue;
			auto common = side ? a : b;
			auto na = port(nested, ID::A), nb = port(nested, ID::B);
			for (int shared = 0; shared < 2; shared++) {
				if (common != (shared ? nb : na)) continue;
				// 选择结果为 B 时，合并两个必要条件；选择结果为 A 时，合并两个充分条件。
				auto ns = port(nested, ID::S), outer = s;
				if (side != (1 - shared)) outer = invert(outer, gate);
				auto select = logic(outer, ns, shared == 1, gate);
				update(root, -1);
				root->setPort(ID::A, na);
				root->setPort(ID::B, nb);
				root->setPort(ID::S, select);
				update(root, 1);
				removed_mux_bits += GetSize(a);
				added_select_gates += 1 + int(side != (1 - shared));
				remove(nested);
				variants++;
				return true;
			}
		}
		return false;
	}

	void run()
	{
		index();
		for (size_t cursor = 0; cursor < pending.size(); cursor++) {
			auto name = pending[cursor];
			queued.erase(name);
			auto cell = module->cell(name);
			if (cell && is_mux(cell) && module->selected(cell) && !cell->get_bool_attribute(ID::keep))
				rewrite(cell);
		}
	}
};

struct OptMuxCombinePass : Pass
{
	OptMuxCombinePass() : Pass("opt_muxcombine", "combine multiplexers with shared data inputs") {}
	void help() override
	{
		log("\n    opt_muxcombine [-no-clean] [selection]\n\n");
		log("Implement shared-input MUX combinations from Optimization of Multiplexer\n");
		log("Combination in RTL Logic Synthesis (Wang et al., ISEDA 2023). Supports\n");
		log("$mux and $_MUX_, including reversed inputs and shared-input variants.\n");
		log("Run before opt_expr and opt_muxtree to expose further simplifications.\n\n");
		log("    -no-clean\n");
		log("        Only perform combination rewrites; skip traditional optimizations.\n\n");
	}
	void execute(std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing OPT_MUXCOMBINE pass (shared-input MUX combinations).\n");
		bool no_clean = false;
		size_t argidx = 1;
		if (argidx < args.size() && args[argidx] == "-no-clean") { no_clean = true; argidx++; }
		extra_args(args, argidx, design);
		CellTypes types;
		types.setup(design);
		bool did_something = design->scratchpad_get_bool("opt.did_something");
		bool repeat;
		int total_combinations = 0, total_variants = 0, removed_mux_bits = 0, added_select_gates = 0, changes;
		do {
			design->scratchpad_unset("opt.did_something");
			changes = 0;
			for (auto module : design->selected_modules()) {
				if (module->has_processes_warn()) continue;
				MuxCombineWorker worker(module, types);
				worker.run();
				changes += worker.combinations + worker.variants;
				total_combinations += worker.combinations;
				total_variants += worker.variants;
				removed_mux_bits += worker.removed_mux_bits;
				added_select_gates += worker.added_select_gates;
			}
			if (changes) design->scratchpad_set_bool("opt.did_something", true);
			if (!no_clean) {
				Pass::call(design, "opt_expr -mux_bool");
				Pass::call(design, "opt_muxtree");
				Pass::call(design, "opt_clean");
			}
			repeat = design->scratchpad_get_bool("opt.did_something");
			did_something |= repeat;
		} while (!no_clean && repeat);
		if (did_something) design->scratchpad_set_bool("opt.did_something", true);
		log("Combined %d shared-input MUX structures and %d nested MUX variants.\n", total_combinations, total_variants);
		log("Removed %d MUX bits and added %d selector logic gates before cleanup.\n", removed_mux_bits, added_select_gates);
	}
} OptMuxCombinePass;

PRIVATE_NAMESPACE_END
