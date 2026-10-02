#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Wang et al., "Optimization of Multiplexer Combination in RTL Logic Synthesis", ISEDA 2023.
// s0 ? (s2 ? b : a) : (s1 ? b : a)  =>  (s0 ? s2 : s1) ? b : a     (Fig.4)
// s0 ? b : (s1 ? b : a)             =>  (s0 | s1) ? b : a          (Fig.6)
struct OptMuxcombWorker
{
	Module *module;
	SigMap sigmap;
	dict<SigBit, int> users;
	dict<SigBit, Cell*> mux_driver;
	pool<Cell*> removed;
	int merged = 0;

	OptMuxcombWorker(Module *module) : module(module), sigmap(module)
	{
		for (auto wire : module->wires())
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(wire))
					users[bit]++;
		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				// ports of unknown direction count as users
				if (cell->output(conn.first) && !cell->input(conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					users[bit]++;
			}
		for (auto cell : module->cells())
			if (cell->type == ID($mux))
				for (auto bit : sigmap(cell->getPort(ID::Y)))
					mux_driver[bit] = cell;
	}

	// the $mux that drives exactly sig and only feeds the input of top
	Cell *child_mux(Cell *top, const SigSpec &sig)
	{
		if (GetSize(sig) == 0 || !mux_driver.count(sig[0]))
			return nullptr;
		Cell *c = mux_driver.at(sig[0]);
		if (c == top || removed.count(c) || sigmap(c->getPort(ID::Y)) != sig)
			return nullptr;
		for (auto bit : sig)
			if (users.at(bit) != 1)
				return nullptr;
		return c;
	}

	SigBit mux_bit(SigBit s, SigBit lo, SigBit hi)
	{
		if (lo == hi)
			return lo;
		if (lo == State::S0 && hi == State::S1)
			return s;
		if (lo == State::S1 && hi == State::S0)
			return module->Not(NEW_ID, s);
		if (lo == State::S0)
			return module->And(NEW_ID, s, hi);
		if (hi == State::S1)
			return module->Or(NEW_ID, s, lo);
		if (hi == State::S0)
			return module->And(NEW_ID, module->Not(NEW_ID, s), lo);
		if (lo == State::S1)
			return module->Or(NEW_ID, module->Not(NEW_ID, s), hi);
		return module->Mux(NEW_ID, lo, hi, s);
	}

	bool try_merge(Cell *top)
	{
		SigSpec y_a = sigmap(top->getPort(ID::A));
		SigSpec y_b = sigmap(top->getPort(ID::B));
		SigBit s0 = sigmap(top->getPort(ID::S)[0]);
		Cell *ca = child_mux(top, y_a);
		Cell *cb = child_mux(top, y_b);
		if (ca == nullptr && cb == nullptr)
			return false;
		if (ca == cb)
			return false;

		SigSpec a, b;
		SigBit ctrl_a, ctrl_b;
		if (ca != nullptr && cb != nullptr) {
			SigSpec a1 = sigmap(ca->getPort(ID::A)), b1 = sigmap(ca->getPort(ID::B));
			SigSpec a2 = sigmap(cb->getPort(ID::A)), b2 = sigmap(cb->getPort(ID::B));
			SigBit s1 = sigmap(ca->getPort(ID::S)[0]), s2 = sigmap(cb->getPort(ID::S)[0]);
			if (a1 == b1)
				return false;
			a = a1, b = b1, ctrl_a = s1;
			if (a2 == a1 && b2 == b1)
				ctrl_b = s2;
			else if (a2 == b1 && b2 == a1)
				ctrl_b = module->Not(NEW_ID, s2);
			else
				return false;
		} else {
			// a plain input equal to one side of the child selects that side constantly
			Cell *c = ca != nullptr ? ca : cb;
			SigSpec leaf = ca != nullptr ? y_b : y_a;
			SigSpec ac = sigmap(c->getPort(ID::A)), bc = sigmap(c->getPort(ID::B));
			SigBit sc = sigmap(c->getPort(ID::S)[0]);
			if (ac == bc)
				return false;
			SigBit ctrl_leaf;
			if (leaf == ac)
				ctrl_leaf = State::S0;
			else if (leaf == bc)
				ctrl_leaf = State::S1;
			else
				return false;
			a = ac, b = bc;
			ctrl_a = ca != nullptr ? sc : ctrl_leaf;
			ctrl_b = ca != nullptr ? ctrl_leaf : sc;
		}

		log("  merging %s into %s\n", ca != nullptr && cb != nullptr ?
				stringf("%s and %s", log_id(ca), log_id(cb)) : log_id(ca != nullptr ? ca : cb), log_id(top));
		top->setPort(ID::A, a);
		top->setPort(ID::B, b);
		top->setPort(ID::S, mux_bit(s0, ctrl_a, ctrl_b));
		if (ca != nullptr)
			removed.insert(ca);
		if (cb != nullptr)
			removed.insert(cb);
		return true;
	}

	bool run()
	{
		bool did_something = false;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($mux) && !removed.count(cell) && try_merge(cell)) {
				did_something = true;
				merged++;
			}
		for (auto cell : removed)
			module->remove(cell);
		removed.clear();
		return did_something;
	}
};

struct OptMuxcombPass : public Pass {
	OptMuxcombPass() : Pass("opt_muxcomb", "merge $mux cells that select between the same pair of inputs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_muxcomb [selection]\n");
		log("\n");
		log("This pass implements the multiplexer combination of Wang et al., ISEDA 2023.\n");
		log("A $mux whose inputs are both $muxes selecting between the same data 'a' and\n");
		log("'b' with different select signals is replaced by a single $mux between 'a'\n");
		log("and 'b', whose select is a 1-bit mux of the child select signals:\n");
		log("\n");
		log("    s0 ? (s2 ? b : a) : (s1 ? b : a)  =>  (s0 ? s2 : s1) ? b : a\n");
		log("\n");
		log("An input that is 'a' or 'b' itself selects it with a constant, so the select\n");
		log("logic becomes an AND, OR or NOT gate, e.g.:\n");
		log("\n");
		log("    s0 ? b : (s1 ? b : a)  =>  (s0 | s1) ? b : a\n");
		log("\n");
		log("Children are only merged if they feed nothing else. The rewrite is repeated\n");
		log("until no more cells can be merged, so whole mux trees are folded bottom-up.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MUXCOMB pass (merge muxes over the same input pair).\n");
		extra_args(args, 1, design);

		int merged = 0;
		for (auto module : design->selected_modules())
			while (true) {
				OptMuxcombWorker worker(module);
				bool did_something = worker.run();
				merged += worker.merged;
				if (!did_something)
					break;
			}

		log("Merged %d $mux combinations.\n", merged);
	}
} OptMuxcombPass;

PRIVATE_NAMESPACE_END
