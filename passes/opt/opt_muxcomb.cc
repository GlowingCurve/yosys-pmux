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
	dict<SigBit, int> drivers;
	dict<SigBit, std::pair<Cell*, int>> mux_driver;
	pool<Cell*> reserved;
	int merged = 0;

	struct Branch {
		Cell *cell = nullptr;
		SigSpec a, b;
		SigBit s;
		bool inverted = false;
	};

	struct Combination {
		Cell *top;
		SigSpec a, b;
		SigBit s;
		Branch lo, hi;
	};
	vector<Combination> combinations;

	OptMuxcombWorker(Module *module) : module(module), sigmap(module)
	{
		for (auto wire : module->wires()) {
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(wire))
					users[bit]++;
			if (wire->port_input)
				for (auto bit : sigmap(wire))
					drivers[bit]++;
		}
		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				// 未知单元的端口同时作为使用者和潜在驱动者。
				bool input = !cell->known() || cell->input(conn.first);
				bool output = !cell->known() || cell->output(conn.first);
				for (auto bit : sigmap(conn.second)) {
					if (input)
						users[bit]++;
					if (output)
						drivers[bit]++;
				}
			}
		for (auto cell : module->selected_cells())
			if (cell->type == ID($mux) && !cell->get_bool_attribute(ID::keep)) {
				SigSpec y = sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < GetSize(y); i++)
					mux_driver[y[i]] = {cell, i};
			}
	}

	// 按父节点的数据位顺序提取子节点，允许输出切片和位序重排。
	Branch child_mux(Cell *top, const SigSpec &sig)
	{
		if (GetSize(sig) == 0 || !mux_driver.count(sig[0]))
			return {};
		Cell *c = mux_driver.at(sig[0]).first;
		if (c == top || reserved.count(c))
			return {};
		pool<SigBit> used;
		Branch branch;
		branch.cell = c;
		branch.s = sigmap(c->getPort(ID::S)[0]);
		SigSpec a = sigmap(c->getPort(ID::A)), b = sigmap(c->getPort(ID::B));
		for (auto bit : sig) {
			auto it = mux_driver.find(bit);
			if (!bit.wire || it == mux_driver.end() || it->second.first != c ||
					drivers.at(bit) != 1 || users.at(bit) != 1 || !used.insert(bit).second)
				return {};
			branch.a.append(a[it->second.second]);
			branch.b.append(b[it->second.second]);
		}
		// 删除子节点时，其余输出位必须已经没有使用者。
		for (auto bit : sigmap(c->getPort(ID::Y)))
			if (!bit.wire || drivers.at(bit) != 1 || (!used.count(bit) && users[bit] != 0))
				return {};
		return branch;
	}

	SigBit invert(SigBit bit)
	{
		if (bit == State::S0)
			return State::S1;
		if (bit == State::S1)
			return State::S0;
		return module->Not(NEW_ID, bit);
	}

	SigBit mux_bit(SigBit s, SigBit lo, SigBit hi)
	{
		if (s == State::S0)
			return lo;
		if (s == State::S1)
			return hi;
		if (lo == hi)
			return lo;
		if (lo == State::S0 && hi == State::S1)
			return s;
		if (lo == State::S1 && hi == State::S0)
			return invert(s);
		if (lo == State::S0)
			return module->And(NEW_ID, s, hi);
		if (hi == State::S1)
			return module->Or(NEW_ID, s, lo);
		if (hi == State::S0)
			return module->And(NEW_ID, invert(s), lo);
		if (lo == State::S1)
			return module->Or(NEW_ID, invert(s), hi);
		return module->Mux(NEW_ID, lo, hi, s);
	}

	// Fig.6(a)-(b)：重复的数据输入表示为选择常量 0 或 1 的虚拟 MUX。
	bool match_branch(Cell *top, const SigSpec &sig, const SigSpec &a, const SigSpec &b, Branch &branch)
	{
		if (sig == a || sig == b) {
			branch.s = sig == a ? State::S0 : State::S1;
			return true;
		}
		branch = child_mux(top, sig);
		if (branch.cell == nullptr)
			return false;
		if (branch.a == a && branch.b == b)
			return true;
		if (branch.a == b && branch.b == a) {
			branch.inverted = true;
			return true;
		}
		return false;
	}

	void find_combination(Cell *top)
	{
		SigSpec lo = sigmap(top->getPort(ID::A)), hi = sigmap(top->getPort(ID::B));
		for (const auto &sig : {lo, hi}) {
			Branch child = child_mux(top, sig);
			if (child.cell == nullptr || child.a == child.b)
				continue;
			Combination comb;
			comb.top = top;
			comb.a = child.a;
			comb.b = child.b;
			comb.s = sigmap(top->getPort(ID::S)[0]);
			if (!match_branch(top, lo, comb.a, comb.b, comb.lo) ||
					!match_branch(top, hi, comb.a, comb.b, comb.hi))
				continue;
			log_assert(comb.lo.cell != nullptr || comb.hi.cell != nullptr);
			combinations.push_back(comb);
			reserved.insert(top);
			if (comb.lo.cell != nullptr)
				reserved.insert(comb.lo.cell);
			if (comb.hi.cell != nullptr)
				reserved.insert(comb.hi.cell);
			return;
		}
	}

	bool run()
	{
		// 匹配期间保持连接关系不变，每个单元只参加一次变换。
		for (auto cell : module->selected_cells())
			if (cell->type == ID($mux) && !cell->get_bool_attribute(ID::keep) && !reserved.count(cell))
				find_combination(cell);
		for (const auto &comb : combinations) {
			// Fig.4、Fig.6(b)-(d)：把数据选择转移到一位控制信号，并化简常量支路。
			SigBit lo = comb.lo.inverted ? invert(comb.lo.s) : comb.lo.s;
			SigBit hi = comb.hi.inverted ? invert(comb.hi.s) : comb.hi.s;
			comb.top->setPort(ID::A, comb.a);
			comb.top->setPort(ID::B, comb.b);
			comb.top->setPort(ID::S, mux_bit(comb.s, lo, hi));
			for (auto child : {comb.lo.cell, comb.hi.cell}) {
				if (child == nullptr)
					continue;
				log("  merging %s into %s\n", log_id(child), log_id(comb.top));
				module->remove(child);
			}
		}
		merged = GetSize(combinations);
		return merged != 0;
	}
};

struct OptMuxcombPass : public Pass {
	OptMuxcombPass() : Pass("opt_muxcomb", "merge $mux cells that select between the same pair of inputs") { }
	void help() override
	{
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
		log("Fig.6 treats a repeated data input as a virtual mux with a constant select.\n");
		log("Combining it with the other branch produces these four equivalent forms:\n");
		log("\n");
		log("    s0 ? b : (s1 ? b : a)  =>  (s0 | s1) ? b : a\n");
		log("    s0 ? a : (s1 ? b : a)  =>  (~s0 & s1) ? b : a\n");
		log("    s0 ? (s1 ? b : a) : a  =>  (s0 & s1) ? b : a\n");
		log("    s0 ? (s1 ? b : a) : b  =>  (~s0 | s1) ? b : a\n");
		log("\n");
		log("Both input orders, aliases, output slices and bit permutations are supported.\n");
		log("Only selected cells without 'keep' are combined. Removed children must have\n");
		log("unique output drivers and feed only their parent; unused output bits are OK.\n");
		log("The rewrite repeats until no combinations remain. Modules with processes\n");
		log("are skipped. Run before opt_muxtree and opt_expr to simplify the resulting\n");
		log("control trees as described in Fig.5 and Fig.7.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MUXCOMB pass (merge muxes over the same input pair).\n");
		extra_args(args, 1, design);

		int merged = 0;
		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			while (true) {
				OptMuxcombWorker worker(module);
				bool did_something = worker.run();
				merged += worker.merged;
				if (!did_something)
					break;
			}
		}

		if (merged)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Merged %d $mux combinations.\n", merged);
	}
} OptMuxcombPass;

PRIVATE_NAMESPACE_END
