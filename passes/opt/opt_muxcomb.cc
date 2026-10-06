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
	int expanded = 0;
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

	struct Expansion {
		Cell *top;
		IdString port;
		SigSpec a, b;
		SigBit s;
	};
	vector<Expansion> expansions;

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

	void find_expansion(Cell *top)
	{
		for (auto port : {ID::A, ID::B}) {
			IdString other_port = port == ID::A ? ID::B : ID::A;
			Branch child = child_mux(top, sigmap(top->getPort(other_port)));
			if (child.cell == nullptr || child.a == child.b)
				continue;
			SigSpec repeated = sigmap(top->getPort(port));
			if (repeated != child.a && repeated != child.b)
				continue;
			SigBit s = repeated == child.a ? State::S0 : State::S1;
			expansions.push_back({top, port, child.a, child.b, s});
			reserved.insert(top);
			reserved.insert(child.cell);
			return;
		}
	}

	bool expand()
	{
		for (auto cell : module->selected_cells())
			if (cell->type == ID($mux) && !cell->get_bool_attribute(ID::keep) && !reserved.count(cell))
				find_expansion(cell);
		for (const auto &expansion : expansions) {
			// Fig.6(a)-(b)：创建常量选择 MUX，并用其输出替换父节点的重复输入。
			Wire *y = module->addWire(NEW_ID, GetSize(expansion.a));
			Cell *child = module->addMux(NEW_ID, expansion.a, expansion.b, expansion.s, y,
					expansion.top->get_src_attribute());
			expansion.top->setPort(expansion.port, y);
			module->design->select(module, child);
			module->design->select(module, y);
			log("  expanding %s.%s with %s (select %s)\n", log_id(expansion.top),
					log_id(expansion.port), log_id(child), log_signal(expansion.s));
		}
		expanded = GetSize(expansions);
		return expanded != 0;
	}

	void find_combination(Cell *top)
	{
		Combination comb;
		comb.top = top;
		comb.lo = child_mux(top, sigmap(top->getPort(ID::A)));
		comb.hi = child_mux(top, sigmap(top->getPort(ID::B)));
		if (comb.lo.cell == nullptr || comb.hi.cell == nullptr || comb.lo.cell == comb.hi.cell)
			return;
		comb.a = comb.lo.a;
		comb.b = comb.lo.b;
		comb.s = sigmap(top->getPort(ID::S)[0]);
		if (comb.a == comb.b)
			return;
		if (comb.hi.a == comb.b && comb.hi.b == comb.a)
			comb.hi.inverted = true;
		else if (comb.hi.a != comb.a || comb.hi.b != comb.b)
			return;
		combinations.push_back(comb);
		reserved.insert(top);
		reserved.insert(comb.lo.cell);
		reserved.insert(comb.hi.cell);
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
		log("    opt_muxcomb [-expand] [selection]\n");
		log("\n");
		log("This pass implements the multiplexer combination of Wang et al., ISEDA 2023.\n");
		log("A $mux whose inputs are both $muxes selecting between the same data 'a' and\n");
		log("'b' with different select signals is replaced by a single $mux between 'a'\n");
		log("and 'b', whose select is a 1-bit mux of the child select signals:\n");
		log("\n");
		log("    s0 ? (s2 ? b : a) : (s1 ? b : a)  =>  (s0 ? s2 : s1) ? b : a\n");
		log("\n");
		log("Fig.6(a)-(b) expands a repeated data input into a new $mux with the same\n");
		log("data pair and a constant select (0 for 'a', 1 for 'b'). Its output replaces\n");
		log("the repeated input of the parent. The resulting circuit is then combined\n");
		log("using Fig.4, and its constant control branches are simplified:\n");
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
		log("    -expand\n");
		log("        perform only the Fig.6(a)-(b) expansion, retaining the new muxes\n");
		log("        and their connections for inspection or subsequent combination\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MUXCOMB pass (merge muxes over the same input pair).\n");
		bool expand_only = false;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-expand") {
				expand_only = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int expanded = 0;
		int merged = 0;
		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			while (true) {
				OptMuxcombWorker expansion_worker(module);
				bool did_expand = expansion_worker.expand();
				expanded += expansion_worker.expanded;
				if (expand_only) {
					if (!did_expand)
						break;
					continue;
				}
				// 重新建立索引，使用扩展后电路中的实际子节点执行 Fig.4。
				OptMuxcombWorker worker(module);
				bool did_something = worker.run();
				merged += worker.merged;
				if (!did_expand && !did_something)
					break;
			}
		}

		if (expanded || merged)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Expanded %d repeated $mux inputs.\n", expanded);
		log("Merged %d $mux combinations.\n", merged);
	}
} OptMuxcombPass;

PRIVATE_NAMESPACE_END
