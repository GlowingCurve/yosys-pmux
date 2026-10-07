#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/muxledger.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Wang et al., "Optimization of Multiplexer Combination in RTL Logic Synthesis", ISEDA 2023.
// s0 ? (s2 ? b : a) : (s1 ? b : a)  =>  (s0 ? s2 : s1) ? b : a     (Fig.4)
// s0 ? b : (s1 ? b : a)             =>  (s0 | s1) ? b : a          (Fig.6)
struct OptMuxcombWorker
{
	Module *module;
	SigMap sigmap;
	bool dry_run;
	bool force;
	int &cand;
	dict<SigBit, int> users;
	dict<SigBit, int> drivers;
	dict<SigBit, std::pair<Cell*, int>> mux_driver;
	pool<Cell*> reserved;
	pool<IdString> merged_tops;  // 本次 run() 改写端口之后保留的父节点，按名字记
	int expanded = 0;
	int merged = 0;
	int64_t predicted_gain = 0;

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

	// 一次展开：改写父节点的一个端口，让新建的常量选择 $mux 顶替重复的数据输入。
	// 撤销需要的全部信息。新建的单元与输出线用名字记身份：run() 可能已经把新建的单元
	// 删掉，此时指针指向的地址会被后来的单元复用，任何解引用都可能作用在别的单元上。
	struct Expansion {
		Cell *top = nullptr;        // 展开时的父节点，只在本轮 run() 之前有效
		IdString top_name;          // 父节点的名字，撤销时按名字查回来
		IdString port;
		SigSpec a, b;
		SigBit s;
		SigSpec saved;              // 端口改写之前的取值
		IdString cell_name;         // 新建 $mux 的名字
		IdString wire_name;         // 新建输出线的名字
	};
	vector<Expansion> expansions;

	OptMuxcombWorker(Module *module, bool dry_run, bool force, int &cand) : module(module), sigmap(module),
			dry_run(dry_run), force(force), cand(cand)
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

	// invert() 将要新建的单元个数：常量取反不新建单元，其余情形一个一位宽 $not
	int64_t invert_cost(SigBit bit)
	{
		return (bit == State::S0 || bit == State::S1) ? 0 : 1;
	}

	// invert() 的预测版本：常量取反的结果还是常量，其余情形新建一个 $not 单元。
	// 新建出来的信号位非恒定，也不会与 lo 相等，用一个与 lo 不同的无连线状态位代表它
	static SigBit predicted_invert(SigBit bit, SigBit lo)
	{
		if (bit == State::S0)
			return State::S1;
		if (bit == State::S1)
			return State::S0;
		return lo == State::Sx ? SigBit(State::Sz) : SigBit(State::Sx);
	}

	// mux_bit 的预测版本：不创建任何单元，返回它将会创建的单元的代价之和。
	// 分支结构与 mux_bit 逐字对应；新建的门都是一位宽，按 muxledger.h 的口径各记 1
	int64_t control_cost(SigBit s, SigBit lo, SigBit hi)
	{
		if (s == State::S0)
			return 0;                    // 直接返回 lo
		if (s == State::S1)
			return 0;                    // 直接返回 hi
		if (lo == hi)
			return 0;                    // 直接返回 lo
		if (lo == State::S0 && hi == State::S1)
			return 0;                    // 直接返回 s
		if (lo == State::S1 && hi == State::S0)
			return invert_cost(s);       // Not(s)
		if (lo == State::S0)
			return 1;                    // And(s, hi)
		if (hi == State::S1)
			return 1;                    // Or(s, lo)
		if (hi == State::S0)
			return invert_cost(s) + 1;   // And(Not(s), lo)
		if (lo == State::S1)
			return invert_cost(s) + 1;   // Or(Not(s), hi)
		return 1;                        // Mux(lo, hi, s)
	}

	// 这次合并新建的整个选择信号的代价：hi 分支反相时先取反一位，再进 mux_bit
	int64_t select_cost(const Combination &comb)
	{
		// comb.lo.inverted 恒为 false，lo 就是 comb.lo.s
		if (!comb.hi.inverted)
			return control_cost(comb.s, comb.lo.s, comb.hi.s);
		return invert_cost(comb.hi.s)
				+ control_cost(comb.s, comb.lo.s, predicted_invert(comb.hi.s, comb.lo.s));
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
			Expansion expansion;
			expansion.top = top;
			expansion.top_name = top->name;
			expansion.port = port;
			expansion.a = child.a;
			expansion.b = child.b;
			expansion.s = s;
			expansion.saved = top->getPort(port);
			expansions.push_back(expansion);
			reserved.insert(top);
			reserved.insert(child.cell);
			return;
		}
	}

	bool expand()
	{
		// -dry-run 不创建单元，也不改写端口
		if (dry_run)
			return false;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($mux) && !cell->get_bool_attribute(ID::keep) && !reserved.count(cell))
				find_expansion(cell);
		for (auto &expansion : expansions) {
			if (!expansion.cell_name.empty())
				continue;
			// Fig.6(a)-(b)：创建常量选择 MUX，并用其输出替换父节点的重复输入。
			Wire *y = module->addWire(NEW_ID, GetSize(expansion.a));
			Cell *child = module->addMux(NEW_ID, expansion.a, expansion.b, expansion.s, y,
					expansion.top->get_src_attribute());
			// 端口的原值在收集阶段已经记下，这一轮没有把它合并掉时按原值恢复
			expansion.top->setPort(expansion.port, y);
			expansion.cell_name = child->name;
			expansion.wire_name = y->name;
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

	// 输出一条候选记录：前缀固定，字段之间用空格分隔，cand 在一个模块内递增
	void log_candidate(const char *decision, int64_t gain, int64_t removed, int64_t dead,
			int64_t added, const char *note)
	{
		log("MUXLEDGER pass=opt_muxcomb module=%s cand=%d decision=%s gain=%lld removed=%lld dead=%lld added=%lld note=%s\n",
				log_id(module), ++cand, decision, (long long)gain, (long long)removed,
				(long long)dead, (long long)added, note);
	}

	bool run()
	{
		// 匹配期间保持连接关系不变，每个单元只参加一次变换。
		for (auto cell : module->selected_cells())
			if (cell->type == ID($mux) && !cell->get_bool_attribute(ID::keep) && !reserved.count(cell))
				find_combination(cell);
		for (int index = 0; index < GetSize(combinations); index++) {
			const Combination &comb = combinations[index];

			// 新建控制逻辑的代价先预测出来，账本判定通过之后才真的创建
			int64_t added = select_cost(comb);
			int64_t removed = MuxLedger::cell_cost(comb.lo.cell) + MuxLedger::cell_cost(comb.hi.cell);

			// 一次决策用一个新建的账本：先计划删除两个子节点、改写父节点的两个数据端口，
			// 再计划占用合并之后的数据信号与新的选择逻辑读到的控制信号，最后结算。
			// 父节点保留，$mux 按位宽计价，端口改写不改变它的代价，所以不用 sub_cost。
			MuxLedger ledger(module);
			ledger.drop_cell(comb.lo.cell);
			ledger.drop_cell(comb.hi.cell);
			ledger.drop_port(comb.top, ID::A);
			ledger.drop_port(comb.top, ID::B);
			ledger.acquire(comb.a);
			ledger.acquire(comb.b);
			// 两个子节点的选择端被删除之后，驱动它们的单元仍然被新的选择逻辑读到。
			// 这一笔漏记会让还活着的驱动单元在 dead_cost() 里被算成死亡，收益因此虚高。
			ledger.acquire(comb.s);
			ledger.acquire(comb.lo.s);
			ledger.acquire(comb.hi.s);
			ledger.add_cost(added);
			int64_t gain = ledger.net_gain();
			int64_t dead = ledger.dead_cost();

			// 账本预测的净收益大于零才施加，-force 取消这道门槛
			bool accept = force || gain > 0;
			log_candidate(!accept ? "reject" : (force ? "forced" : "accept"),
					gain, removed, dead, added, accept ? "kept" : "no_gain");
			if (!accept)
				continue;

			if (!dry_run) {
				// Fig.4、Fig.6(b)-(d)：把数据选择转移到一位控制信号，并化简常量支路。
				// 反相的 hi 分支在这里才创建取反单元，select_cost() 已经把它计入代价。
				SigBit lo = comb.lo.s;
				SigBit hi = comb.hi.inverted ? invert(comb.hi.s) : comb.hi.s;
				comb.top->setPort(ID::A, comb.a);
				comb.top->setPort(ID::B, comb.b);
				comb.top->setPort(ID::S, mux_bit(comb.s, lo, hi));
				for (auto child : {comb.lo.cell, comb.hi.cell}) {
					log("  merging %s into %s\n", log_id(child), log_id(comb.top));
					module->remove(child);
				}
				merged_tops.insert(comb.top->name);
				merged++;
			}
			predicted_gain += gain;
		}
		return merged != 0;
	}
};

struct OptMuxcombPass : public Pass {
	OptMuxcombPass() : Pass("opt_muxcomb", "merge $mux cells that select between the same pair of inputs") { }
	void help() override
	{
		log("\n");
		log("    opt_muxcomb [-expand] [-dry-run] [-force] [selection]\n");
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
		log("Whether a combination pays off is decided with the MuxLedger of\n");
		log("passes/opt/muxledger.h: the cost of the two child $mux cells plus the cost of\n");
		log("the cells that lose all their users, minus the cost of the new select logic,\n");
		log("has to be greater than zero. The new select logic covers the $not, $and and\n");
		log("$or gates for the constant data branches, the 1-bit $mux of the two child\n");
		log("select signals, and the $not inverting a swapped child select.\n");
		log("\n");
		log("An expansion that the same round does not combine away is rolled back: the\n");
		log("rewritten port gets its old value back, and the new $mux cell and its output\n");
		log("wire are removed. No expansion is left behind in the circuit, so the cost of\n");
		log("an expansion only remains when a combination actually consumes it.\n");
		log("\n");
		log("Every candidate is reported as a log line starting with 'MUXLEDGER', holding\n");
		log("the ledger gain and the outcome: 'kept' for an applied combination, 'no_gain'\n");
		log("for one that fails the threshold, and 'rollback' for an undone expansion.\n");
		log("\n");
		log("    -expand\n");
		log("        perform only the Fig.6(a)-(b) expansion, retaining the new muxes\n");
		log("        and their connections for inspection or subsequent combination\n");
		log("\n");
		log("    -dry-run\n");
		log("        match the candidates and report the ledger results, do not modify the\n");
		log("        module. No expansion is performed, even together with -expand, and\n");
		log("        the candidates are the ones the current connections offer. Given\n");
		log("        together with -force, the pass behaves as with -dry-run alone.\n");
		log("\n");
		log("    -force\n");
		log("        ignore the 'gain greater than zero' requirement and apply every\n");
		log("        candidate, reporting its decision as 'forced'.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MUXCOMB pass (merge muxes over the same input pair).\n");
		bool expand_only = false;
		bool dry_run = false, force = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-expand") {
				expand_only = true;
				continue;
			}
			if (args[argidx] == "-dry-run") {
				dry_run = true;
				continue;
			}
			if (args[argidx] == "-force") {
				force = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// 两个选项同时给出时按 -dry-run 处理：忽略 -force，模块保持不变
		if (dry_run)
			force = false;

		int expanded = 0;
		int merged = 0;
		int recycled = 0, rolled_back = 0;
		int64_t predicted_gain = 0;

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;

			// 候选序号在一个模块内跨轮次递增，便于在日志里对照
			int cand = 0;

			if (dry_run) {
				// 展开会新建单元并改写端口，-dry-run 下只做匹配与结算，
				// 列出当前连接上的候选
				OptMuxcombWorker worker(module, dry_run, force, cand);
				worker.run();
				merged += worker.merged;
				predicted_gain += worker.predicted_gain;
				continue;
			}

			while (true) {
				OptMuxcombWorker expansion_worker(module, dry_run, force, cand);
				bool did_expand = expansion_worker.expand();
				expanded += expansion_worker.expanded;
				if (expand_only) {
					if (!did_expand)
						break;
					continue;
				}
				// 重新建立索引，使用扩展后电路中的实际子节点执行 Fig.4。
				OptMuxcombWorker worker(module, dry_run, force, cand);
				bool did_something = worker.run();
				merged += worker.merged;
				predicted_gain += worker.predicted_gain;

				// 展开只有被同一轮的 run() 合并掉才算回收。没有被合并掉的把父节点的
				// 端口恢复成原值，并删除新建的单元与它的输出线，电路里不留多余的单元。
				// 新建的单元一律按名字查回来：run() 可能已经把它删掉，此时它的地址会被
				// 后来的单元复用，按指针判断会认错单元、删掉别人的驱动。
				int recycled_here = 0;
				for (auto &expansion : expansion_worker.expansions) {
					if (expansion.cell_name.empty())
						continue;
					Cell *cell = module->cell(expansion.cell_name);
					// 查不到就是已经被 run() 合并掉，展开被回收
					if (cell == nullptr) {
						recycled_here++;
						continue;
					}
					// 新建单元自己成了某个合并的父节点，这一轮保留
					if (worker.merged_tops.count(expansion.cell_name)) {
						recycled_here++;
						continue;
					}
					// 新建单元的成本按账本口径记为新增代价，撤销之后这笔代价不再存在
					int64_t cost = MuxLedger::cell_cost(cell);
					expansion_worker.log_candidate("reject", -cost, 0, 0, cost, "rollback");
					// 父节点被别的合并删掉时端口已经没有意义，只清掉新建的单元
					Cell *top = module->cell(expansion.top_name);
					if (top == nullptr) {
						log("  removing expansion %s, its parent is gone\n", log_id(cell));
					} else {
						top->setPort(expansion.port, expansion.saved);
						log("  rolling back expansion %s of %s.%s\n", log_id(cell),
								log_id(top), log_id(expansion.port));
					}
					module->remove(cell);
					Wire *w = module->wire(expansion.wire_name);
					if (w != nullptr)
						module->remove({w});
					rolled_back++;
				}
				recycled += recycled_here;

				// 展开全部被撤销、又没有发生别的合并时，电路与这一轮开始时一样，
				// 再循环一次只会重复同样的展开，就此结束
				if (!did_something && recycled_here == 0)
					break;
			}
		}

		// -expand 保留新建的 mux，其余的展开要么被回收，要么已经撤销
		if (merged || (expand_only && expanded))
			design->scratchpad_set_bool("opt.did_something", true);
		if (dry_run)
			log("Dry run: no module is modified.\n");
		log("Merged %d $mux combinations.\n", merged);
		log("Expanded %d repeated $mux inputs.\n", expanded);
		log("Recycled %d expansions, rolled back %d.\n", recycled, rolled_back);
		log("Ledger predicted gain %lld cells in total.\n", (long long)predicted_gain);
	}
} OptMuxcombPass;

PRIVATE_NAMESPACE_END
