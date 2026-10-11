#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/muxledger.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MuxcombWireCleanup
{
	Module *module;
	pool<IdString> unused;
	explicit MuxcombWireCleanup(Module *module) : module(module) { }
	~MuxcombWireCleanup()
	{
		// 全部 SigBit 索引与函数缓存销毁之后，统一删除临时输出线。
		pool<Wire *> wires;
		for (IdString name : unused) {
			Wire *wire = module->wire(name);
			log_assert(wire != nullptr);
			wires.insert(wire);
		}
		module->remove(wires);
	}
};

// Wang et al., "Optimization of Multiplexer Combination in RTL Logic Synthesis", ISEDA 2023.
// s0 ? (s2 ? b : a) : (s1 ? b : a)  =>  (s0 ? s2 : s1) ? b : a     (Fig.4)
// s0 ? b : (s1 ? b : a)             =>  (s0 | s1) ? b : a          (Fig.6)
struct OptMuxcombWorker
{
	Module *module;
	MuxCostContext &costs;
	SigMap &sigmap;
	MuxWorkspace workspace;
	MuxWorkspace &wire_workspace;
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

	OptMuxcombWorker(Module *module, MuxCostContext &costs, MuxWorkspace &wire_workspace, bool dry_run, bool force, int &cand) : module(module), costs(costs), sigmap(costs.sigmap),
			workspace(costs.resources), wire_workspace(wire_workspace), dry_run(dry_run), force(force), cand(cand)
	{
		if (!workspace.reserve(1024 + (GetSize(costs.use_count) + GetSize(costs.drivers)) * 256))
			return;
		users = costs.use_count;
		for (SigBit bit : costs.output_bits)
			users[bit]++;
		for (SigBit bit : costs.protected_bits)
			if (!costs.output_bits.count(bit))
				users[bit]++;
		for (const auto &entry : costs.drivers)
			drivers[entry.first] = GetSize(entry.second);
		costs.resources.charge(GetSize(users) + GetSize(drivers));
		for (auto cell : module->selected_cells())
			if (cell->type == ID($mux) && costs.mutable_cell(cell)) {
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
		if (c == top || reserved.count(c) || !costs.mutable_cell(c))
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

	// 同一选择计划提供函数成本、实际输入出现次数与最终发射结构。
	struct ControlPlan {
		struct Node {
			IdString type;
			SigBit signal;
			vector<int> inputs;
			Lut4Functions::Ref function;
		};
		MuxCostContext &costs;
		vector<Node> nodes;
		dict<SigBit, int> leaves;
		ControlPlan(MuxCostContext &costs) : costs(costs) { }
		int leaf(SigBit signal)
		{
			if (leaves.count(signal))
				return leaves.at(signal);
			int id = GetSize(nodes);
			nodes.push_back({IdString(), signal, {}, costs.word(signal).at(0)});
			return leaves[signal] = id;
		}
		int operation(IdString type, vector<int> inputs)
		{
			Lut4Functions::Word functions;
			for (int input : inputs)
				functions.push_back(nodes[input].function);
			auto function = costs.functions.apply(type, functions);
			costs.functions.boundary({function});
			int id = GetSize(nodes);
			nodes.push_back({type, SigBit(), inputs, function});
			return id;
		}
		int invert(int id)
		{
			if (nodes[id].type.empty()) {
				if (nodes[id].signal == State::S0)
					return leaf(State::S1);
				if (nodes[id].signal == State::S1)
					return leaf(State::S0);
			}
			return operation(ID($not), {id});
		}
		int mux(int select, int lo, int hi)
		{
			auto is = [&](int id, State state) { return nodes[id].type.empty() && nodes[id].signal == state; };
			if (is(select, State::S0) || lo == hi)
				return lo;
			if (is(select, State::S1))
				return hi;
			if (is(lo, State::S0) && is(hi, State::S1))
				return select;
			if (is(lo, State::S1) && is(hi, State::S0))
				return invert(select);
			if (is(lo, State::S0))
				return operation(ID($and), {select, hi});
			if (is(hi, State::S1))
				return operation(ID($or), {select, lo});
			if (is(hi, State::S0))
				return operation(ID($and), {invert(select), lo});
			if (is(lo, State::S1))
				return operation(ID($or), {invert(select), hi});
			return operation(ID($mux), {lo, hi, select});
		}
		void account(int root, MuxLedger &ledger)
		{
			pool<int> seen;
			vector<int> todo = {root};
			if (nodes[root].type.empty())
				ledger.acquire(nodes[root].signal);
			while (!todo.empty()) {
				int id = todo.back(); todo.pop_back();
				if (!seen.insert(id).second)
					continue;
				for (int input : nodes[id].inputs) {
					if (nodes[input].type.empty())
						ledger.acquire(nodes[input].signal);
					else
						todo.push_back(input);
				}
			}
		}
		SigBit emit(int root, pool<IdString> &modified)
		{
			dict<int, SigBit> memo;
			std::function<SigBit(int)> build = [&](int id) -> SigBit {
				if (memo.count(id))
					return memo.at(id);
				const Node &node = nodes[id];
				if (node.type.empty())
					return node.signal;
				vector<SigBit> inputs;
				for (int input : node.inputs)
					inputs.push_back(build(input));
				Wire *wire = costs.module->addWire(NEW_ID);
				Cell *cell;
				if (node.type == ID($not))
					cell = costs.module->addNot(NEW_ID, inputs[0], wire);
				else if (node.type == ID($and))
					cell = costs.module->addAnd(NEW_ID, inputs[0], inputs[1], wire);
				else if (node.type == ID($or))
					cell = costs.module->addOr(NEW_ID, inputs[0], inputs[1], wire);
				else
					cell = costs.module->addMux(NEW_ID, inputs[0], inputs[1], inputs[2], wire);
				modified.insert(cell->name);
				return memo[id] = SigBit(wire);
			};
			return build(root);
		}
	};

	void find_expansion(Cell *top)
	{
		if (!costs.resources.charge(32))
			return;
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
			if (!workspace.reserve(512 + GetSize(repeated) * 32))
				return;
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
		if (dry_run || costs.resources.exhausted)
			return false;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($mux) && costs.mutable_cell(cell) && !reserved.count(cell))
				find_expansion(cell);
		if (expansions.empty())
			return false;
		int64_t update_work = 1024 + costs.index_work() * 3;
		int64_t wire_bytes = 0;
		for (const auto &expansion : expansions) {
			update_work += GetSize(expansion.a) * 64;
			// 延迟删除的 Wire、稳定名字集合和新增索引条目保持到成本上下文结束。
			wire_bytes += 512 + GetSize(expansion.a) * 256;
		}
		if (costs.resources.limit > 0 && update_work * 2 > costs.resources.limit - costs.resources.used)
			return false;
		if (!costs.resources.reserve_commit(update_work))
			return false;
		costs.resources.restore_reserved = update_work;
		if (!wire_workspace.reserve(wire_bytes)) {
			costs.resources.commit_reserved = 0;
			costs.resources.restore_reserved = 0;
			return false;
		}
		pool<IdString> modified;
		for (auto &expansion : expansions) {
			// Fig.6(a)-(b)：创建常量选择 MUX，并用其输出替换父节点的重复输入。
			Wire *y = module->addWire(NEW_ID, GetSize(expansion.a));
			Cell *child = module->addMux(NEW_ID, expansion.a, expansion.b, expansion.s, y,
					expansion.top->get_src_attribute());
			// 端口的原值在收集阶段已经记下，这一轮没有把它合并掉时按原值恢复
			expansion.top->setPort(expansion.port, y);
			expansion.cell_name = child->name;
			expansion.wire_name = y->name;
			modified.insert(child->name);
			modified.insert(expansion.top->name);
			module->design->select(module, child);
			module->design->select(module, y);
			log("  expanding %s.%s with %s (select %s)\n", log_id(expansion.top),
					log_id(expansion.port), log_id(child), log_signal(expansion.s));
		}
		if (!modified.empty())
			costs.update(modified);
		costs.resources.commit_reserved = 0;
		expanded = GetSize(expansions);
		return expanded != 0;
	}

	void find_combination(Cell *top)
	{
		if (!costs.resources.charge(32))
			return;
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
		if (!workspace.reserve(512 + GetSize(comb.a) * 32))
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
			if (cell->type == ID($mux) && costs.mutable_cell(cell) && !reserved.count(cell))
				find_combination(cell);
		for (int index = 0; index < GetSize(combinations); index++) {
			if (costs.resources.exhausted)
				break;
			const Combination &comb = combinations[index];

			MuxLedger ledger(costs);
			ControlPlan plan(costs);
			int lo = plan.leaf(comb.lo.s), hi = plan.leaf(comb.hi.s);
			if (comb.hi.inverted)
				hi = plan.invert(hi);
			int select = plan.mux(plan.leaf(comb.s), lo, hi);
			Lut4Functions::Word a = costs.word(comb.a), b = costs.word(comb.b), outputs;
			for (int i = 0; i < GetSize(a); i++)
				outputs.push_back(costs.functions.mux(a[i], b[i], plan.nodes[select].function));
			ledger.drop_cell(comb.lo.cell);
			ledger.drop_cell(comb.hi.cell);
			ledger.replace_outputs(comb.top, outputs);
			ledger.acquire(comb.a);
			ledger.acquire(comb.b);
			plan.account(select, ledger);
			ledger.settle();
			int64_t gain = ledger.gain, dead = ledger.dead_result;
			int64_t removed = ledger.removed_gain, added = ledger.added_cost;

			// 账本预测的净收益大于零才施加，-force 取消这道门槛
			bool accept = ledger.valid && (force || gain > 0);
			log_candidate(!accept ? "reject" : (force ? "forced" : "accept"),
					gain, removed, dead, added, !ledger.valid ? "unsupported" : accept ? "kept" : "no_gain");
			if (!accept)
				continue;

			if (!dry_run) {
				pool<IdString> modified = {comb.top->name, comb.lo.cell->name, comb.hi.cell->name};
				SigBit selected = plan.emit(select, modified);
				comb.top->setPort(ID::A, comb.a);
				comb.top->setPort(ID::B, comb.b);
				comb.top->setPort(ID::S, selected);
				for (auto child : {comb.lo.cell, comb.hi.cell}) {
					log("  merging %s into %s\n", log_id(child), log_id(comb.top));
					module->remove(child);
				}
				merged_tops.insert(comb.top->name);
				costs.update(modified);
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
		log("MuxLedger prices the original and replacement LUT4 function DAGs, including\n");
		log("the changed parent mux, selection logic and shared functions. A normal\n");
		log("candidate requires positive gain. Protected signals, multiple drivers and\n");
		log("combinational cycles remain boundaries, including with -force.\n");
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

			// 候选类型集合为{$mux}，至少两个选中对象；达到阈值立即停止扫描。
			MuxCostContext costs(module);
			if (!costs.type_scan([](const Cell *cell) { return cell->type == ID($mux); }, 2, "muxcomb"))
				continue;
			costs.refresh();

			// 候选序号在一个模块内跨轮次递增，便于在日志里对照
			int cand = 0;
			MuxcombWireCleanup wire_cleanup(module);
			MuxWorkspace wire_workspace(costs.resources);

			if (dry_run) {
				// 展开会新建单元并改写端口，-dry-run 下只做匹配与结算，
				// 列出当前连接上的候选
				OptMuxcombWorker worker(module, costs, wire_workspace, dry_run, force, cand);
				worker.run();
				merged += worker.merged;
				predicted_gain += worker.predicted_gain;
				continue;
			}

			while (!costs.resources.exhausted) {
				OptMuxcombWorker expansion_worker(module, costs, wire_workspace, dry_run, force, cand);
				bool did_expand = expansion_worker.expand();
				expanded += expansion_worker.expanded;
				if (expand_only) {
					costs.resources.restore_reserved = 0;
					if (!did_expand)
						break;
					continue;
				}
				// 重新建立索引，使用扩展后电路中的实际子节点执行 Fig.4。
				OptMuxcombWorker worker(module, costs, wire_workspace, dry_run, force, cand);
				bool did_something = worker.run();
				merged += worker.merged;
				predicted_gain += worker.predicted_gain;

				// 展开只有被同一轮的 run() 合并掉才算回收。没有被合并掉的把父节点的
				// 端口恢复成原值，并删除新建的单元与它的输出线，电路里不留多余的单元。
				// 新建的单元一律按名字查回来：run() 可能已经把它删掉，此时它的地址会被
				// 后来的单元复用，按指针判断会认错单元、删掉别人的驱动。
				int recycled_here = 0;
				pool<IdString> restored;
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
					// 未使用的展开按实际函数依赖记录成本，并恢复原有连接。
					int64_t cost = GetSize(expansion_worker.costs.cells.at(cell->name).dependencies);
					expansion_worker.log_candidate("reject", -cost, 0, 0, cost, "rollback");
					// 父节点被别的合并删掉时端口已经没有意义，只清掉新建的单元
					Cell *top = module->cell(expansion.top_name);
					if (top == nullptr) {
						log("  removing expansion %s, its parent is gone\n", log_id(cell));
					} else {
						top->setPort(expansion.port, expansion.saved);
						restored.insert(top->name);
						log("  rolling back expansion %s of %s.%s\n", log_id(cell),
								log_id(top), log_id(expansion.port));
					}
					restored.insert(cell->name);
					module->remove(cell);
					wire_cleanup.unused.insert(expansion.wire_name);
					rolled_back++;
				}
				recycled += recycled_here;
				costs.resources.commit_reserved = costs.resources.restore_reserved;
				costs.resources.restore_reserved = 0;
				if (!restored.empty()) {
					costs.update(restored);
					costs.resources.account(costs.index_work(), MuxResources::Commit);
				}
				costs.resources.commit_reserved = 0;

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
		log("Ledger predicted gain %lld LUT4 units in total.\n", (long long)predicted_gain);
	}
} OptMuxcombPass;

PRIVATE_NAMESPACE_END
