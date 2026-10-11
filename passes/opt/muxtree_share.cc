#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/muxledger.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// 使用共享节点的字级 MUX DAG。
struct MuxDag
{
	struct Node {
		SigSpec leaf;
		SigBit sel;
		int lo = -1, hi = -1;
	};

	vector<Node> nodes;
	dict<SigSpec, int> leaf_cache;
	dict<std::tuple<SigBit, int, int>, int> mux_cache;

	int leaf(const SigSpec &sig)
	{
		auto it = leaf_cache.find(sig);
		if (it != leaf_cache.end())
			return it->second;
		nodes.push_back(Node());
		nodes.back().leaf = sig;
		return leaf_cache[sig] = GetSize(nodes) - 1;
	}

	// 保留每个数据字的实际常量状态。
	int mux(SigBit sel, int lo, int hi)
	{
		if (sel == State::S0 || lo == hi)
			return lo;
		if (sel == State::S1)
			return hi;
		auto key = std::make_tuple(sel, lo, hi);
		auto it = mux_cache.find(key);
		if (it != mux_cache.end())
			return it->second;
		nodes.push_back(Node());
		nodes.back().sel = sel;
		nodes.back().lo = lo;
		nodes.back().hi = hi;
		return mux_cache[key] = GetSize(nodes) - 1;
	}

	// return d[k] where k is the value of s (LSB first), GetSize(d) == 2^GetSize(s)
	int tree(vector<int> d, const SigSpec &s)
	{
		for (auto sel : s) {
			vector<int> next;
			for (int k = 0; k < GetSize(d); k += 2)
				next.push_back(mux(sel, d[k], d[k+1]));
			d.swap(next);
		}
		log_assert(GetSize(d) == 1);
		return d[0];
	}

	// children are always created before their parents
	vector<SigSpec> emit(Module *module, int width, std::pair<int, int> roots)
	{
		pool<int> reachable;
		vector<int> todo = {roots.first, roots.second};
		while (!todo.empty()) {
			int id = todo.back(); todo.pop_back();
			if (!reachable.insert(id).second)
				continue;
			if (nodes[id].lo != -1) {
				todo.push_back(nodes[id].lo);
				todo.push_back(nodes[id].hi);
			}
		}
		vector<SigSpec> sig(GetSize(nodes));
		for (int id = 0; id < GetSize(nodes); id++) {
			if (!reachable.count(id))
				continue;
			const Node &n = nodes[id];
			if (n.lo == -1 && n.hi == -1) {
				sig[id] = n.leaf;
				continue;
			}
			sig[id] = module->addWire(NEW_ID, width);
			module->addMux(NEW_ID, sig[n.lo], sig[n.hi], n.sel, sig[id]);
		}
		return sig;
	}
};

// a $pmux whose select bits are "base == value", tabulated over all values of base
struct PmuxTable
{
	Cell *cell;
	SigSpec base;
	vector<SigSpec> data;
};

struct MuxtreeShareWorker
{
	Module *module;
	MuxCostContext &costs;
	SigMap &sigmap;
	bool dry_run;                 // 只做匹配与账本结算，不改动模块
	bool force;                   // 取消 gain 大于零的门槛，全部候选都参与配对
	int shared_pairs = 0;         // 被选中并施加的候选个数
	int candidate_count = 0;      // 枚举出的候选个数
	int64_t predicted_gain = 0;   // 选中候选的账本收益之和
	int candidate_budget = 20000;
	MuxWorkspace workspace;

	// 一个 (p, q, j) 候选的结算记录，最后逐行输出
	struct Candidate {
		int p, q, j;
		int64_t gain = 0;      // 账本收益：删除所得 + 连带死亡所得 - 共享树代价
		int64_t removed = 0;   // 删除集合释放的共享 LUT4 函数
		int64_t dead = 0;      // 连带死亡所得，失去全部使用者的单元代价之和
		int64_t added = 0;     // 新增 LUT4 函数的代价
		int64_t update_work = 0;
		bool feasible = true;
		const char *decision = "reject";
		const char *note = "no_gain";
	};

	MuxtreeShareWorker(Module *module, MuxCostContext &costs, bool dry_run, bool force) :
			module(module), costs(costs), sigmap(costs.sigmap), dry_run(dry_run), force(force), workspace(costs.resources) { }

	void run()
	{
		dict<std::pair<SigSpec, int>, vector<PmuxTable>> groups;
		for (auto cell : module->selected_cells()) {
			PmuxTable t;
			if (cell->type == ID($pmux) && decode(cell, t))
				groups[std::make_pair(t.base, cell->getParam(ID::WIDTH).as_int())].push_back(t);
		}

		for (auto &it : groups)
			if (GetSize(it.second) >= 2)
				share_group(it.second);
	}
	// decompose a select bit into "base == value", value == -1 if the compare is never true
	bool match_select(SigBit s, SigSpec &base, int &value)
	{
		Cell *cmp = costs.unique_driver(s);
		if (cmp == nullptr)
			return false;

		if (!cmp->type.in(ID($eq), ID($logic_not)) || sigmap(cmp->getPort(ID::Y)[0]) != sigmap(s))
			return false;

		SigSpec a = sigmap(cmp->getPort(ID::A));
		SigSpec b;
		if (cmp->type == ID($logic_not)) {
			b = Const(0, GetSize(a));
		} else {
			b = sigmap(cmp->getPort(ID::B));
			if (a.is_fully_const())
				std::swap(a, b);
			if (!b.is_fully_def())
				return false;
			bool is_signed = cmp->getParam(ID::A_SIGNED).as_bool() && cmp->getParam(ID::B_SIGNED).as_bool();
			if (is_signed && GetSize(a) != GetSize(b))
				return false;
		}

		if (GetSize(a) == 0 || GetSize(a) > 8)
			return false;

		// "a == b" with b zero-extended to the width of a, or the other way around
		value = 0;
		for (int i = 0; i < GetSize(b); i++) {
			if (b[i] != State::S1)
				continue;
			if (i >= GetSize(a)) {
				value = -1;
				break;
			}
			value |= 1 << i;
		}
		base = a;
		return true;
	}

	bool decode(Cell *cell, PmuxTable &t)
	{
		if (!costs.resources.charge(32))
			return false;
		if (!costs.mutable_cell(cell))
			return false;
		int width = cell->getParam(ID::WIDTH).as_int();
		SigSpec sig_a = sigmap(cell->getPort(ID::A));
		SigSpec sig_b = sigmap(cell->getPort(ID::B));
		SigSpec sig_s = sigmap(cell->getPort(ID::S));

		vector<int> values;
		for (auto s : sig_s) {
			SigSpec this_base;
			int value;
			if (!match_select(s, this_base, value))
				return false;
			if (t.base.empty())
				t.base = this_base;
			else if (this_base != t.base)
				return false;
			values.push_back(value);
		}
		if (t.base.empty())
			return false;
		for (SigBit bit : t.base)
			if (!bit.wire && bit != State::S0 && bit != State::S1)
				return false;

		// values not matched by any select bit take A, two bits with the same value would be active at once
		t.cell = cell;
		int64_t entries = int64_t(1) << GetSize(t.base);
		if (!workspace.reserve(entries * (64 + width * 16)) || !costs.resources.charge(entries))
			return false;
		t.data.assign(entries, sig_a);
		pool<int> seen;
		for (int i = 0; i < GetSize(values); i++) {
			if (values[i] < 0)
				continue;
			if (seen.count(values[i]))
				return false;
			seen.insert(values[i]);
			t.data[values[i]] = sig_b.extract(i * width, width);
		}
		return true;
	}

	// q(v) == p(v ^ 2^j) for most v: select the common words with the other bits, then swap on bit j
	std::pair<int, int> share(MuxDag &dag, const PmuxTable &p, const PmuxTable &q, int j)
	{
		int n = GetSize(p.base);
		SigBit sel_j = p.base[j];
		SigSpec sel_rest = p.base;
		sel_rest.remove(j);

		vector<int> leaf0, leaf1;
		for (int u = 0; u < (1 << (n - 1)); u++) {
			int low = u & ((1 << j) - 1);
			int v0 = ((u >> j) << (j + 1)) | low;
			int v1 = v0 | (1 << j);
			// t0 is p(v) when bit j is 0 and q(v) when it is 1, t1 the other way round
			leaf0.push_back(dag.mux(sel_j, dag.leaf(p.data[v0]), dag.leaf(q.data[v1])));
			leaf1.push_back(dag.mux(sel_j, dag.leaf(q.data[v0]), dag.leaf(p.data[v1])));
		}

		int t0 = dag.tree(leaf0, sel_rest);
		int t1 = dag.tree(leaf1, sel_rest);
		return std::make_pair(dag.mux(sel_j, t0, t1), dag.mux(sel_j, t1, t0));
	}

	// whether sig combinationally depends on any bit in target
	bool depends_on(const SigSpec &sig, const pool<SigBit> &target)
	{
		pool<SigBit> visited;
		vector<SigBit> queue;
		for (auto bit : sigmap(sig))
			if (bit.wire)
				queue.push_back(bit);

		while (!queue.empty()) {
			if (!costs.resources.charge(1))
				return true;
			SigBit bit = queue.back();
			queue.pop_back();
			if (target.count(bit))
				return true;
			if (visited.count(bit))
				continue;
			visited.insert(bit);

			Cell *cell = costs.unique_driver(bit);
			if (cell == nullptr || RTLIL::builtin_ff_cell_types().count(cell->type))
				continue;
			for (auto &conn : cell->connections())
				if (cell->input(conn.first))
					for (auto in : sigmap(conn.second))
						if (in.wire)
							queue.push_back(in);
		}
		return false;
	}

	// sharing makes each output depend on the data of the other
	bool may_share(const PmuxTable &p, const PmuxTable &q)
	{
		pool<SigBit> p_y, q_y;
		for (auto bit : sigmap(p.cell->getPort(ID::Y)))
			p_y.insert(bit);
		for (auto bit : sigmap(q.cell->getPort(ID::Y)))
			q_y.insert(bit);

		SigSpec p_data, q_data;
		for (auto &sig : p.data)
			p_data.append(sig);
		for (auto &sig : q.data)
			q_data.append(sig);
		return !depends_on(p_data, q_y) && !depends_on(q_data, p_y);
	}

	void price(Candidate &candidate, const PmuxTable &p, const PmuxTable &q)
	{
		MuxWorkspace scratch(costs.resources);
		int64_t entries = GetSize(p.data), width = GetSize(p.data.front());
		if (!costs.resources.charge(entries * 4) || !scratch.reserve(entries * (512 + width * 64))) {
			candidate.feasible = false;
			candidate.note = "budget";
			return;
		}
		MuxLedger ledger(costs);
		ledger.alias_commit = true;
		ledger.drop_cell(p.cell);
		ledger.drop_cell(q.cell);
		MuxDag dag;
		auto roots = share(dag, p, q, candidate.j);
		using Word = Lut4Functions::Word;
		dict<int, Word> memo;
		std::function<Word(int)> build = [&](int id) -> Word {
			auto found = memo.find(id);
			if (found != memo.end())
				return found->second;
			const auto &node = dag.nodes[id];
			if (node.lo == -1 && node.hi == -1)
				return memo[id] = costs.word(node.leaf);
			Word lo = build(node.lo), hi = build(node.hi), result;
			for (int child : {node.lo, node.hi})
				if (dag.nodes[child].lo == -1 && dag.nodes[child].hi == -1)
					ledger.acquire(dag.nodes[child].leaf);
			ledger.acquire(node.sel);
			auto select = costs.word(node.sel).at(0);
			for (int i = 0; i < GetSize(lo); i++)
				result.push_back(costs.functions.mux(lo[i], hi[i], select));
			costs.functions.boundary(result);
			return memo[id] = result;
		};
		ledger.add_outputs(p.cell->getPort(ID::Y), build(roots.first));
		ledger.add_outputs(q.cell->getPort(ID::Y), build(roots.second));
		for (int root : {roots.first, roots.second})
			if (dag.nodes[root].lo == -1 && dag.nodes[root].hi == -1)
				ledger.acquire(dag.nodes[root].leaf);
		candidate.feasible = ledger.settle();
		candidate.update_work = costs.resources.commit_reserved;
		candidate.removed = ledger.removed_gain;
		candidate.dead = ledger.dead_result;
		candidate.added = ledger.added_cost;
		candidate.gain = ledger.gain;
		if (!candidate.feasible)
			candidate.note = "unsupported";
	}

	// 每个候选按待发射 DAG 的实际连接结算，再按收益顺序配对。
	void share_group(const vector<PmuxTable> &tables)
	{
		int n = GetSize(tables[0].base);

		vector<Candidate> rows;
		for (int p = 0; p < GetSize(tables) && candidate_budget > 0 && !costs.resources.exhausted; p++)
		for (int q = p + 1; q < GetSize(tables) && candidate_budget > 0 && !costs.resources.exhausted; q++) {
			for (int j = 0; j < n && candidate_budget > 0 && !costs.resources.exhausted; j++, candidate_budget--) {
				if (!workspace.reserve(sizeof(Candidate) * 2 + 32))
					break;
				Candidate c;
				c.p = p;
				c.q = q;
				c.j = j;
				price(c, tables[p], tables[q]);
				rows.push_back(c);
			}
		}

		// 进入贪心配对的是 gain 大于零的候选，-force 时门槛取消、全部候选都参与。
		// 按 gain 降序排序，gain 相同时按 (p, q, j) 升序，配对结果与枚举顺序无关。
		vector<int> order;
		for (int i = 0; i < GetSize(rows); i++)
			if (rows[i].feasible && (force || rows[i].gain > 0))
				order.push_back(i);
		std::sort(order.begin(), order.end(), [&](int a, int b) {
			const Candidate &x = rows[a], &y = rows[b];
			if (x.gain != y.gain)
				return x.gain > y.gain;
			return std::make_tuple(x.p, x.q, x.j) < std::make_tuple(y.p, y.q, y.j);
		});

		pool<int> used;
		for (auto i : order) {
			Candidate &c = rows[i];
			if (used.count(c.p) || used.count(c.q)) {
				c.note = "conflict";
				continue;
			}
			if (!may_share(tables[c.p], tables[c.q])) {
				c.note = "cycle";
				continue;
			}
			if (!dry_run) {
				price(c, tables[c.p], tables[c.q]);
				if (!c.feasible || (!force && c.gain <= 0)) {
					c.note = c.feasible ? "no_gain" : "unsupported";
					continue;
				}
			}

			used.insert(c.p);
			used.insert(c.q);
			c.decision = force ? "forced" : "accept";
			c.note = "kept";
			if (!dry_run) {
				log_assert(costs.resources.reserve_commit(c.update_work));
				apply(tables[c.p], tables[c.q], c.j);
				costs.refresh();
				costs.resources.commit_reserved = 0;
			}
			shared_pairs++;
			predicted_gain += c.gain;
		}

		// 候选指枚举出的全部 (p, q, j) 三元组：gain 不大于零的三元组同样输出一行 reject/no_gain，
		// 方便核对账本口径，它们不参与贪心配对；-force 时门槛取消，全部三元组都参与。
		candidate_count += GetSize(rows);

		// 每个候选输出一行：被选中的记 kept，因为 cell 已被别的候选占用而落选的记 conflict，
		// 会成环的记 cycle，没进贪心的 gain 不大于零的三元组保持默认的 reject/no_gain
		for (int i = 0; i < GetSize(rows); i++) {
			const Candidate &c = rows[i];
			log("MUXLEDGER pass=muxtree_share module=%s cand=%d decision=%s gain=%lld removed=%lld dead=%lld added=%lld note=%s\n",
					log_id(module), i, c.decision, (long long)c.gain, (long long)c.removed,
					(long long)c.dead, (long long)c.added, c.note);
		}
	}

	void apply(const PmuxTable &p, const PmuxTable &q, int j)
	{
		int width = p.cell->getParam(ID::WIDTH).as_int();
		MuxDag dag;
		auto roots = share(dag, p, q, j);
		vector<SigSpec> sig = dag.emit(module, width, roots);

		SigSpec p_y = p.cell->getPort(ID::Y);
		SigSpec q_y = q.cell->getPort(ID::Y);
		module->remove(p.cell);
		module->remove(q.cell);
		module->connect(p_y, sig[roots.first]);
		module->connect(q_y, sig[roots.second]);
	}
};

struct MuxtreeSharePass : public Pass {
	MuxtreeSharePass() : Pass("muxtree_share", "share the select trees of $pmux pairs that differ in one select bit") { }
	void help() override
	{
		log("\n");
		log("    muxtree_share [options] [selection]\n");
		log("\n");
		log("This pass looks for pairs of $pmux cells whose select bits are $eq/$logic_not\n");
		log("cells comparing the same signal 'base' against constants, and where the second\n");
		log("$pmux mostly selects the data the first one selects with bit 'base[j]' inverted.\n");
		log("Both cells are then rebuilt as two mux trees over the other bits of 'base',\n");
		log("shared by both outputs and swapped by 'base[j]' at the root. Values where the\n");
		log("two cells disagree get an extra mux on 'base[j]' at the leaves.\n");
		log("\n");
		log("A pair is only rebuilt if the sharing pays off, measured with the MuxLedger of\n");
		log("passes/opt/muxledger.h: the gain of dropping the two $pmux cells plus the gain\n");
		log("of the $eq/$logic_not cells that lose all their users, minus the cost of the\n");
		log("muxes of the new shared tree, has to be greater than zero.\n");
		log("\n");
		log("Every candidate (a pair of cells together with one bit 'base[j]') is reported\n");
		log("as a log line starting with 'MUXLEDGER', holding the gain and the reason for the\n");
		log("decision (kept, no_gain, cycle or conflict).\n");
		log("\n");
		log("    -dry-run\n");
		log("        Match the candidates and report the ledger results, do not modify the\n");
		log("        module.\n");
		log("\n");
		log("    -force\n");
		log("        Ignore the 'gain greater than zero' requirement and apply all\n");
		log("        candidates, reporting their decisions as 'forced'.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool dry_run = false, force = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
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

		// 两个选项同时给出时按 -dry-run 处理：门槛也不取消，记录行反映账本原本的决定
		if (dry_run)
			force = false;

		log_header(design, "Executing MUXTREE_SHARE pass (share select trees of $pmux pairs).\n");

		int candidate_count = 0, shared_pairs = 0;
		int64_t predicted_gain = 0;
		for (auto module : design->selected_modules()) {
			// 候选类型集合为{$pmux}，至少两个选中对象；达到阈值立即停止扫描。
			MuxCostContext costs(module);
			if (!costs.type_scan([](const Cell *cell) { return cell->type == ID($pmux); }, 2, "muxtree_share"))
				continue;
			costs.refresh();
			MuxtreeShareWorker worker(module, costs, dry_run, force);
			worker.run();
			candidate_count += worker.candidate_count;
			shared_pairs += worker.shared_pairs;
			predicted_gain += worker.predicted_gain;
		}

		if (dry_run)
			log("Dry run: no module is modified.\n");
		log("%d candidates, %d accepted, predicted ledger gain %lld.\n", candidate_count, shared_pairs, (long long)predicted_gain);
	}
} MuxtreeSharePass;

PRIVATE_NAMESPACE_END
