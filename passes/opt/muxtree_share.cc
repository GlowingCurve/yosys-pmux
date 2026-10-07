#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/muxledger.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// a hash-consed DAG of word-level 2:1 muxes, id -1 is an all-x word
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
	int mux_count = 0;

	int leaf(const SigSpec &sig)
	{
		if (sig.is_fully_undef())
			return -1;
		auto it = leaf_cache.find(sig);
		if (it != leaf_cache.end())
			return it->second;
		nodes.push_back(Node());
		nodes.back().leaf = sig;
		return leaf_cache[sig] = GetSize(nodes) - 1;
	}

	// sel ? hi : lo, an all-x side is a don't care
	int mux(SigBit sel, int lo, int hi)
	{
		if (lo == hi || hi == -1)
			return lo;
		if (lo == -1)
			return hi;
		auto key = std::make_tuple(sel, lo, hi);
		auto it = mux_cache.find(key);
		if (it != mux_cache.end())
			return it->second;
		nodes.push_back(Node());
		nodes.back().sel = sel;
		nodes.back().lo = lo;
		nodes.back().hi = hi;
		mux_count++;
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
	vector<SigSpec> emit(Module *module, int width)
	{
		vector<SigSpec> sig(GetSize(nodes));
		auto get = [&](int id) { return id == -1 ? SigSpec(State::Sx, width) : sig[id]; };
		for (int id = 0; id < GetSize(nodes); id++) {
			const Node &n = nodes[id];
			if (n.lo == -1 && n.hi == -1) {
				sig[id] = n.leaf;
				continue;
			}
			sig[id] = module->addWire(NEW_ID, width);
			module->addMux(NEW_ID, get(n.lo), get(n.hi), n.sel, sig[id]);
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
	SigMap sigmap;
	dict<SigBit, Cell*> driver;
	bool dry_run;                 // 只做匹配与账本结算，不改动模块
	bool force;                   // 取消 gain 大于零的门槛，全部候选都参与配对
	int shared_pairs = 0;         // 被选中并施加的候选个数
	int candidate_count = 0;      // 枚举出的候选个数
	int64_t predicted_gain = 0;   // 选中候选的账本收益之和

	// 一个 (p, q, j) 候选的结算记录，最后逐行输出
	struct Candidate {
		int p, q, j;
		int64_t gain;      // 账本收益：删除所得 + 连带死亡所得 - 共享树代价
		int64_t removed;   // 删除所得，两个 $pmux 的代价之和
		int64_t dead;      // 连带死亡所得，失去全部使用者的单元代价之和
		int64_t added;     // 共享树的代价，按字级 mux 个数折算
		const char *decision = "reject";
		const char *note = "no_gain";
	};

	MuxtreeShareWorker(Module *module, bool dry_run, bool force) : module(module), dry_run(dry_run), force(force)
	{
		dict<std::pair<SigSpec, int>, vector<PmuxTable>> groups;
		update_index();
		for (auto cell : module->selected_cells()) {
			PmuxTable t;
			if (cell->type == ID($pmux) && decode(cell, t))
				groups[std::make_pair(t.base, cell->getParam(ID::WIDTH).as_int())].push_back(t);
		}

		for (auto &it : groups)
			if (GetSize(it.second) >= 2)
				share_group(it.second);
	}

	void update_index()
	{
		sigmap.set(module);
		driver.clear();
		for (auto cell : module->cells())
		for (auto &conn : cell->connections())
			if (cell->output(conn.first))
				for (auto bit : sigmap(conn.second))
					driver[bit] = cell;
	}
	// decompose a select bit into "base == value", value == -1 if the compare is never true
	bool match_select(SigBit s, SigSpec &base, int &value)
	{
		auto it = driver.find(sigmap(s));
		if (it == driver.end())
			return false;

		Cell *cmp = it->second;
		if (!cmp->type.in(ID($eq), ID($logic_not)) || sigmap(cmp->getPort(ID::Y)[0]) != sigmap(s))
			return false;

		SigSpec a = sigmap(cmp->getPort(ID::A));
		SigSpec b;
		if (cmp->type == ID($logic_not)) {
			b = Const(0, GetSize(a));
		} else if (cmp->type == ID($eq)) {
			b = sigmap(cmp->getPort(ID::B));
			if (a.is_fully_const())
				std::swap(a, b);
			if (!b.is_fully_def())
				return false;
			bool is_signed = cmp->getParam(ID::A_SIGNED).as_bool() && cmp->getParam(ID::B_SIGNED).as_bool();
			if (is_signed && GetSize(a) != GetSize(b))
				return false;
		} else
			return false;

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

		// values not matched by any select bit take A, two bits with the same value would be active at once
		t.cell = cell;
		t.data.assign(1 << GetSize(t.base), sig_a);
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
			SigBit bit = queue.back();
			queue.pop_back();
			if (target.count(bit))
				return true;
			if (visited.count(bit))
				continue;
			visited.insert(bit);

			auto it = driver.find(bit);
			if (it == driver.end() || RTLIL::builtin_ff_cell_types().count(it->second->type))
				continue;
			for (auto &conn : it->second->connections())
				if (it->second->input(conn.first))
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

	// 枚举同一组内的全部 (p, q, j) 候选，用账本结算每个候选的收益，再按收益降序贪心配对。
	// 账本把拆除两个 $pmux 的所得、驱动它们选择端的 $eq/$logic_not 失去全部使用者之后的
	// 所得、以及共享树新增的代价放在一起比较，其中死亡比较器这一笔正是字级 mux 计数漏掉的。
	void share_group(const vector<PmuxTable> &tables)
	{
		int n = GetSize(tables[0].base);

		vector<Candidate> rows;
		for (int p = 0; p < GetSize(tables); p++)
		for (int q = p + 1; q < GetSize(tables); q++) {
			// 一对 (p, q) 新建一个账本：计划删除两个 $pmux，共享树接管两者的全部数据字与 base。
			// 账本自己不建 sigmap，acquire 进来的是解码时已经做过 sigmap 的 tables，删除与释放
			// 走的是单元端口上的原始信号位，与 muxledger.h 的约定一致。
			MuxLedger ledger(module);
			ledger.drop_cell(tables[p].cell);
			ledger.drop_cell(tables[q].cell);
			for (auto &sig : tables[p].data)
				ledger.acquire(sig);
			for (auto &sig : tables[q].data)
				ledger.acquire(sig);
			ledger.acquire(tables[p].base);

			// base_gain 与 j 无关：共享树在所有的 j 下读的都是同一批叶子，也就是两个 $pmux
			// 全部数据字的并集，选择端用的还是同一个 base，acquire 记下的使用者集合因此与 j
			// 无关，dead_cost() 传播出来的死亡单元与 j 无关；removed 也只跟两个 $pmux 有关。
			// acquire 只影响使用者计数，不产生代价，所以此处 net_gain() 等于删除所得加连带
			// 死亡所得；唯一随 j 变化的是共享树新增的 mux 个数，它在下面按 j 逐个扣除。
			int64_t base_gain = ledger.net_gain();

			int width = tables[p].cell->getParam(ID::WIDTH).as_int();
			for (int j = 0; j < n; j++) {
				MuxDag dag;
				share(dag, tables[p], tables[q], j);

				Candidate c;
				c.p = p;
				c.q = q;
				c.j = j;
				c.removed = ledger.removed_gain;
				c.dead = ledger.dead_cost();
				c.added = (int64_t)dag.mux_count * width;
				c.gain = base_gain - c.added;
				rows.push_back(c);
			}
		}

		// 进入贪心配对的是 gain 大于零的候选，-force 时门槛取消、全部候选都参与。
		// 按 gain 降序排序，gain 相同时按 (p, q, j) 升序，配对结果与枚举顺序无关。
		vector<int> order;
		for (int i = 0; i < GetSize(rows); i++)
			if (force || rows[i].gain > 0)
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

			used.insert(c.p);
			used.insert(c.q);
			c.decision = force ? "forced" : "accept";
			c.note = "kept";
			if (!dry_run) {
				apply(tables[c.p], tables[c.q], c.j);
				update_index();
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
		vector<SigSpec> sig = dag.emit(module, width);

		SigSpec p_y = p.cell->getPort(ID::Y);
		SigSpec q_y = q.cell->getPort(ID::Y);
		module->remove(p.cell);
		module->remove(q.cell);
		module->connect(p_y, roots.first == -1 ? SigSpec(State::Sx, width) : sig[roots.first]);
		module->connect(q_y, roots.second == -1 ? SigSpec(State::Sx, width) : sig[roots.second]);
	}
};

struct MuxtreeSharePass : public Pass {
	MuxtreeSharePass() : Pass("muxtree_share", "share the select trees of $pmux pairs that differ in one select bit") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
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
			MuxtreeShareWorker worker(module, dry_run, force);
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
