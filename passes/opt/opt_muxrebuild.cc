#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/muxtree_index.h"
#include "passes/opt/muxledger.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// smaRTLy section III: a muxtree whose control ports are eq/logic_not/reduce_or of a few
// signal bits is a function from those bits to the leaf data words. Build its ADD with the
// heuristic "split on the bit that minimizes the terminal kinds of both children" and
// replace the tree when the shared mux ledger reports a positive gain.
static const int TERM_CONFLICT = -2;

struct TreeNode {
	Cell *cell;
	// 每个数据端口：子节点下标或者叶子编号，子节点用 ~index 表示
	vector<int> ports;
};

struct AddNode {
	int var;
	int lo, hi;
};

struct RebuildWorker
{
	MuxTreeIndex &idx;
	SigMap &sigmap;
	Module *module;
	int max_vars;
	bool dry_run;
	bool force;

	// 当前树
	vector<TreeNode> nodes;
	vector<SigSpec> terms;
	dict<SigSpec, int> term_ids;
	pool<Cell *> tree_cells;

	// 控制逻辑
	vector<SigBit> vars;
	dict<SigBit, int> var_ids;
	pool<Cell *> ctrl_cells;
	bool ctrl_ok;
	bool collect_ok = true;
	int64_t table_budget = 1000000;
	MuxWorkspace workspace;
	MuxWorkspace *candidate_workspace = nullptr;

	// ADD，叶子编号 t 的节点为 {-1, t, t}
	vector<AddNode> add;
	dict<std::tuple<int, int, int>, int> add_cache;
	dict<std::pair<vector<int>, vector<int>>, int> build_cache;

	int rebuilt = 0;
	// 已输出的候选记录序号，从 1 开始，按模块内记录的先后递增
	int cand = 0;

	RebuildWorker(MuxTreeIndex &idx, int max_vars, bool dry_run, bool force) :
			idx(idx), sigmap(idx.sigmap), module(idx.module), max_vars(max_vars),
			dry_run(dry_run), force(force), workspace(idx.costs.resources) { }

	int term_id(const SigSpec &sig)
	{
		auto it = term_ids.find(sig);
		if (it != term_ids.end())
			return it->second;
		terms.push_back(sig);
		return term_ids[sig] = GetSize(terms) - 1;
	}

	int collect(Cell *cell, int depth = 0)
	{
		if (depth > 256 || GetSize(nodes) >= 4096 || !idx.costs.resources.charge(32) ||
			!candidate_workspace->reserve(256 + GetSize(cell->getPort(ID::Y)) * 32)) {
			collect_ok = false;
			return 0;
		}
		int id = GetSize(nodes);
		nodes.push_back({cell, {}});
		tree_cells.insert(cell);
		int n = mux_port_count(cell);
		vector<int> ports;
		for (int i = 0; i < n; i++) {
			SigSpec sig = mux_port_sig(sigmap, cell, i);
			auto cit = idx.children.find({cell, i});
			if (cit != idx.children.end() && GetSize(cit->second) == 1 &&
					sigmap(cit->second[0]->getPort(ID::Y)) == sig)
				ports.push_back(~collect(cit->second[0], depth + 1));
			else
				ports.push_back(term_id(sig));
		}
		nodes[id].ports = ports;
		return id;
	}

	// 控制位由 eq/ne/logic_not/reduce_or/reduce_bool/not 组成的表达式计算，表达式的叶子是变量
	void classify(SigBit bit, int depth = 0)
	{
		if ((!bit.wire && bit != State::S0 && bit != State::S1) || depth > 256 || GetSize(ctrl_cells) > 4096 ||
			!idx.costs.resources.charge(8)) {
			ctrl_ok = false;
			return;
		}
		if (!bit.wire || var_ids.count(bit))
			return;
		auto drv = idx.driver.find(bit);
		Cell *cell = drv == idx.driver.end() ? nullptr : drv->second;
		if (cell != nullptr && !tree_cells.count(cell) &&
				idx.costs.mutable_cell(cell) &&
				cell->type.in(ID($eq), ID($ne), ID($logic_not), ID($reduce_or), ID($reduce_bool), ID($not))) {
			if (ctrl_cells.insert(cell).second) {
				for (auto in : sigmap(cell->getPort(ID::A)))
					classify(in, depth + 1);
				if (cell->hasPort(ID::B))
					for (auto in : sigmap(cell->getPort(ID::B)))
						classify(in, depth + 1);
			}
			return;
		}
		var_ids[bit] = GetSize(vars);
		vars.push_back(bit);
		if (GetSize(vars) > max_vars)
			ctrl_ok = false;
	}

	// 在变量赋值 mask 下计算一位控制信号
	dict<SigBit, bool> memo;

	bool eval_bit(SigBit bit, int mask)
	{
		idx.costs.resources.charge(1);
		if (!bit.wire)
			return bit == State::S1;
		auto vit = var_ids.find(bit);
		if (vit != var_ids.end())
			return (mask >> vit->second) & 1;
		auto mit = memo.find(bit);
		if (mit != memo.end())
			return mit->second;

		Cell *cell = idx.driver.at(bit);
		SigSpec y = sigmap(cell->getPort(ID::Y));
		int offset = 0;
		while (y[offset] != bit)
			offset++;
		bool res = false;
		if (cell->type == ID($not)) {
			SigSpec a = sigmap(cell->getPort(ID::A));
			a.extend_u0(GetSize(y), cell->getParam(ID::A_SIGNED).as_bool());
			res = !eval_bit(a[offset], mask);
		} else if (offset > 0) {
			res = false;
		} else if (cell->type.in(ID($eq), ID($ne))) {
			SigSpec a = sigmap(cell->getPort(ID::A));
			SigSpec b = sigmap(cell->getPort(ID::B));
			int width = std::max(GetSize(a), GetSize(b));
			bool is_signed = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
			a.extend_u0(width, is_signed);
			b.extend_u0(width, is_signed);
			bool eq = true;
			for (int i = 0; i < width && eq; i++)
				eq = eval_bit(a[i], mask) == eval_bit(b[i], mask);
			res = cell->type == ID($eq) ? eq : !eq;
		} else {
			bool any = false;
			for (auto in : sigmap(cell->getPort(ID::A)))
				if (eval_bit(in, mask)) {
					any = true;
					break;
				}
			res = cell->type == ID($logic_not) ? !any : any;
		}
		memo[bit] = res;
		return res;
	}

	// 树在赋值 mask 下选中的叶子
	int eval_tree(int node, int mask)
	{
		const TreeNode &tn = nodes[node];
		auto leaf_of = [&](int i) {
			// 端口是叶子编号（>=0）或子节点下标取反（<=-2）
			int p = tn.ports[i];
			return p >= 0 ? p : eval_tree(~p, mask);
		};
		Cell *cell = tn.cell;
		if (cell->type == ID($mux)) {
			bool s = eval_bit(sigmap(cell->getPort(ID::S)[0]), mask);
			return leaf_of(s ? 1 : 0);
		}
		SigSpec s = sigmap(cell->getPort(ID::S));
		int result = 0;
		bool any = false;
		for (int i = 0; i < GetSize(s); i++) {
			if (!eval_bit(s[i], mask))
				continue;
			int v = leaf_of(i + 1);
			if (v == TERM_CONFLICT)
				return TERM_CONFLICT;
			if (!any) {
				result = v;
				any = true;
			} else if (v != result)
				return TERM_CONFLICT;
		}
		return any ? result : leaf_of(0);
	}

	int make_node(int var, int lo, int hi)
	{
		if (lo == hi)
			return lo;
		auto key = std::make_tuple(var, lo, hi);
		auto it = add_cache.find(key);
		if (it != add_cache.end())
			return it->second;
		if (!workspace.reserve(256))
			return lo;
		add.push_back({var, lo, hi});
		return add_cache[key] = GetSize(add) - 1;
	}

	dict<int, int> leaf_nodes;

	int leaf_node(int term)
	{
		auto it = leaf_nodes.find(term);
		if (it != leaf_nodes.end())
			return it->second;
		if (!workspace.reserve(128))
			return -1;
		add.push_back({-1, term, term});
		return leaf_nodes[term] = GetSize(add) - 1;
	}

	static int kinds(const vector<int> &table)
	{
		pool<int> seen;
		for (int t : table)
			seen.insert(t);
		return GetSize(seen);
	}

	// table 的第 k 位对应 vlist 中的第 k 个变量；返回 ADD 节点，-1 表示全部无关
	int build(const vector<int> &table, const vector<int> &vlist)
	{
		if (!idx.costs.resources.charge(GetSize(table) * (GetSize(vlist) + 1)) ||
			!candidate_workspace->reserve(128 + (GetSize(table) + GetSize(vlist)) * 16))
			return -1;
		pool<int> seen;
		for (int t : table)
			seen.insert(t);
		if (seen.empty())
			return -1;
		if (GetSize(seen) == 1)
			return leaf_node(*seen.begin());

		auto key = std::make_pair(table, vlist);
		auto it = build_cache.find(key);
		if (it != build_cache.end())
			return it->second;

		int best = -1, best_cost = 0;
		vector<int> best_lo, best_hi;
		for (int k = 0; k < GetSize(vlist); k++) {
			vector<int> lo, hi;
			for (int m = 0; m < GetSize(table); m++) {
				int rest = (m & ((1 << k) - 1)) | ((m >> (k + 1)) << k);
				if (rest >= GetSize(lo)) {
					lo.resize(rest + 1);
					hi.resize(rest + 1);
				}
				((m >> k) & 1 ? hi : lo)[rest] = table[m];
			}
			int lo_kinds = kinds(lo), hi_kinds = kinds(hi);
			// 某一侧的叶子种类数小于 2 时，build() 为这一侧返回叶子，它不会再新增节点
			int cost = (lo_kinds < 2 ? 0 : lo_kinds) + (hi_kinds < 2 ? 0 : hi_kinds);
			if (best < 0 || cost < best_cost) {
				best = k;
				best_cost = cost;
				best_lo = lo;
				best_hi = hi;
			}
		}

		vector<int> sub_vlist = vlist;
		sub_vlist.erase(sub_vlist.begin() + best);
		int lo = build(best_lo, sub_vlist);
		int hi = build(best_hi, sub_vlist);
		int res = lo < 0 ? hi : hi < 0 ? lo : make_node(vlist[best], lo, hi);
		return build_cache[key] = res;
	}

	// 输出一条候选记录：前缀固定，空格分隔 k=v
	void log_candidate(int cand, const char *decision, int64_t gain, int64_t removed, int64_t dead, int64_t added, const char *note)
	{
		log("MUXLEDGER pass=opt_muxrebuild module=%s cand=%d decision=%s gain=%lld removed=%lld dead=%lld added=%lld note=%s\n",
				log_id(module), cand, decision, (long long)gain, (long long)removed, (long long)dead,
				(long long)added, note);
	}

	SigSpec emit(int n, dict<int, SigSpec> &emitted)
	{
		auto it = emitted.find(n);
		if (it != emitted.end())
			return it->second;
		SigSpec res;
		if (add[n].var < 0)
			res = terms[add[n].lo];
		else {
			SigSpec lo = emit(add[n].lo, emitted);
			SigSpec hi = emit(add[n].hi, emitted);
			res = module->Mux(NEW_ID, lo, hi, vars[add[n].var]);
		}
		return emitted[n] = res;
	}

	struct Plan {
		Cell *root;
		int add_root;
		vector<Cell *> cells;
		vector<SigBit> vars;
		vector<SigSpec> terms;
	};
	vector<Plan> plans;

	struct Cost {
		bool feasible;
		int64_t removed, dead, added, gain;
		int64_t update_work;
	};

	// 提交判据，与 analyze() 的判定链同义：不可行拒绝，-force 放行，否则要求正收益
	// 且比较器全部保留时新增的 LUT4 成本不超过删除所得的一半。analyze() 与 apply() 共用。
	bool accepts(const Cost &cost, bool force) const
	{
		if (!cost.feasible)
			return false;
		return force || (cost.gain > 0 && !(cost.dead == 0 && 2 * cost.added > cost.removed));
	}

	Cost price(Cell *root, int add_root, const vector<Cell *> &removed)
	{
		MuxLedger ledger(idx.costs);
		ledger.alias_commit = true;
		for (Cell *cell : removed)
			ledger.drop_cell(cell);
		using Word = Lut4Functions::Word;
		dict<int, Word> memo;
		std::function<Word(int)> build_cost = [&](int n) -> Word {
			auto found = memo.find(n);
			if (found != memo.end())
				return found->second;
			const AddNode &node = add[n];
			if (node.var < 0)
				return memo[n] = idx.costs.word(terms[node.lo]);
			Word lo = build_cost(node.lo), hi = build_cost(node.hi), outputs;
			for (int child : {node.lo, node.hi})
				if (add[child].var < 0)
					ledger.acquire(terms[add[child].lo]);
			ledger.acquire(vars[node.var]);
			auto select = idx.costs.word(vars[node.var]).at(0);
			for (int i = 0; i < GetSize(lo); i++)
				outputs.push_back(idx.costs.functions.mux(lo[i], hi[i], select));
			idx.costs.functions.boundary(outputs);
			return memo[n] = outputs;
		};
		ledger.add_outputs(root->getPort(ID::Y), build_cost(add_root));
		if (add[add_root].var < 0)
			ledger.acquire(terms[add[add_root].lo]);
		bool feasible = ledger.settle();
		return {feasible, ledger.removed_gain, ledger.dead_result, ledger.added_cost, ledger.gain, idx.costs.resources.commit_reserved};
	}

	void analyze(Cell *root)
	{
		if (idx.costs.resources.exhausted || !idx.costs.mutable_cell(root))
			return;
		MuxWorkspace scratch(idx.costs.resources);
		candidate_workspace = &scratch;
		nodes.clear();
		terms.clear();
		term_ids.clear();
		tree_cells.clear();
		vars.clear();
		var_ids.clear();
		ctrl_cells.clear();
		ctrl_ok = true;
		collect_ok = true;
		// 叶子编号只在一棵树内有效
		leaf_nodes.clear();
		build_cache.clear();

		collect(root);
		if (!collect_ok) {
			log_candidate(++cand, "infeasible", 0, 0, 0, 0, "budget");
			return;
		}
		if (GetSize(nodes) < 2 && mux_port_count(root) < 3)
			return;

		for (auto &tn : nodes)
			for (auto bit : sigmap(tn.cell->getPort(ID::S)))
				classify(bit);
		// 控制位与树单元无关的树不在本 Pass 的处理范围内，变量数超限只在有控制单元时才算候选
		if (ctrl_cells.empty() || vars.empty())
			return;
		if (!ctrl_ok) {
			cand++;
			log_candidate(cand, "infeasible", 0, 0, 0, 0, "too_wide");
			return;
		}

		int nv = GetSize(vars);
		if (nv > 20 || (int64_t(1) << nv) > table_budget ||
			!scratch.reserve((int64_t(1) << nv) * 16) ||
			!idx.costs.resources.charge((int64_t(1) << nv) * GetSize(nodes))) {
			log_candidate(++cand, "infeasible", 0, 0, 0, 0, "budget");
			return;
		}
		table_budget -= int64_t(1) << nv;
		vector<int> table(1 << nv);
		for (int mask = 0; mask < (1 << nv); mask++) {
			memo.clear();
			table[mask] = eval_tree(0, mask);
			if (table[mask] == TERM_CONFLICT) {
				cand++;
				log_candidate(cand, "infeasible", 0, 0, 0, 0, "conflict");
				return;
			}
		}

		vector<int> vlist;
		for (int i = 0; i < nv; i++)
			vlist.push_back(i);
		int add_root = build(table, vlist);
		if (add_root < 0 || idx.costs.resources.exhausted)
			return;

		vector<Cell *> removed;
		for (auto &tn : nodes)
			removed.push_back(tn.cell);
		Cost cost = price(root, add_root, removed);
		int64_t removed_mux = cost.removed, added_mux = cost.added, removed_ctrl = cost.dead, gain = cost.gain;

		log_debug("  root %s: %d vars, removed %lld, dead %lld, added %lld, gain %lld\n",
				log_id(root), nv, (long long)removed_mux, (long long)removed_ctrl,
				(long long)added_mux, (long long)gain);

		bool rebuild = accepts(cost, force);
		const char *decision, *note;
		if (!cost.feasible) {
			decision = "infeasible";
			note = "unsupported";
		} else if (force) {
			// -force 忽略门槛，可以评估的候选全部施加
			decision = "forced";
			note = "kept";
		} else if (gain <= 0) {
			decision = "reject";
			note = "no_gain";
		} else if (removed_ctrl == 0 && 2 * added_mux > removed_mux) {
			// 比较器全部保留时，新图的新增 LUT4 成本限制为删除所得的一半。
			decision = "reject";
			note = "half_rule";
		} else {
			decision = "accept";
			note = "kept";
		}
		cand++;
		log_candidate(cand, decision, gain, removed_mux, removed_ctrl, added_mux, note);
		if (!rebuild)
			return;

		Plan plan;
		if (!workspace.reserve(256 + GetSize(nodes) * 32 + GetSize(vars) * 32 + GetSize(terms) * 128))
			return;
		plan.root = root;
		plan.add_root = add_root;
		plan.cells = std::move(removed);
		plan.vars = vars;
		plan.terms = terms;
		plans.push_back(plan);
		log("  accepted %s: %d mux cells, %d vars, ledger gain %lld\n",
				log_id(root), GetSize(nodes), nv, (long long)gain);
	}

	void apply()
	{
		if (dry_run)
			return;
		for (Plan &plan : plans) {
			vars = plan.vars;
			terms = plan.terms;
			Cost cost = price(plan.root, plan.add_root, plan.cells);
			if (!accepts(cost, force))
				continue;
			log_assert(idx.costs.resources.reserve_commit(cost.update_work));
			dict<int, SigSpec> emitted;
			SigSpec y = plan.root->getPort(ID::Y);
			SigSpec res = emit(plan.add_root, emitted);
			for (auto cell : plan.cells)
				module->remove(cell);
			module->connect(y, res);
			idx.costs.refresh();
			idx.costs.resources.commit_reserved = 0;
			rebuilt++;
		}
	}
};

struct OptMuxRebuildPass : public Pass {
	OptMuxRebuildPass() : Pass("opt_muxrebuild", "rebuild muxtrees controlled by comparators") { }
	void help() override
	{
		log("\n");
		log("    opt_muxrebuild [options] [selection]\n");
		log("\n");
		log("This pass collects every $mux/$pmux tree whose control bits are computed from a\n");
		log("few signal bits by $eq/$ne/$logic_not/$reduce_or/$reduce_bool/$not cells. The\n");
		log("tree is evaluated for every assignment of those bits and the resulting function\n");
		log("is rebuilt as an algebraic decision diagram of $mux cells. At every node the bit\n");
		log("that minimizes the number of distinct leaves of both children is selected.\n");
		log("\n");
		log("Every candidate is settled with the shared mux ledger. The tree cells, the data\n");
		log("words and the control bits of the new diagram and the new $mux cells are booked\n");
		log("with one cost model, and the comparators that lose all their users follow from\n");
		log("the dead propagation of the ledger. The tree is replaced when the ledger gain is\n");
		log("positive. When no comparator is removed, newly needed LUT4 functions must cost\n");
		log("at most half the removed functions. Each candidate is reported starting with\n");
		log("\"MUXLEDGER\".\n");
		log("\n");
		log("    -max_vars <n>\n");
		log("        maximum number of control variables of a tree (default 10)\n");
		log("\n");
		log("    -dry-run\n");
		log("        analyze every candidate and print its ledger record without modifying the\n");
		log("        design\n");
		log("\n");
		log("    -force\n");
		log("        ignore the gain threshold and the half rule and rebuild every candidate\n");
		log("        that can be evaluated; those records use decision=forced. A candidate\n");
		log("        with too many control variables or with conflicting leaf values stays\n");
		log("        infeasible. Given together with -dry-run, the pass behaves as with\n");
		log("        -dry-run alone.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int max_vars = 10;
		bool dry_run = false, force = false;

		log_header(design, "Executing OPT_MUXREBUILD pass (rebuild muxtrees as decision diagrams).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_vars" && argidx + 1 < args.size()) {
				max_vars = atoi(args[++argidx].c_str());
				if (max_vars < 1)
					log_error("Invalid -max_vars value \"%s\": need at least one control variable.\n", args[argidx].c_str());
				// 真值表有 2^n 项，n 超过 30 时 1 << n 在 int 中溢出
				if (max_vars > 30)
					log_error("Invalid -max_vars value \"%s\": 1 << n overflows an int.\n", args[argidx].c_str());
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

		// 两个选项同时给出时按 -dry-run 处理，-force 不参与判断
		if (dry_run)
			force = false;

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			MuxTreeIndex idx(module);
			if (!idx.costs.type_scan([](const Cell *cell) { return cell->type.in(ID($mux), ID($pmux)); }, 1, "muxrebuild"))
				continue;
			idx.costs.refresh();
			idx.rebuild();
			RebuildWorker worker(idx, max_vars, dry_run, force);
			for (auto root : idx.roots)
				worker.analyze(root);
			worker.apply();
			if (dry_run)
				log("  %s: dry run, %d muxtrees would be rebuilt.\n", log_id(module), GetSize(worker.plans));
			else
				log("  %s: rebuilt %d muxtrees.\n", log_id(module), worker.rebuilt);
		}
	}
} OptMuxRebuildPass;

PRIVATE_NAMESPACE_END
