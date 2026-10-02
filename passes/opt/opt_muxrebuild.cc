#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "passes/opt/muxtree_index.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// smaRTLy section III: a muxtree whose control ports are eq/logic_not/reduce_or of a few
// signal bits is a function from those bits to the leaf data words. Build its ADD with the
// heuristic "split on the bit that minimizes the terminal kinds of both children" and
// replace the tree when the ADD needs fewer mux bits than the tree and its comparators.
static const int TERM_DC = -1;
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

	// ADD，叶子编号 t 的节点为 {-1, t, t}
	vector<AddNode> add;
	dict<std::tuple<int, int, int>, int> add_cache;
	dict<std::pair<vector<int>, vector<int>>, int> build_cache;

	int rebuilt = 0;

	RebuildWorker(MuxTreeIndex &idx, int max_vars) :
			idx(idx), sigmap(idx.sigmap), module(idx.module), max_vars(max_vars) { }

	int term_id(const SigSpec &sig)
	{
		if (sig.is_fully_undef())
			return TERM_DC;
		auto it = term_ids.find(sig);
		if (it != term_ids.end())
			return it->second;
		terms.push_back(sig);
		return term_ids[sig] = GetSize(terms) - 1;
	}

	int collect(Cell *cell)
	{
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
				ports.push_back(~collect(cit->second[0]));
			else
				ports.push_back(term_id(sig));
		}
		nodes[id].ports = ports;
		return id;
	}

	// 控制位由 eq/ne/logic_not/reduce_or/reduce_bool/not 组成的表达式计算，表达式的叶子是变量
	void classify(SigBit bit)
	{
		if (!bit.wire || var_ids.count(bit))
			return;
		auto drv = idx.driver.find(bit);
		Cell *cell = drv == idx.driver.end() ? nullptr : drv->second;
		if (cell != nullptr && !tree_cells.count(cell) &&
				cell->type.in(ID($eq), ID($ne), ID($logic_not), ID($reduce_or), ID($reduce_bool), ID($not))) {
			if (ctrl_cells.insert(cell).second) {
				for (auto in : sigmap(cell->getPort(ID::A)))
					classify(in);
				if (cell->hasPort(ID::B))
					for (auto in : sigmap(cell->getPort(ID::B)))
						classify(in);
			}
			return;
		}
		if (!var_ids.count(bit)) {
			var_ids[bit] = GetSize(vars);
			vars.push_back(bit);
			if (GetSize(vars) > max_vars)
				ctrl_ok = false;
		}
	}

	// 在变量赋值 mask 下计算一位控制信号
	dict<SigBit, bool> memo;

	bool eval_bit(SigBit bit, int mask)
	{
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
			int p = tn.ports[i];
			return p >= 0 || p == TERM_DC ? p : eval_tree(~p, mask);
		};
		Cell *cell = tn.cell;
		if (cell->type == ID($mux)) {
			bool s = eval_bit(sigmap(cell->getPort(ID::S)[0]), mask);
			return leaf_of(s ? 1 : 0);
		}
		SigSpec s = sigmap(cell->getPort(ID::S));
		int result = TERM_DC;
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
		add.push_back({var, lo, hi});
		return add_cache[key] = GetSize(add) - 1;
	}

	dict<int, int> leaf_nodes;

	int leaf_node(int term)
	{
		auto it = leaf_nodes.find(term);
		if (it != leaf_nodes.end())
			return it->second;
		add.push_back({-1, term, term});
		return leaf_nodes[term] = GetSize(add) - 1;
	}

	static int kinds(const vector<int> &table)
	{
		pool<int> seen;
		for (int t : table)
			if (t != TERM_DC)
				seen.insert(t);
		return GetSize(seen);
	}

	// table 的第 k 位对应 vlist 中的第 k 个变量；返回 ADD 节点，-1 表示全部无关
	int build(const vector<int> &table, const vector<int> &vlist)
	{
		pool<int> seen;
		for (int t : table)
			if (t != TERM_DC)
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
			int cost = kinds(lo) + kinds(hi);
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

	int count_muxes(int root)
	{
		pool<int> seen;
		vector<int> todo = {root};
		int count = 0;
		while (!todo.empty()) {
			int n = todo.back();
			todo.pop_back();
			if (!seen.insert(n).second || add[n].var < 0)
				continue;
			count++;
			todo.push_back(add[n].lo);
			todo.push_back(add[n].hi);
		}
		return count;
	}

	// 只被树和其他可删除控制单元使用的控制单元会在重建后失去全部使用者
	int removable_ctrl_cost()
	{
		pool<Cell *> removable = ctrl_cells;
		for (bool changed = true; changed;) {
			changed = false;
			for (auto cell : ctrl_cells) {
				if (!removable.count(cell))
					continue;
				bool ok = true;
				for (auto bit : sigmap(cell->getPort(ID::Y))) {
					if (idx.port_bits.count(bit))
						ok = false;
					auto uit = idx.users.find(bit);
					if (uit != idx.users.end())
						for (auto user : uit->second)
							if (!tree_cells.count(user) && !removable.count(user))
								ok = false;
				}
				if (!ok) {
					removable.erase(cell);
					changed = true;
				}
			}
		}
		int cost = 0;
		for (auto cell : removable) {
			int width = 0;
			for (auto bit : sigmap(cell->getPort(ID::A)))
				width += bit.wire != nullptr;
			if (cell->hasPort(ID::B))
				for (auto bit : sigmap(cell->getPort(ID::B)))
					width += bit.wire != nullptr;
			cost += std::max(width - 1, 0);
		}
		return cost;
	}

	SigSpec emit(int n, int width, dict<int, SigSpec> &emitted)
	{
		auto it = emitted.find(n);
		if (it != emitted.end())
			return it->second;
		SigSpec res;
		if (add[n].var < 0)
			res = terms[add[n].lo];
		else {
			SigSpec lo = emit(add[n].lo, width, emitted);
			SigSpec hi = emit(add[n].hi, width, emitted);
			res = module->Mux(NEW_ID, lo, hi, vars[add[n].var]);
		}
		return emitted[n] = res;
	}

	struct Plan {
		Cell *root;
		int add_root;
		vector<Cell *> cells;
	};
	vector<Plan> plans;

	void analyze(Cell *root)
	{
		nodes.clear();
		terms.clear();
		term_ids.clear();
		tree_cells.clear();
		vars.clear();
		var_ids.clear();
		ctrl_cells.clear();
		ctrl_ok = true;
		// 叶子编号只在一棵树内有效
		leaf_nodes.clear();
		build_cache.clear();

		collect(root);
		if (GetSize(nodes) < 2 && (root->type == ID($mux) || mux_port_count(root) < 3))
			return;

		for (auto &tn : nodes) {
			for (auto bit : sigmap(tn.cell->getPort(ID::S)))
				classify(bit);
			if (!ctrl_ok)
				return;
		}
		if (ctrl_cells.empty() || vars.empty())
			return;

		int nv = GetSize(vars);
		vector<int> table(1 << nv);
		for (int mask = 0; mask < (1 << nv); mask++) {
			memo.clear();
			table[mask] = eval_tree(0, mask);
			if (table[mask] == TERM_CONFLICT)
				return;
		}

		vector<int> vlist;
		for (int i = 0; i < nv; i++)
			vlist.push_back(i);
		int add_root = build(table, vlist);
		if (add_root < 0)
			return;

		int width = mux_width(root);
		int removed_cost = removable_ctrl_cost();
		int old_mux_cost = 0;
		for (auto &tn : nodes)
			old_mux_cost += 3 * width * (mux_port_count(tn.cell) - 1);
		int old_cost = old_mux_cost + removed_cost;
		int new_cost = 3 * width * count_muxes(add_root);

		log_debug("  root %s: %d vars, old cost %d, new cost %d\n", log_id(root), nv, old_cost, new_cost);
		if (new_cost >= old_cost)
			return;
		// 论文的 Check：比较器全部保留时，mux 位数至少减半才值得改变树的结构
		if (removed_cost == 0 && 2 * new_cost > old_mux_cost)
			return;

		Plan plan;
		plan.root = root;
		plan.add_root = add_root;
		for (auto &tn : nodes)
			plan.cells.push_back(tn.cell);
		plans.push_back(plan);
		plan_vars.push_back(vars);
		plan_terms.push_back(terms);
		log("  rebuilding %s: %d mux cells, %d vars, cost %d -> %d\n",
				log_id(root), GetSize(nodes), nv, old_cost, new_cost);
	}

	vector<vector<SigBit>> plan_vars;
	vector<vector<SigSpec>> plan_terms;

	void apply()
	{
		for (int i = 0; i < GetSize(plans); i++) {
			Plan &plan = plans[i];
			vars = plan_vars[i];
			terms = plan_terms[i];
			dict<int, SigSpec> emitted;
			SigSpec y = plan.root->getPort(ID::Y);
			SigSpec res = emit(plan.add_root, GetSize(y), emitted);
			for (auto cell : plan.cells)
				module->remove(cell);
			module->connect(y, res);
			rebuilt++;
		}
	}
};

struct OptMuxRebuildPass : public Pass {
	OptMuxRebuildPass() : Pass("opt_muxrebuild", "rebuild muxtrees controlled by comparators") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_muxrebuild [options] [selection]\n");
		log("\n");
		log("This pass collects every $mux/$pmux tree whose control bits are computed from a\n");
		log("few signal bits by $eq/$ne/$logic_not/$reduce_or/$reduce_bool/$not cells. The\n");
		log("tree is evaluated for every assignment of those bits and the resulting function\n");
		log("is rebuilt as an algebraic decision diagram of $mux cells. At every node the bit\n");
		log("that minimizes the number of distinct leaves of both children is selected. The\n");
		log("tree is replaced when the new mux bits cost less than the old mux bits together\n");
		log("with the comparators that lose all their users. When no comparator is removed,\n");
		log("the new mux bits must be at most half of the old mux bits.\n");
		log("\n");
		log("    -max_vars <n>\n");
		log("        maximum number of control variables of a tree (default 10)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int max_vars = 10;

		log_header(design, "Executing OPT_MUXREBUILD pass (rebuild muxtrees as decision diagrams).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_vars" && argidx + 1 < args.size()) {
				max_vars = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			MuxTreeIndex idx(module);
			RebuildWorker worker(idx, max_vars);
			for (auto root : idx.roots)
				worker.analyze(root);
			worker.apply();
			log("  %s: rebuilt %d muxtrees.\n", log_id(module), worker.rebuilt);
		}
	}
} OptMuxRebuildPass;

PRIVATE_NAMESPACE_END
