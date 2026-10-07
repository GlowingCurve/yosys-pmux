#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"
#include "passes/opt/muxledger.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Mishchenko et al., "Control Logic Restructuring for Area Optimization" (ABC &reshape)
// 寄存器 D 端的 $mux/$pmux 锥写成 F(C, X) = x0&f0(C) | x1&f1(C) | ...：
// 枚举控制变量 C 的全部取值，得到每个取值下被选中的数据源；
// Q 反馈对应的 f_Q 取反后驱动 CE，其余数据源用最小位宽编码，编码位由整个字共享的控制函数产生，
// 每个数据位只剩一棵 k:1 MUX，CE 关闭的取值作为无关项参与控制函数化简

enum TV : int8_t { T0 = 0, T1 = 1, TD = 2 };

// 控制函数：support 是叶子下标，table 按 support 顺序索引（support[0] 为最低位）
struct Func {
	std::vector<int> support;
	std::vector<bool> table;
};

// 锥中的一个 $mux/$pmux；单元指针记在 ReshapeWorker::cone_cells 里
struct Node {
	// 数据槽：>=0 为子节点下标，-1 为全 x，<=-2 为数据源 -2-slot
	std::vector<int> slots;
	// 选择位：>=0 为 ctrl 下标，-1 为常量 0，-2 为常量 1
	std::vector<int> sel;
};

struct Plan {
	Cell *ff;
	SigSpec leaves;
	std::vector<SigSpec> data;
	int nbits;
	std::vector<Func> sel_funcs;
	bool has_en;
	Func en_func;
	// 新增逻辑的估计代价，结算时用账本的 add_cost 记入
	int64_t cost;
};

static const int R_DC = -1, R_FAIL = -2;

// 预测 emit_lut 将会发射的 $lut 的代价，整个过程不创建任何单元。
// 分支与 emit_lut 一一对应：输入位数为空时返回常量，输入位数为 1 且真值表是恒等映射时直接返回该输入，
// 这两种情况都不发射单元，代价为零；其余情况发射 WIDTH 等于输入位数的 $lut，按账本的 $lut 折算规则计价。
static int64_t predict_lut_cost(const SigSpec &inputs, const std::vector<bool> &table)
{
	if (inputs.empty())
		return 0;
	if (GetSize(inputs) == 1 && !table[0] && table[1])
		return 0;
	return (int64_t)1 << std::max(GetSize(inputs) - 4, 0);
}

struct ReshapeWorker
{
	Module *module;
	ConstEval ce;
	SigMap &sigmap;
	FfInitVals initvals;
	int max_leaves, max_cells;
	bool force;

	// 拒绝原因计数：cone_fail 与 no_gain 按寄存器计，too_wide 与 infeasible 按候选方案计
	int count_cone_fail = 0;    // D 端无法展开成锥的寄存器数
	int count_too_wide = 0;     // 控制量超过 -max_leaves 而放弃的候选方案数
	int count_infeasible = 0;   // 制表冲突或 make_plan 给不出方案的候选方案数
	int count_no_gain = 0;      // 账本判定收益不大于零而拒绝的寄存器数

	dict<SigBit, Cell *> mux_driver;
	dict<SigBit, int> fanout;
	pool<Cell *> claimed;

	std::vector<Node> nodes;
	std::vector<Cell *> cone_cells;   // 当前寄存器锥内的单元，add_node 依次记录
	std::vector<SigBit> ctrl;
	dict<SigBit, int> ctrl_idx;
	std::vector<SigSpec> sources;
	dict<SigSpec, int> source_idx;

	std::vector<Plan> plans;
	dict<std::pair<SigSpec, Const>, SigBit> func_cache;

	ReshapeWorker(Module *module, int max_leaves, int max_cells, bool force) :
			module(module), ce(module), sigmap(ce.assign_map), max_leaves(max_leaves), max_cells(max_cells),
			force(force)
	{
		initvals.set(&sigmap, module);
		for (auto cell : module->cells()) {
			if (cell->type.in(ID($mux), ID($pmux)))
				for (auto bit : sigmap(cell->getPort(ID::Y)))
					mux_driver[bit] = cell;
			for (auto &conn : cell->connections())
				if (!cell->known() || cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							fanout[bit]++;
		}
		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					fanout[bit]++;
	}

	// 每个寄存器一行账本记录，字段固定、空格分隔
	void log_record(int cand, const char *decision, int64_t gain, int64_t removed, int64_t dead, int64_t added, const char *note)
	{
		log("MUXLEDGER pass=opt_reshape module=%s cand=%d decision=%s gain=%lld removed=%lld dead=%lld added=%lld note=%s\n",
				log_id(module), cand, decision, (long long)gain, (long long)removed, (long long)dead,
				(long long)added, note);
	}

	// 模块级汇总：四类放弃原因的计数与已经定下的计划数
	void log_summary()
	{
		log("MUXLEDGER pass=opt_reshape module=%s cone_fail=%d too_wide=%d infeasible=%d no_gain=%d planned=%d\n",
				log_id(module), count_cone_fail, count_too_wide, count_infeasible, count_no_gain, GetSize(plans));
	}

	int source_slot(const SigSpec &sig)
	{
		if (sig.is_fully_undef())
			return -1;
		auto it = source_idx.find(sig);
		if (it != source_idx.end())
			return -2 - it->second;
		int id = GetSize(sources);
		sources.push_back(sig);
		source_idx[sig] = id;
		return -2 - id;
	}

	int ctrl_slot(SigBit bit)
	{
		if (bit == State::S0)
			return -1;
		if (bit == State::S1)
			return -2;
		if (!bit.wire)
			return -3;
		auto it = ctrl_idx.find(bit);
		if (it != ctrl_idx.end())
			return it->second;
		int id = GetSize(ctrl);
		ctrl.push_back(bit);
		ctrl_idx[bit] = id;
		return id;
	}

	// 扇出为 1 且宽度一致的 $mux/$pmux 并入锥，其余信号作为数据源
	int add_slot(const SigSpec &sig)
	{
		Cell *drv = nullptr;
		for (auto bit : sig) {
			auto it = mux_driver.find(bit);
			Cell *c = it == mux_driver.end() ? nullptr : it->second;
			if (c == nullptr || fanout[bit] != 1 || (drv != nullptr && c != drv)) {
				drv = nullptr;
				break;
			}
			drv = c;
		}
		if (drv == nullptr || claimed.count(drv) || GetSize(nodes) >= max_cells ||
				sigmap(drv->getPort(ID::Y)) != sig)
			return source_slot(sig);
		return add_node(drv);
	}

	int add_node(Cell *cell)
	{
		claimed.insert(cell);
		int id = GetSize(nodes);
		nodes.push_back(Node());
		cone_cells.push_back(cell);

		SigSpec sig_a = sigmap(cell->getPort(ID::A));
		SigSpec sig_b = sigmap(cell->getPort(ID::B));
		SigSpec sig_s = sigmap(cell->getPort(ID::S));
		int width = GetSize(sig_a);

		std::vector<int> sel, slots;
		for (auto bit : sig_s)
			sel.push_back(ctrl_slot(bit));
		slots.push_back(add_slot(sig_a));
		for (int i = 0; i < GetSize(sig_s); i++)
			slots.push_back(add_slot(sig_b.extract(i * width, width)));
		nodes[id].sel = sel;
		nodes[id].slots = slots;
		return id;
	}

	int resolve(int slot, const std::vector<bool> &cval)
	{
		if (slot >= 0)
			return eval_node(slot, cval);
		if (slot == -1)
			return R_DC;
		return -2 - slot;
	}

	// 给定控制位取值，返回被选中的数据源；$pmux 多个选择位同时有效时要求各分支一致
	int eval_node(int id, const std::vector<bool> &cval)
	{
		const Node &node = nodes[id];
		int result = R_DC;
		int hot = 0;
		for (int i = 0; i < GetSize(node.sel); i++) {
			int s = node.sel[i];
			if (s == -3)
				return R_FAIL;
			bool v = s == -1 ? false : s == -2 ? true : bool(cval[s]);
			if (!v)
				continue;
			int r = resolve(node.slots[i + 1], cval);
			if (r == R_FAIL || (hot > 0 && r != result))
				return R_FAIL;
			result = r;
			hot++;
		}
		if (hot == 0)
			return resolve(node.slots[0], cval);
		return result;
	}

	bool driven_by(SigBit bit, const pool<Cell *> &cells)
	{
		pool<Cell *> drivers;
		ce.sig2driver.find(bit, drivers);
		for (auto c : drivers)
			if (cells.count(c))
				return true;
		return false;
	}

	// 控制位沿组合逻辑向输入方向展开，叶子数不超过 max_leaves；
	// 例如 $eq(state, k) 展开到 state，互斥的 $pmux 选择位不再被当作独立变量。
	// 已展开单元的输出位不能再成为叶子，否则 ConstEval 计算该单元时会覆盖叶子的取值
	pool<SigBit> expand(pool<SigBit> front)
	{
		pool<Cell *> tried, expanded;
		bool changed = true;
		while (changed) {
			changed = false;
			std::vector<SigBit> bits(front.begin(), front.end());
			for (auto bit : bits) {
				if (!front.count(bit))
					continue;
				pool<Cell *> drivers;
				ce.sig2driver.find(bit, drivers);
				if (GetSize(drivers) != 1)
					continue;
				Cell *cell = *drivers.begin();
				if (tried.count(cell) || claimed.count(cell))
					continue;
				tried.insert(cell);
				pool<SigBit> next = front;
				for (auto &conn : cell->connections())
					if (cell->output(conn.first))
						for (auto b : sigmap(conn.second))
							next.erase(b);
				for (auto &conn : cell->connections())
					if (cell->input(conn.first))
						for (auto b : sigmap(conn.second))
							if (b.wire && !driven_by(b, expanded))
								next.insert(b);
				if (GetSize(next) <= max_leaves) {
					front = next;
					expanded.insert(cell);
					changed = true;
				}
			}
		}
		return front;
	}

	// 枚举叶子的全部取值，返回每个取值下被选中的数据源；失败时返回空
	std::vector<int> tabulate(const SigSpec &leaves, int root)
	{
		int n = GetSize(leaves);
		std::vector<int> table(1 << n);
		std::vector<bool> cval(GetSize(ctrl));
		for (int p = 0; p < (1 << n); p++) {
			ce.push();
			ce.set(leaves, Const(p, n));
			for (int i = 0; i < GetSize(ctrl); i++) {
				SigSpec sig = ctrl[i];
				if (!ce.eval(sig) || !sig.is_fully_def()) {
					ce.pop();
					return {};
				}
				cval[i] = sig.as_bool();
			}
			ce.pop();
			table[p] = eval_node(root, cval);
			if (table[p] == R_FAIL)
				return {};
		}
		return table;
	}

	// 去掉 removed 中的变量后，无关项之外是否仍然没有冲突
	static bool consistent(const std::vector<TV> &table, int n, int removed)
	{
		dict<int, TV> seen;
		for (int p = 0; p < (1 << n); p++) {
			if (table[p] == TD)
				continue;
			auto it = seen.find(p & ~removed);
			if (it == seen.end())
				seen[p & ~removed] = table[p];
			else if (it->second != table[p])
				return false;
		}
		return true;
	}

	// 贪心删除变量得到极小 support，无关项填 0
	static Func minimize(const std::vector<TV> &table, int n)
	{
		int removed = 0;
		for (int v = n - 1; v >= 0; v--)
			if (consistent(table, n, removed | (1 << v)))
				removed |= 1 << v;
		Func f;
		for (int v = 0; v < n; v++)
			if (!(removed & (1 << v)))
				f.support.push_back(v);
		int m = GetSize(f.support);
		f.table.assign(1 << m, false);
		for (int p = 0; p < (1 << n); p++) {
			if (table[p] != T1)
				continue;
			int q = 0;
			for (int i = 0; i < m; i++)
				if (p & (1 << f.support[i]))
					q |= 1 << i;
			f.table[q] = true;
		}
		return f;
	}

	// 位宽 nbits 的 MUX 树中，码 c 在第 b 位是否经过一个 MUX（码 >= k 的子树被剪掉）
	static bool sel_needed(int c, int b, int k)
	{
		int base = (c >> (b + 1)) << (b + 1);
		return base + (1 << b) < k;
	}

	// 控制函数的输入信号：support 决定取哪些叶子位，emit_lut 与代价预测共用
	SigSpec func_inputs(const SigSpec &leaves, const Func &f)
	{
		SigSpec inputs;
		for (auto v : f.support)
			inputs.append(leaves[v]);
		return inputs;
	}

	// table[p] 为取值 p 下的数据源；q_src 为 Q 反馈的数据源下标（没有则为 -1）
	bool make_plan(Plan &plan, const SigSpec &leaves, const std::vector<int> &table, int q_src, const FfData &ff)
	{
		int width = ff.width;
		int n = GetSize(leaves);
		std::vector<int> data;
		for (auto r : table)
			if (r >= 0 && r != q_src && std::find(data.begin(), data.end(), r) == data.end())
				data.push_back(r);
		if (data.empty())
			return false;
		std::sort(data.begin(), data.end());

		plan.leaves = leaves;
		plan.has_en = std::find(table.begin(), table.end(), q_src) != table.end() && q_src >= 0;
		int64_t cost = 0;
		if (plan.has_en) {
			std::vector<TV> en(1 << n);
			for (int p = 0; p < (1 << n); p++)
				en[p] = table[p] == R_DC ? TD : table[p] == q_src ? T0 : T1;
			plan.en_func = minimize(en, n);
			cost += predict_lut_cost(func_inputs(leaves, plan.en_func), plan.en_func.table);
			// 已有 CE 时，apply() 还会发射一个把原 CE 与 en 相与的 $lut，表下标为 {en, 原 CE}。
			// en 在计划阶段还没有信号位，这里用两位常量占位；两位输入的代价与具体信号无关。
			if (ff.has_ce) {
				SigSpec and_inputs(State::S0, 2);
				std::vector<bool> and_table = {false, false, !ff.pol_ce, ff.pol_ce};
				cost += predict_lut_cost(and_inputs, and_table);
			}
		}

		int k = GetSize(data);
		int nbits = 0;
		while ((1 << nbits) < k)
			nbits++;
		plan.nbits = nbits;

		// 数据源到码的分配：k 较小时枚举全部排列，取控制函数总代价最小者
		std::vector<int> best_order;
		std::vector<Func> best_funcs;
		int64_t best_cost = INT64_MAX;
		std::vector<int> order = data;
		do {
			dict<int, int> code;
			for (int c = 0; c < k; c++)
				code[order[c]] = c;
			std::vector<Func> funcs;
			int64_t cost_bits = 0;
			for (int b = 0; b < nbits; b++) {
				std::vector<TV> sel(1 << n);
				for (int p = 0; p < (1 << n); p++) {
					int r = table[p];
					if (r < 0 || r == q_src || !sel_needed(code[r], b, k))
						sel[p] = TD;
					else
						sel[p] = (code[r] >> b) & 1 ? T1 : T0;
				}
				funcs.push_back(minimize(sel, n));
				cost_bits += predict_lut_cost(func_inputs(leaves, funcs.back()), funcs.back().table);
			}
			if (cost_bits < best_cost) {
				best_cost = cost_bits;
				best_order = order;
				best_funcs = funcs;
			}
		} while (k <= 5 && std::next_permutation(order.begin(), order.end()));

		plan.data.clear();
		for (auto r : best_order)
			plan.data.push_back(sources[r]);
		plan.sel_funcs = best_funcs;
		// k 选 1 的 mux 树恰好由 k-1 个 $mux 单元组成，每个单元的代价是 WIDTH
		cost += best_cost + (int64_t)(k - 1) * width;
		plan.cost = cost;
		return true;
	}

	void analyze(Cell *cell)
	{
		FfData ff(&initvals, cell);
		if (!ff.has_clk || ff.has_gclk || ff.has_aload || ff.has_sr || ff.has_srst || ff.is_fine)
			return;
		SigSpec sig_d = sigmap(ff.sig_d);
		SigSpec sig_q = sigmap(ff.sig_q);

		nodes.clear();
		cone_cells.clear();
		ctrl.clear();
		ctrl_idx.clear();
		sources.clear();
		source_idx.clear();

		int root = add_slot(sig_d);
		if (root < 0) {
			// 锥构造失败：D 端的驱动不能并入锥
			count_cone_fail++;
			log_record(-1, "infeasible", 0, 0, 0, 0, "infeasible");
			return;
		}
		int q_src = source_idx.count(sig_q) ? source_idx.at(sig_q) : -1;

		// 候选叶子集合：原始控制位，以及沿组合逻辑向输入方向展开之后的控制位
		std::vector<SigSpec> options;
		if (GetSize(ctrl) <= max_leaves)
			options.push_back(SigSpec(ctrl));
		else
			count_too_wide++;
		pool<SigBit> ctrl_leaves(ctrl.begin(), ctrl.end());
		pool<SigBit> deep = expand(ctrl_leaves);
		if (deep != ctrl_leaves) {
			if (GetSize(deep) <= max_leaves) {
				std::vector<SigBit> deep_bits(deep.begin(), deep.end());
				std::sort(deep_bits.begin(), deep_bits.end());
				options.push_back(SigSpec(deep_bits));
			} else {
				count_too_wide++;
			}
		}

		Plan best;
		bool have_best = false;
		int64_t best_gain = 0, best_removed = 0, best_dead = 0, best_added = 0;
		int best_cand = -1;
		int first_infeasible = -1;
		int cand = 0;
		for (auto &leaves : options) {
			std::vector<int> table = tabulate(leaves, root);
			if (table.empty()) {
				// 枚举叶子取值时控制位无法求值，或者 $pmux 同时有效的分支给出不同数据源
				count_infeasible++;
				if (first_infeasible < 0)
					first_infeasible = cand;
				cand++;
				continue;
			}
			Plan plan;
			plan.ff = cell;
			if (!make_plan(plan, leaves, table, q_src, ff)) {
				// 控制函数的关闭取值之外没有剩下任何数据源
				count_infeasible++;
				if (first_infeasible < 0)
					first_infeasible = cand;
				cand++;
				continue;
			}

			// 每个候选方案各用一个新建的账本：叶子集合不同，释放之后又被占用的信号位就不同。
			// 用原始控制位作叶子时比较器仍然被占用；用展开后的叶子时比较器失去使用者，
			// 它的代价由 dead_cost 给出，这是本 Pass 最大的收益来源。
			MuxLedger ledger(module);
			int64_t removed = 0;
			for (auto cone_cell : cone_cells) {
				ledger.drop_cell(cone_cell);
				removed += MuxLedger::cell_cost(cone_cell);
			}
			ledger.acquire(leaves);
			for (auto &source : plan.data)
				ledger.acquire(source);
			// 寄存器本身会被重建，Q 仍然由它驱动；不占用 Q 的话，Q 的使用者只剩下
			// 被删除的锥内单元时，这个寄存器会被当成失去全部使用者而虚增收益。
			ledger.acquire(sig_q);
			ledger.add_cost(plan.cost);
			int64_t dead = ledger.dead_cost();
			int64_t gain = ledger.net_gain();

			if (!have_best || gain > best_gain) {
				have_best = true;
				best = plan;
				best_gain = gain;
				best_removed = removed;
				best_dead = dead;
				best_added = plan.cost;
				best_cand = cand;
			}
			cand++;
		}

		if (!have_best) {
			// 没有可用方案：控制量超过 max_leaves，或者全部候选方案都不可行
			if (first_infeasible >= 0)
				log_record(first_infeasible, "infeasible", 0, 0, 0, 0, "infeasible");
			else
				log_record(-1, "reject", 0, 0, 0, 0, "too_wide");
			return;
		}

		if (!force && best_gain <= 0) {
			count_no_gain++;
			log_record(best_cand, "reject", best_gain, best_removed, best_dead, best_added, "no_gain");
			return;
		}

		log_debug("  %s: %d sources over %d leaves, added %lld, gain %lld (removed %lld, dead %lld)\n",
				log_id(cell), GetSize(best.data), GetSize(best.leaves), (long long)best_added,
				(long long)best_gain, (long long)best_removed, (long long)best_dead);
		log_record(best_cand, force ? "forced" : "accept", best_gain, best_removed, best_dead, best_added, "kept");
		plans.push_back(best);
	}

	// 相同 support 与真值表的控制函数在整个模块内只生成一次
	SigBit emit_lut(const SigSpec &inputs, const std::vector<bool> &table)
	{
		if (inputs.empty())
			return table[0] ? State::S1 : State::S0;
		if (GetSize(inputs) == 1 && !table[0] && table[1])
			return inputs[0];
		Const lut(std::vector<State>(table.size(), State::S0));
		for (int i = 0; i < GetSize(table); i++)
			if (table[i])
				lut.set(i, State::S1);
		auto key = std::make_pair(inputs, lut);
		auto it = func_cache.find(key);
		if (it != func_cache.end())
			return it->second;
		Wire *w = module->addWire(NEW_ID);
		module->addLut(NEW_ID, inputs, w, lut);
		func_cache[key] = w;
		return w;
	}

	SigBit emit_func(const Plan &plan, const Func &f)
	{
		return emit_lut(func_inputs(plan.leaves, f), f.table);
	}

	SigSpec build_mux(const std::vector<SigSpec> &data, const SigSpec &sel, int lo, int b)
	{
		if (b < 0)
			return data[lo];
		int mid = lo + (1 << b);
		if (mid >= GetSize(data))
			return build_mux(data, sel, lo, b - 1);
		SigSpec y = module->addWire(NEW_ID, GetSize(data[0]));
		module->addMux(NEW_ID, build_mux(data, sel, lo, b - 1), build_mux(data, sel, mid, b - 1), sel[b], y);
		return y;
	}

	void apply(const Plan &plan)
	{
		FfData ff(&initvals, plan.ff);
		SigSpec sel;
		for (auto &f : plan.sel_funcs)
			sel.append(emit_func(plan, f));
		ff.sig_d = build_mux(plan.data, sel, 0, plan.nbits - 1);
		if (plan.has_en) {
			SigBit en = emit_func(plan, plan.en_func);
			if (ff.has_ce) {
				// 新 CE = 原 CE 有效 & en；查找表下标 = {en, 原 CE}
				std::vector<bool> table = {false, false, !ff.pol_ce, ff.pol_ce};
				SigSpec inputs = ff.sig_ce[0];
				inputs.append(en);
				en = emit_lut(inputs, table);
			}
			ff.has_ce = true;
			ff.pol_ce = true;
			ff.sig_ce = en;
		}
		ff.emit();
	}
};

struct OptReshapePass : public Pass {
	OptReshapePass() : Pass("opt_reshape", "restructure register next-state control logic") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_reshape [options] [selection]\n");
		log("\n");
		log("Restructure the $mux/$pmux cone driving the D input of each word-level register\n");
		log("(Mishchenko et al., \"Control Logic Restructuring for Area Optimization\").\n");
		log("The control variables of the cone are enumerated to find the data source selected\n");
		log("under each assignment. The feedback from Q becomes a clock enable, the remaining\n");
		log("sources are binary encoded, and the encoding bits are produced by control\n");
		log("functions shared by all data bits, using the disabled assignments as don't-cares.\n");
		log("Each data bit is left with a single k:1 multiplexer.\n");
		log("\n");
		log("The decision for each register is made with the shared mux ledger: the $mux/$pmux\n");
		log("cells of the cone are released, a comparator absorbed by the expansion of the\n");
		log("control variables counts towards the gain as well, and the restructuring is kept\n");
		log("only when the ledger reports a positive gain.\n");
		log("\n");
		log("    -max_leaves <n>\n");
		log("        maximum number of control variables enumerated per register (default 10,\n");
		log("        allowed range 1 to 20)\n");
		log("\n");
		log("    -max_cells <n>\n");
		log("        maximum number of $mux/$pmux cells in one cone (default 64)\n");
		log("\n");
		log("    -dry-run\n");
		log("        analyze the registers and print the ledger records without modifying the\n");
		log("        module\n");
		log("\n");
		log("    -force\n");
		log("        ignore the ledger threshold and apply every plan, the records are written\n");
		log("        with decision=forced. Given together with -dry-run, -force is ignored and\n");
		log("        the records show what the ledger would decide.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int max_leaves = 10, max_cells = 64;
		bool dry_run = false, force = false;

		log_header(design, "Executing OPT_RESHAPE pass (register control logic restructuring).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_leaves" && argidx + 1 < args.size()) {
				max_leaves = std::stoi(args[++argidx]);
				if (max_leaves < 1 || max_leaves > 20)
					log_error("Invalid -max_leaves value %d: expected a value between 1 and 20.\n", max_leaves);
				continue;
			}
			if (args[argidx] == "-max_cells" && argidx + 1 < args.size()) {
				max_cells = std::stoi(args[++argidx]);
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

		// 两个选项同时给出时按 -dry-run 处理：门槛也不取消，记录行反映账本原本的决定
		if (dry_run)
			force = false;

		int total = 0;
		for (auto module : design->selected_modules()) {
			ReshapeWorker worker(module, max_leaves, max_cells, force);
			for (auto cell : module->selected_cells())
				if (StaticCellTypes::categories.is_ff(cell->type))
					worker.analyze(cell);
			if (!dry_run)
				for (auto &plan : worker.plans)
					worker.apply(plan);
			worker.log_summary();
			total += GetSize(worker.plans);
		}
		if (dry_run)
			log("Planned %d registers (dry run, modules unchanged).\n", total);
		else
			log("Restructured %d registers.\n", total);
	}
} OptReshapePass;

PRIVATE_NAMESPACE_END
