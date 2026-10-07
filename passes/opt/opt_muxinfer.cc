#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/satgen.h"
#include "passes/opt/muxtree_index.h"
#include "passes/opt/muxledger.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// smaRTLy section II: walk each muxtree from the root, collect the control values implied
// by the path, and prove further control/data bits constant on a small sub-graph with
// inference rules first and SAT second
//
// 每一处改写都先用 MuxLedger 结算收益，账本判定收益为正才施加，-force 时无条件施加；
// SAT 求解的传播步数受 opt_muxinfer.sat_effort 限制，预算耗尽之后不再发起新的求解
struct Cone {
	pool<SigBit> bits;
	pool<Cell *> cells;
};

struct InferWorker
{
	MuxTreeIndex &idx;
	SigMap &sigmap;
	int max_depth, max_cells, max_inputs;
	bool infer_data;
	bool dry_run;        // 只做遍历、推断与记录，不改写模块
	bool force;          // 忽略账本门槛，施加全部改写
	int64_t sat_effort;  // SAT 求解的传播步数预算，0 表示不限
	int64_t sat_spent = 0;
	bool solve_budget_abort = false;  // 本次求解是否达到传播步数上限而放弃
	bool infer_budget_abort = false;  // 本次推断是否因为预算而返回 -1

	dict<SigBit, Cone> cone_cache;

	// (cell, select index) -> constant value, applied after the traversal
	dict<std::pair<Cell *, int>, bool> sel_fix;
	// (cell, data port, offset) -> constant value
	dict<std::tuple<Cell *, IdString, int>, bool> data_fix;
	// 推断因为预算耗尽而放弃的候选：选择位按单元记录，数据位按 (单元, 端口) 记录
	pool<Cell *> sel_budget;
	pool<std::pair<Cell *, IdString>> data_budget;

	int sat_calls = 0, rule_hits = 0, sat_hits = 0;
	int rewrites = 0;       // 已经施加（dry_run 时为账本预测会施加）的改写次数
	int removed_cells = 0;  // 账本预测删除的单元数

	InferWorker(MuxTreeIndex &idx, int max_depth, int max_cells, int max_inputs, bool infer_data,
			bool dry_run, bool force, int64_t sat_effort) :
			idx(idx), sigmap(idx.sigmap), max_depth(max_depth), max_cells(max_cells),
			max_inputs(max_inputs), infer_data(infer_data), dry_run(dry_run), force(force),
			sat_effort(sat_effort) { }

	// 从 bit 向输入方向展开 max_depth 层组合逻辑，得到 bit 的祖先集合
	const Cone &cone(SigBit bit)
	{
		auto it = cone_cache.find(bit);
		if (it != cone_cache.end())
			return it->second;
		Cone c;
		vector<SigBit> frontier = {bit};
		c.bits.insert(bit);
		for (int depth = 0; depth < max_depth && !frontier.empty(); depth++) {
			vector<SigBit> next;
			for (auto b : frontier) {
				auto drv = idx.driver.find(b);
				if (drv == idx.driver.end())
					continue;
				Cell *cell = drv->second;
				if (!idx.comb_ct.cell_known(cell->type) || c.cells.count(cell))
					continue;
				if (GetSize(c.cells) >= max_cells)
					break;
				c.cells.insert(cell);
				for (auto &conn : cell->connections()) {
					if (cell->output(conn.first))
						continue;
					for (auto in : sigmap(conn.second))
						if (in.wire && c.bits.insert(in).second)
							next.push_back(in);
				}
			}
			frontier.swap(next);
		}
		return cone_cache[bit] = c;
	}

	static bool has_undef_input(Cell *cell)
	{
		for (auto &conn : cell->connections())
			if (!cell->output(conn.first))
				for (auto bit : conn.second)
					if (!bit.wire && bit != State::S0 && bit != State::S1)
						return true;
		return false;
	}

	// ---- table I 推理规则，在子图上做常量传播 ----

	dict<SigBit, bool> *val;
	bool conflict, changed;

	int get(SigBit bit)
	{
		if (!bit.wire)
			return bit == State::S0 ? 0 : bit == State::S1 ? 1 : -1;
		auto it = val->find(bit);
		return it == val->end() ? -1 : it->second;
	}

	void set(SigBit bit, bool v)
	{
		if (!bit.wire) {
			if ((bit == State::S0 && v) || (bit == State::S1 && !v))
				conflict = true;
			return;
		}
		auto it = val->find(bit);
		if (it == val->end()) {
			(*val)[bit] = v;
			changed = true;
		} else if (it->second != v)
			conflict = true;
	}

	SigSpec port_ext(Cell *cell, IdString port, int width)
	{
		SigSpec sig = sigmap(cell->getPort(port));
		bool is_signed = false;
		if (cell->hasParam(port == ID::A ? ID::A_SIGNED : ID::B_SIGNED))
			is_signed = cell->getParam(port == ID::A ? ID::A_SIGNED : ID::B_SIGNED).as_bool();
		if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex)))
			is_signed = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
		sig.extend_u0(width, is_signed);
		return sig;
	}

	// y = inv ^ (a[0] | a[1] | ...)
	void or_rule(const SigSpec &a, SigBit y, bool inv)
	{
		int yv = get(y);
		int unknown = 0;
		SigBit last_unknown;
		bool any_one = false;
		for (auto bit : a) {
			int v = get(bit);
			if (v == 1)
				any_one = true;
			else if (v < 0) {
				unknown++;
				last_unknown = bit;
			}
		}
		if (any_one)
			set(y, !inv);
		else if (unknown == 0)
			set(y, inv);
		if (yv >= 0) {
			bool orv = yv ^ inv;
			if (!orv)
				for (auto bit : a)
					set(bit, false);
			else if (!any_one && unknown == 1)
				set(last_unknown, true);
		}
	}

	void zero_upper(Cell *cell)
	{
		SigSpec y = sigmap(cell->getPort(ID::Y));
		for (int i = 1; i < GetSize(y); i++)
			set(y[i], false);
	}

	void propagate_cell(Cell *cell)
	{
		IdString type = cell->type;

		if (type.in(ID($not), ID($_NOT_), ID($pos), ID($buf), ID($_BUF_))) {
			SigSpec y = sigmap(cell->getPort(ID::Y));
			SigSpec a = type.in(ID($not), ID($pos)) ? port_ext(cell, ID::A, GetSize(y)) : sigmap(cell->getPort(ID::A));
			bool inv = type.in(ID($not), ID($_NOT_));
			for (int i = 0; i < GetSize(y); i++) {
				int av = get(a[i]), yv = get(y[i]);
				if (av >= 0)
					set(y[i], av ^ inv);
				if (yv >= 0)
					set(a[i], yv ^ inv);
			}
			return;
		}

		if (type.in(ID($and), ID($or), ID($_AND_), ID($_OR_), ID($_NAND_), ID($_NOR_))) {
			SigSpec y = sigmap(cell->getPort(ID::Y));
			bool fine = type.begins_with("$_");
			SigSpec a = fine ? sigmap(cell->getPort(ID::A)) : port_ext(cell, ID::A, GetSize(y));
			SigSpec b = fine ? sigmap(cell->getPort(ID::B)) : port_ext(cell, ID::B, GetSize(y));
			bool is_and = type.in(ID($and), ID($_AND_), ID($_NAND_));
			bool inv = type.in(ID($_NAND_), ID($_NOR_));
			for (int i = 0; i < GetSize(y); i++) {
				// and 用德摩根转成 or：~y = ~a | ~b
				SigSpec ab = {a[i], b[i]};
				if (!is_and) {
					or_rule(ab, y[i], inv);
					continue;
				}
				int av = get(a[i]), bv = get(b[i]), yv = get(y[i]);
				if (av == 0 || bv == 0)
					set(y[i], inv);
				if (av == 1 && bv == 1)
					set(y[i], !inv);
				if (yv >= 0) {
					bool andv = yv ^ inv;
					if (andv) {
						set(a[i], true);
						set(b[i], true);
					} else if (av == 1)
						set(b[i], false);
					else if (bv == 1)
						set(a[i], false);
				}
			}
			return;
		}

		if (type.in(ID($reduce_or), ID($reduce_bool), ID($logic_not))) {
			SigSpec y = sigmap(cell->getPort(ID::Y));
			or_rule(sigmap(cell->getPort(ID::A)), y[0], type == ID($logic_not));
			zero_upper(cell);
			return;
		}

		if (type == ID($logic_or)) {
			SigSpec y = sigmap(cell->getPort(ID::Y));
			SigSpec ab = sigmap(cell->getPort(ID::A));
			ab.append(sigmap(cell->getPort(ID::B)));
			or_rule(ab, y[0], false);
			zero_upper(cell);
			return;
		}

		if (type == ID($reduce_and)) {
			SigSpec y = sigmap(cell->getPort(ID::Y));
			SigSpec a = sigmap(cell->getPort(ID::A));
			int yv = get(y[0]);
			int unknown = 0;
			SigBit last_unknown;
			bool any_zero = false;
			for (auto bit : a) {
				int v = get(bit);
				if (v == 0)
					any_zero = true;
				else if (v < 0) {
					unknown++;
					last_unknown = bit;
				}
			}
			if (any_zero)
				set(y[0], false);
			else if (unknown == 0)
				set(y[0], true);
			if (yv == 1)
				for (auto bit : a)
					set(bit, true);
			else if (yv == 0 && !any_zero && unknown == 1)
				set(last_unknown, false);
			zero_upper(cell);
			return;
		}

		if (type.in(ID($eq), ID($ne))) {
			int width = std::max(GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::B)));
			SigSpec a = port_ext(cell, ID::A, width);
			SigSpec b = port_ext(cell, ID::B, width);
			SigBit y = sigmap(cell->getPort(ID::Y))[0];
			bool inv = type == ID($ne);
			int yv = get(y);
			int unknown = 0, last = -1;
			bool differ = false;
			for (int i = 0; i < width; i++) {
				int av = get(a[i]), bv = get(b[i]);
				if (av >= 0 && bv >= 0) {
					if (av != bv)
						differ = true;
				} else if (a[i] != b[i]) {
					unknown++;
					last = i;
				}
			}
			if (differ)
				set(y, inv);
			else if (unknown == 0)
				set(y, !inv);
			if (yv >= 0) {
				bool eqv = yv ^ inv;
				for (int i = 0; i < width; i++) {
					int av = get(a[i]), bv = get(b[i]);
					if (eqv && av >= 0)
						set(b[i], av);
					if (eqv && bv >= 0)
						set(a[i], bv);
				}
				if (!eqv && !differ && unknown == 1) {
					int av = get(a[last]), bv = get(b[last]);
					if (av >= 0)
						set(b[last], !av);
					if (bv >= 0)
						set(a[last], !bv);
				}
			}
			zero_upper(cell);
			return;
		}

		if (type.in(ID($xor), ID($xnor), ID($_XOR_), ID($_XNOR_))) {
			SigSpec y = sigmap(cell->getPort(ID::Y));
			bool fine = type.begins_with("$_");
			SigSpec a = fine ? sigmap(cell->getPort(ID::A)) : port_ext(cell, ID::A, GetSize(y));
			SigSpec b = fine ? sigmap(cell->getPort(ID::B)) : port_ext(cell, ID::B, GetSize(y));
			bool inv = type.in(ID($xnor), ID($_XNOR_));
			for (int i = 0; i < GetSize(y); i++) {
				int av = get(a[i]), bv = get(b[i]), yv = get(y[i]);
				if (av >= 0 && bv >= 0)
					set(y[i], av ^ bv ^ inv);
				if (av >= 0 && yv >= 0)
					set(b[i], av ^ yv ^ inv);
				if (bv >= 0 && yv >= 0)
					set(a[i], bv ^ yv ^ inv);
			}
			return;
		}

		if (type.in(ID($mux), ID($_MUX_))) {
			SigSpec a = sigmap(cell->getPort(ID::A));
			SigSpec b = sigmap(cell->getPort(ID::B));
			SigSpec y = sigmap(cell->getPort(ID::Y));
			int sv = get(sigmap(cell->getPort(ID::S))[0]);
			for (int i = 0; i < GetSize(y); i++) {
				int av = get(a[i]), bv = get(b[i]), yv = get(y[i]);
				if (sv >= 0) {
					SigBit d = sv ? b[i] : a[i];
					int dv = sv ? bv : av;
					if (dv >= 0)
						set(y[i], dv);
					if (yv >= 0)
						set(d, yv);
				} else if (av >= 0 && av == bv)
					set(y[i], av);
			}
			return;
		}
	}

	// 返回 -1 表示无法确定；路径矛盾（该路径不可达）时任意取 0
	int propagate(const pool<Cell *> &cells, dict<SigBit, bool> &values, SigBit target)
	{
		val = &values;
		conflict = false;
		for (int iter = 0; iter < 64; iter++) {
			changed = false;
			for (auto cell : cells) {
				propagate_cell(cell);
				if (conflict)
					return 0;
			}
			if (get(target) >= 0)
				return get(target);
			if (!changed)
				break;
		}
		return -1;
	}

	// 预算是否已经用尽
	bool budget_spent()
	{
		return sat_effort > 0 && sat_spent >= sat_effort;
	}

	// 在剩余预算内求解一次。预算已经用尽、或者本次求解达到传播步数上限而放弃时，
	// 把 solve_budget_abort 置位并返回假；达到上限的求解结果不可信，调用者必须放弃整次推断
	bool solve_with_budget(ezSAT *ez, const std::vector<int> &model_exprs, std::vector<bool> &model_values,
			const std::vector<int> &assumptions)
	{
		solve_budget_abort = false;
		if (budget_spent()) {
			solve_budget_abort = true;
			return false;
		}

		if (sat_effort > 0)
			ez->setSolverPropLimit(sat_effort - sat_spent);
		bool result = ez->solve(model_exprs, model_values, assumptions);
		if (sat_effort > 0) {
			sat_spent += ez->getSolverProps();
			if (ez->getSolverPropLimitStatus())
				solve_budget_abort = true;
		}
		return result;
	}

	// 在 known 条件下 target 是否恒为常量
	int infer(SigBit target, const dict<SigBit, bool> &known)
	{
		infer_budget_abort = false;
		target = sigmap(target);
		if (!target.wire)
			return target == State::S0 ? 0 : target == State::S1 ? 1 : -1;
		auto kit = known.find(target);
		if (kit != known.end())
			return kit->second;
		if (known.empty())
			return -1;

		// theorem II.1/II.2：只保留与 target 的祖先集合相交的已知信号，按相交关系扩展成一组
		pool<SigBit> group_bits = cone(target).bits;
		pool<Cell *> cells = cone(target).cells;
		dict<SigBit, bool> values;
		pool<SigBit> used;
		for (bool grown = true; grown;) {
			grown = false;
			for (auto &it : known) {
				if (used.count(it.first))
					continue;
				const Cone &kc = cone(it.first);
				bool touch = false;
				for (auto bit : kc.bits)
					if (group_bits.count(bit)) {
						touch = true;
						break;
					}
				if (!touch)
					continue;
				used.insert(it.first);
				values[it.first] = it.second;
				grown = true;
				for (auto bit : kc.bits)
					group_bits.insert(bit);
				for (auto cell : kc.cells)
					cells.insert(cell);
			}
			if (GetSize(cells) > 4 * max_cells)
				break;
		}
		if (values.empty())
			return -1;

		int res = propagate(cells, values, target);
		if (res >= 0) {
			rule_hits++;
			return res;
		}

		pool<SigBit> driven, inputs;
		for (auto cell : cells)
			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						driven.insert(bit);
		for (auto cell : cells)
			for (auto &conn : cell->connections())
				if (!cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire && !driven.count(bit))
							inputs.insert(bit);
		if (GetSize(inputs) > max_inputs)
			return -1;

		// 预算已经用尽：不再发起新的 SAT 调用，也不构造求解器
		if (budget_spent()) {
			infer_budget_abort = true;
			return -1;
		}

		sat_calls++;
		ezSatPtr ez;
		SatGen satgen(ez.get(), &sigmap);
		// $pmux 在多个选择位同时有效时的取值依赖实现，不导入，输出作为自由变量
		for (auto cell : cells)
			if (cell->type != ID($pmux) && !has_undef_input(cell))
				satgen.importCell(cell);
		vector<int> assumptions;
		for (auto &it : values) {
			int lit = satgen.importSigSpec(it.first)[0];
			assumptions.push_back(it.second ? lit : ez->NOT(lit));
		}
		int t = satgen.importSigSpec(target)[0];
		vector<int> model_exprs;
		vector<bool> model_values;
		assumptions.push_back(t);
		bool can_one = solve_with_budget(ez.get(), model_exprs, model_values, assumptions);
		if (solve_budget_abort) {
			infer_budget_abort = true;
			return -1;
		}
		assumptions.back() = ez->NOT(t);
		bool can_zero = solve_with_budget(ez.get(), model_exprs, model_values, assumptions);
		if (solve_budget_abort) {
			infer_budget_abort = true;
			return -1;
		}
		if (can_one && can_zero)
			return -1;
		sat_hits++;
		return can_one ? 1 : 0;
	}

	void visit_port(Cell *cell, int index, const dict<SigBit, bool> &known)
	{
		pool<SigBit> child_bits;
		auto cit = idx.children.find({cell, index});
		if (cit != idx.children.end())
			for (auto child : cit->second) {
				for (auto bit : sigmap(child->getPort(ID::Y)))
					child_bits.insert(bit);
				visit(child, known);
			}

		if (!infer_data || known.empty())
			return;

		IdString port = index == 0 ? ID::A : ID::B;
		int base = (cell->type == ID($pmux) && index > 0) ? (index - 1) * mux_width(cell) : 0;
		SigSpec sig = mux_port_sig(sigmap, cell, index);
		for (int i = 0; i < GetSize(sig); i++) {
			SigBit bit = sig[i];
			if (!bit.wire || child_bits.count(bit))
				continue;
			int v = infer(bit, known);
			if (v >= 0)
				data_fix[std::make_tuple(cell, port, base + i)] = v;
			else if (infer_budget_abort)
				data_budget.insert({cell, port});
		}
	}

	void visit(Cell *cell, const dict<SigBit, bool> &known)
	{
		if (cell->type == ID($mux)) {
			SigBit s = sigmap(cell->getPort(ID::S)[0]);
			int v = s.wire ? infer(s, known) : -1;
			if (v >= 0) {
				sel_fix[{cell, 0}] = v;
				visit_port(cell, v, known);
				return;
			}
			if (s.wire && infer_budget_abort)
				sel_budget.insert(cell);
			for (int side = 0; side < 2; side++) {
				dict<SigBit, bool> sub = known;
				if (s.wire)
					sub[s] = side;
				visit_port(cell, side, sub);
			}
			return;
		}

		SigSpec s = sigmap(cell->getPort(ID::S));
		int n = GetSize(s);
		vector<int> sv(n);
		int ones = 0, zeros = 0;
		for (int i = 0; i < n; i++) {
			sv[i] = s[i].wire ? infer(s[i], known) : -1;
			if (sv[i] >= 0)
				sel_fix[{cell, i}] = sv[i];
			else if (s[i].wire && infer_budget_abort)
				sel_budget.insert(cell);
			ones += sv[i] == 1;
			zeros += sv[i] == 0;
		}
		for (int i = 0; i < n; i++) {
			if (sv[i] == 0)
				continue;
			dict<SigBit, bool> sub = known;
			if (s[i].wire)
				sub[s[i]] = true;
			visit_port(cell, i + 1, sub);
		}
		if (ones == 0) {
			dict<SigBit, bool> sub = known;
			for (int i = 0; i < n; i++)
				if (s[i].wire)
					sub[s[i]] = false;
			visit_port(cell, 0, sub);
		}
	}

	// 输出一条候选记录：前缀固定，空格分隔 k=v
	void log_candidate(int cand, const char *decision, int64_t gain, int64_t removed, int64_t dead, int64_t added, const char *note)
	{
		log("MUXLEDGER pass=opt_muxinfer module=%s cand=%d decision=%s gain=%lld removed=%lld dead=%lld added=%lld note=%s\n",
				log_id(idx.module), cand, decision, (long long)gain, (long long)removed, (long long)dead,
				(long long)added, note);
	}

	// 整只删除一个 mux 单元：账本记入删除所得并释放输入端口，保留的那一段数据重新占用。
	// 收益至少是 WIDTH，账本不会判定没有收益；dry_run 时只结算与记录
	void apply_drop(Cell *cell, const SigSpec &kept, int cand)
	{
		MuxLedger ledger(idx.module);
		ledger.drop_cell(cell);
		ledger.acquire(kept);
		int64_t dead = ledger.dead_cost();
		int64_t gain = ledger.net_gain();
		int64_t removed = MuxLedger::cell_cost(cell);

		log_candidate(cand, force ? "forced" : "accept", gain, removed, dead, 0, "kept");
		rewrites++;
		removed_cells++;
		if (dry_run)
			return;
		idx.module->connect(cell->getPort(ID::Y), kept);
		idx.module->remove(cell);
	}

	void apply()
	{
		Module *module = idx.module;
		int cand = 0;

		// 数据位改写按 (单元, 端口) 分组：一组一次决策、一次端口写回。
		// 端口值里被换成常量的位释放出去，收益来自因此失去全部使用者的驱动单元
		dict<std::pair<Cell *, IdString>, vector<std::pair<int, bool>>> by_port;
		for (auto &it : data_fix)
			by_port[{std::get<0>(it.first), std::get<1>(it.first)}].push_back({std::get<2>(it.first), it.second});

		for (auto &it : by_port) {
			Cell *cell = it.first.first;
			IdString port = it.first.second;
			cand++;

			SigSpec old_sig = cell->getPort(port);
			SigSpec new_sig = old_sig;
			for (auto &bit : it.second)
				new_sig[bit.first] = bit.second ? State::S1 : State::S0;

			// 端口旧值的信号位释放掉，改写后的端口值重新占用；单元本身代价不变
			MuxLedger ledger(module);
			ledger.drop_port(cell, port);
			ledger.acquire(new_sig);
			int64_t dead = ledger.dead_cost();
			int64_t gain = ledger.net_gain();
			bool enough = gain > 0;

			log_candidate(cand, force ? "forced" : (enough ? "accept" : "reject"), gain, 0, dead, 0,
					enough ? "kept" : "no_gain");
			if (dry_run || !(enough || force))
				continue;
			cell->setPort(port, new_sig);
			rewrites++;
		}

		// 数据位推断因为预算耗尽而没有结论的候选
		for (auto &it : data_budget) {
			if (by_port.count(it))
				continue;
			cand++;
			log_candidate(cand, "reject", 0, 0, 0, 0, "budget");
		}

		dict<Cell *, vector<std::pair<int, bool>>> by_cell;
		for (auto &it : sel_fix)
			by_cell[it.first.first].push_back({it.first.second, it.second});
		// 选择位推断因为预算耗尽而没有结论的单元，候选列表里记为没有可用结论
		for (auto cell : sel_budget)
			if (!by_cell.count(cell))
				by_cell[cell] = vector<std::pair<int, bool>>();

		for (auto &it : by_cell) {
			Cell *cell = it.first;
			vector<std::pair<int, bool>> &fixes = it.second;
			cand++;

			if (fixes.empty()) {
				log_candidate(cand, "reject", 0, 0, 0, 0, "budget");
				continue;
			}

			if (cell->type == ID($mux)) {
				bool select_value = fixes[0].second;
				apply_drop(cell, cell->getPort(select_value ? ID::B : ID::A), cand);
				continue;
			}

			int width = mux_width(cell);
			SigSpec old_select = cell->getPort(ID::S);
			SigSpec old_data = cell->getPort(ID::B);
			dict<int, bool> fixed;
			for (auto &fix : fixes)
				fixed[fix.first] = fix.second;

			int ones = 0, one_index = -1;
			bool all_known = true;
			for (int i = 0; i < GetSize(old_select); i++) {
				if (!fixed.count(i))
					all_known = false;
				else if (fixed[i]) {
					ones++;
					one_index = i;
				}
			}

			// 选择位全已知：没有 1 时整只单元等价于 A，恰好一个 1 时等价于那一段 B
			if (all_known && ones <= 1) {
				SigSpec kept = ones == 0 ? cell->getPort(ID::A) : old_data.extract(one_index * width, width);
				apply_drop(cell, kept, cand);
				continue;
			}

			// 删除恒为 0 的选择位，其余选择位保持原样
			SigSpec new_select, new_data;
			for (int i = 0; i < GetSize(old_select); i++) {
				if (fixed.count(i) && !fixed[i])
					continue;
				new_select.append(old_select[i]);
				new_data.append(old_data.extract(i * width, width));
			}
			// 选择位全部为 0 时等价于整只删除，上面的分支已经覆盖，这里兜底
			if (GetSize(new_select) == 0) {
				apply_drop(cell, cell->getPort(ID::A), cand);
				continue;
			}

			// $pmux 的代价是 WIDTH * (S_WIDTH - 1)，选择位变短省下的部分记入减少所得
			MuxLedger ledger(module);
			ledger.drop_port(cell, ID::S);
			ledger.drop_port(cell, ID::B);
			ledger.acquire(new_select);
			ledger.acquire(new_data);
			ledger.sub_cost((int64_t)width * (GetSize(old_select) - GetSize(new_select)));
			int64_t dead = ledger.dead_cost();
			int64_t gain = ledger.net_gain();
			bool enough = gain > 0;
			// 已知的选择位全部为 1 时长度没有变化，账本判定收益为零
			bool changed = GetSize(new_select) != GetSize(old_select);

			log_candidate(cand, force ? "forced" : (enough ? "accept" : "reject"), gain, 0, dead, 0,
					enough ? "kept" : "no_gain");
			if (dry_run || !(enough || force) || !changed)
				continue;
			cell->setPort(ID::S, new_select);
			cell->setPort(ID::B, new_data);
			cell->setParam(ID::S_WIDTH, GetSize(new_select));
			rewrites++;
		}
	}
};

struct OptMuxInferPass : public Pass {
	OptMuxInferPass() : Pass("opt_muxinfer", "remove muxtree redundancy implied by path conditions") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_muxinfer [options] [selection]\n");
		log("\n");
		log("This pass traverses every $mux/$pmux tree from its root and records the values\n");
		log("of the control signals on the path. A control or data bit whose value follows\n");
		log("from the recorded values is replaced by a constant. The value is derived on a\n");
		log("sub-graph made of the cones of the target bit and of the related known bits,\n");
		log("first by constant propagation rules and then by a SAT solver.\n");
		log("\n");
		log("Every rewrite is priced with a ledger of the signal bits that lose or gain a\n");
		log("user, and is applied only when the predicted gain is positive. Each candidate\n");
		log("is reported on a line starting with \"MUXLEDGER\".\n");
		log("\n");
		log("    -depth <n>\n");
		log("        number of logic levels in the cone of each bit (default 6)\n");
		log("\n");
		log("    -max_cells <n>\n");
		log("        maximum number of cells in the cone of each bit (default 64)\n");
		log("\n");
		log("    -max_inputs <n>\n");
		log("        skip the SAT call when the sub-graph has more inputs (default 64)\n");
		log("\n");
		log("    -nodata\n");
		log("        only infer control bits, keep data bits unchanged\n");
		log("\n");
		log("    -dry-run\n");
		log("        traverse and infer, report every candidate, leave the module unchanged\n");
		log("\n");
		log("    -force\n");
		log("        ignore the ledger threshold and apply every rewrite, reported with\n");
		log("        decision=forced; given together with -dry-run the module stays unchanged\n");
		log("\n");
		log("The solver effort is limited by the number of solver propagation steps held in\n");
		log("the scratchpad key opt_muxinfer.sat_effort (default 1000000000, 0 means\n");
		log("unlimited). Once the budget is used up no further SAT call is made and the\n");
		log("remaining candidates are left unproven.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int max_depth = 6, max_cells = 64, max_inputs = 64;
		bool infer_data = true;
		bool dry_run = false, force = false;
		int64_t sat_effort = design->scratchpad_get_int("opt_muxinfer.sat_effort", 1000000000);

		log_header(design, "Executing OPT_MUXINFER pass (path condition inference on muxtrees).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-depth" && argidx + 1 < args.size()) {
				max_depth = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max_cells" && argidx + 1 < args.size()) {
				max_cells = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max_inputs" && argidx + 1 < args.size()) {
				max_inputs = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-nodata") {
				infer_data = false;
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

		// 同时给出 -dry-run 与 -force 时按 -dry-run 处理
		if (dry_run)
			force = false;

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			MuxTreeIndex idx(module);
			InferWorker worker(idx, max_depth, max_cells, max_inputs, infer_data, dry_run, force, sat_effort);
			for (auto root : idx.roots)
				worker.visit(root, dict<SigBit, bool>());
			worker.apply();

			std::string effort;
			if (sat_effort > 0)
				effort = stringf("sat effort %lld of %lld left", (long long)std::max<int64_t>(sat_effort - worker.sat_spent, 0),
						(long long)sat_effort);
			else
				effort = "sat effort unlimited";
			log("  %s: %d rewrites, ledger predicted %d removed cells, %d rule hits, %d sat hits, %d sat calls, %s.\n",
					log_id(module), worker.rewrites, worker.removed_cells,
					worker.rule_hits, worker.sat_hits, worker.sat_calls, effort.c_str());
		}
	}
} OptMuxInferPass;

PRIVATE_NAMESPACE_END
