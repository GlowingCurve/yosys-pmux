#include "kernel/cellaigs.h"
#include "kernel/ff.h"
#include "kernel/ffinit.h"
#include "kernel/log.h"
#include "kernel/modtools.h"
#include "kernel/qcsat.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CrNode {
	SigBit leaf;
	int lhs = -1, rhs = -1;
};

struct CrDriver {
	Cell *cell;
	IdString port;
	int offset;
};

struct CrCellAig {
	Aig aig;
	vector<int> imported;
	dict<pair<IdString, int>, int> outputs;
	int any_select = -1;

	// 构建单元 AIG，并建立输出节点索引和导入缓存。
	CrCellAig(Cell *cell) : aig(cell), imported(GetSize(aig.nodes), -1)
	{
		for (int i = 0; i < GetSize(aig.nodes); i++)
			for (auto port : aig.nodes[i].outports)
				outputs[port] = i;
	}
};

// literal 的高位保存节点编号，最低位表示反相；0 和 1 表示常量。
struct CrAig {
	SigMap &sigmap;
	dict<SigBit, CrDriver> drivers;
	dict<SigBit, int> leaf_nodes, signal_cache;
	dict<pair<int, int>, int> and_nodes;
	std::map<Cell *, CrCellAig> cell_aigs;
	pool<SigBit> active, cyclic_signals;
	vector<CrNode> nodes;

	// 建立信号驱动索引，并保留常量节点。
	CrAig(Module *module, SigMap &sigmap) : sigmap(sigmap)
	{
		nodes.push_back(CrNode());
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->output(conn.first)) {
					SigSpec output = sigmap(conn.second);
					for (int i = GetSize(output) - 1; i >= 0; i--)
						drivers[output[i]] = {cell, conn.first, i};
				}
	}

	// 翻转 AIG literal 的极性。
	int inv(int value) const { return value ^ 1; }

	// 复用或创建信号对应的 AIG 叶节点。
	int leaf(SigBit bit)
	{
		bit = sigmap(bit);
		if (bit == State::S0)
			return 0;
		if (bit == State::S1)
			return 1;
		auto entry = leaf_nodes.emplace(bit, GetSize(nodes));
		if (entry.second) {
			CrNode node;
			node.leaf = bit;
			nodes.push_back(node);
		}
		return entry.first->second << 1;
	}

	// 化简 AND 表达式并复用结构相同的节点。
	int land(int lhs, int rhs)
	{
		if (lhs == 0 || rhs == 0)
			return 0;
		if (lhs == 1)
			return rhs;
		if (rhs == 1)
			return lhs;
		if (lhs == rhs)
			return lhs;
		if (lhs == inv(rhs))
			return 0;
		if (lhs > rhs)
			std::swap(lhs, rhs);
		pair<int, int> key(lhs, rhs);
		auto entry = and_nodes.emplace(key, GetSize(nodes));
		if (entry.second) {
			CrNode node;
			node.lhs = lhs;
			node.rhs = rhs;
			nodes.push_back(node);
		}
		return entry.first->second << 1;
	}

	// 使用 AND 和反相表示 OR 表达式。
	int lor(int lhs, int rhs) { return inv(land(inv(lhs), inv(rhs))); }

	// 按单元复用 AIG，保持递归导入期间的缓存引用有效。
	CrCellAig &cell_aig(Cell *cell)
	{
		return cell_aigs.try_emplace(cell, cell).first->second;
	}

	// 递归导入单元 AIG 节点并缓存结果。
	int import_node(Cell *cell, CrCellAig &cached, int index)
	{
		if (cached.imported[index] >= 0)
			return cached.imported[index];
		const AigNode &node = cached.aig.nodes[index];
		int value = 0;
		if (node.left_parent >= 0)
			value = land(import_node(cell, cached, node.left_parent), import_node(cell, cached, node.right_parent));
		else if (node.portbit >= 0)
			value = signal(cell->getPort(node.portname)[node.portbit]);
		return cached.imported[index] = value ^ node.inverter;
	}

	// 导入单元输出的组合逻辑，将不支持的单元输出作为边界。
	int import_cell(Cell *cell, IdString outport, int outbit)
	{
		auto &cached = cell_aig(cell);
		if (cell->type == ID($pmux)) {
			int width = GetSize(cell->getPort(ID::A));
			const SigSpec &b = cell->getPort(ID::B);
			const SigSpec &s = cell->getPort(ID::S);
			if (cached.any_select < 0) {
				int any_select = 0;
				for (auto bit : s)
					any_select = lor(any_select, signal(bit));
				cached.any_select = any_select;
			}
			int selected = 0;
			for (int i = 0; i < GetSize(s); i++)
				selected = lor(selected, land(signal(b[i * width + outbit]), signal(s[i])));
			return lor(land(signal(cell->getPort(ID::A)[outbit]), inv(cached.any_select)), selected);
		}
		if (cached.aig.nodes.empty())
			return leaf(cell->getPort(outport)[outbit]);
		return import_node(cell, cached, cached.outputs.at({outport, outbit}));
	}

	// 沿信号驱动构建 AIG，并记录组合环的边界。
	int signal(SigBit bit)
	{
		bit = sigmap(bit);
		if (bit.wire == nullptr)
			return leaf(bit);
		auto cached = signal_cache.find(bit);
		if (cached != signal_cache.end())
			return cached->second;
		if (active.count(bit)) {
			cyclic_signals.insert(bit);
			return leaf(bit);
		}
		auto driver = drivers.find(bit);
		if (driver == drivers.end())
			return leaf(bit);
		active.insert(bit);
		int result = import_cell(driver->second.cell, driver->second.port, driver->second.offset);
		active.erase(bit);
		return signal_cache[bit] = result;
	}
};

// 每个分支包含选择条件，以及按寄存器位序排列的数据 literal。
struct CrBranch {
	int coefficient;
	vector<int> source;
};

struct CrCandidate {
	vector<CrBranch> branches;
	int feedback = -1;
	int controls = 0;
};

struct CtrlRestructureWorker {
	Module *module;
	Design *design;
	SigMap sigmap;
	CrAig aig;
	vector<int> refs;
	vector<bool> invalid;
	int considered = 0, restructured = 0, rejected_partial = 0;
	int rejected_nonexclusive = 0, rejected_inequivalent = 0;
	int shared_controls = 0, data_inputs = 0;

	// 初始化当前模块的信号映射和 AIG 分析状态。
	CtrlRestructureWorker(Design *design, Module *module) : module(module), design(design), sigmap(module), aig(module, sigmap) {}

	// 增加非常量 AIG 节点的引用计数。
	void reference(int literal)
	{
		int node = literal >> 1;
		if (node)
			refs[node]++;
	}

	// 统计 AIG 引用，并按拓扑顺序标记含未知值或组合环的节点。
	void prepare_references()
	{
		vector<int> external;
		for (auto cell : module->cells()) {
			bool represented = cell->type == ID($pmux) || !aig.cell_aig(cell).aig.nodes.empty();
			if (represented)
				continue;
			for (auto &conn : cell->connections())
				if (!cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						external.push_back(aig.signal(bit));
		}
		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					external.push_back(aig.signal(bit));
		aig.cell_aigs.clear();
		refs.resize(GetSize(aig.nodes));
		invalid.resize(GetSize(aig.nodes));
		for (int node = 1; node < GetSize(aig.nodes); node++)
			if (aig.nodes[node].lhs >= 0) {
				reference(aig.nodes[node].lhs);
				reference(aig.nodes[node].rhs);
				invalid[node] = invalid[aig.nodes[node].lhs >> 1] || invalid[aig.nodes[node].rhs >> 1];
			} else
				invalid[node] = aig.nodes[node].leaf.wire == nullptr || aig.cyclic_signals.count(aig.nodes[node].leaf);
		for (int literal : external)
			reference(literal);
	}

	// 递减引用计数，收集 MFFC 内部节点及边界。
	void dereference(int literal, vector<int> &cone, pool<int> &boundary)
	{
		int node = literal >> 1;
		if (!node)
			return;
		log_assert(refs[node] > 0);
		if (--refs[node] != 0 || aig.nodes[node].lhs < 0) {
			boundary.insert(node);
			return;
		}
		cone.push_back(node);
		dereference(aig.nodes[node].lhs, cone, boundary);
		dereference(aig.nodes[node].rhs, cone, boundary);
	}

	// 恢复计算 MFFC 时递减的引用计数。
	void restore(int literal)
	{
		int node = literal >> 1;
		if (!node)
			return;
		if (refs[node]++ == 0 && aig.nodes[node].lhs >= 0) {
			restore(aig.nodes[node].lhs);
			restore(aig.nodes[node].rhs);
		}
	}

	// 将指定数据变量赋值为一、其余赋值为零，求取控制余因子。
	int cofactor(int literal, const pool<int> &cut, const pool<int> &data, int selected, dict<int, int> &memo)
	{
		bool inverted = literal & 1;
		int node = literal >> 1;
		if (!node)
			return literal;
		if (data.count(node))
			return ((node == selected) ? 1 : 0) ^ inverted;
		if (cut.count(node))
			return literal;
		log_assert(aig.nodes[node].lhs >= 0);
		auto cached = memo.find(node);
		if (cached != memo.end())
			return cached->second ^ inverted;
		int value = aig.land(cofactor(aig.nodes[node].lhs, cut, data, selected, memo),
				     cofactor(aig.nodes[node].rhs, cut, data, selected, memo));
		memo[node] = value;
		return value ^ inverted;
	}

	// 提取逐位 MFFC 边界，将仅出现一次的节点归为数据变量。
	bool classify_boundaries(const vector<int> &roots, vector<pool<int>> &boundaries, vector<pool<int>> &data, int &controls)
	{
		struct BoundaryUse {
			int count = 0;
			int bit;
		};
		dict<int, BoundaryUse> uses;
		for (int bit = 0; bit < GetSize(roots); bit++) {
			vector<int> cone;
			dereference(roots[bit], cone, boundaries[bit]);
			// 重汇聚节点可能先被记作边界，全部引用移除后需从边界中删除。
			for (auto node = cone.rbegin(); node != cone.rend(); ++node)
				boundaries[bit].erase(*node);
			restore(roots[bit]);
			for (int node : boundaries[bit]) {
				auto &use = uses[node];
				use.count++;
				use.bit = bit;
			}
		}
		for (const auto &item : uses) {
			if (item.second.count == GetSize(roots))
				controls++;
			else if (item.second.count == 1)
				data[item.second.bit].insert(item.first);
			else {
				rejected_partial++;
				return false;
			}
		}
		return controls > 0 && !data[0].empty();
	}

	// 按相同控制系数逐位组装数据总线，遇到重复或缺失系数立即拒绝。
	bool match_branches(const vector<int> &roots, const vector<pool<int>> &boundaries,
			    const vector<pool<int>> &data, CrCandidate &candidate)
	{
		for (int bit = 0; bit < GetSize(roots); bit++) {
			dict<int, int> source_for_coefficient;
			for (int node : data[bit]) {
				dict<int, int> memo;
				int coefficient = cofactor(roots[bit], boundaries[bit], data[bit], node, memo);
				if (coefficient == 0)
					continue;
				if (!source_for_coefficient.emplace(coefficient, node << 1).second)
					return false;
			}
			if (bit == 0) {
				if (GetSize(source_for_coefficient) < 2)
					return false;
				for (const auto &item : source_for_coefficient)
					candidate.branches.push_back({item.first, {item.second}});
				continue;
			}
			if (source_for_coefficient.size() != candidate.branches.size())
				return false;
			for (auto &branch : candidate.branches) {
				auto source = source_for_coefficient.find(branch.coefficient);
				if (source == source_for_coefficient.end())
					return false;
				branch.source.push_back(source->second);
			}
		}
		return true;
	}

	// 从寄存器输入提取共享控制和数据分支，并识别保持原值的反馈分支。
	bool analyze(const FfData &ff, CrCandidate &candidate)
	{
		vector<int> roots;
		for (auto bit : ff.sig_d) {
			int root = aig.signal(bit);
			if (invalid[root >> 1])
				return false;
			roots.push_back(root);
		}
		vector<pool<int>> boundaries(ff.width), data(ff.width);
		if (!classify_boundaries(roots, boundaries, data, candidate.controls))
			return false;
		if (!match_branches(roots, boundaries, data, candidate))
			return false;
		vector<int> feedback;
		for (auto bit : ff.sig_q)
			feedback.push_back(aig.signal(bit));
		for (int i = 0; i < GetSize(candidate.branches); i++)
			if (candidate.branches[i].source == feedback) {
				candidate.feedback = i;
				break;
			}
		return true;
	}

	// 将 AIG literal 转换为 SAT 表达式并复用已导入节点。
	int import_sat(QuickConeSat &sat, int literal, dict<int, int> &memo)
	{
		bool inverted = literal & 1;
		int node = literal >> 1;
		if (!node)
			return inverted ? sat.ez->CONST_TRUE : sat.ez->CONST_FALSE;
		auto cached = memo.find(node);
		int value;
		if (cached != memo.end()) {
			value = cached->second;
		} else {
			const auto &entry = aig.nodes[node];
			value = entry.lhs < 0 ? sat.importSigBit(entry.leaf)
				: sat.ez->AND(import_sat(sat, entry.lhs, memo), import_sat(sat, entry.rhs, memo));
			memo[node] = value;
		}
		return inverted ? sat.ez->NOT(value) : value;
	}

	// 按有效极性将控制信号转换为 SAT 表达式。
	int active_signal(QuickConeSat &sat, SigBit signal, bool polarity)
	{
		int value = sat.importSigBit(signal);
		return polarity ? value : sat.ez->NOT(value);
	}

	// 证明控制系数互斥、数据分解正确及寄存器下一状态等价。
	bool prove(const FfData &ff, const CrCandidate &candidate, ModWalker &walker)
	{
		QuickConeSat sat(walker);
		dict<int, int> memo;
		vector<int> coefficients;
		for (const auto &branch : candidate.branches)
			coefficients.push_back(import_sat(sat, branch.coefficient, memo));
		vector<vector<int>> sources;
		for (const auto &branch : candidate.branches) {
			vector<int> values;
			for (int value : branch.source)
				values.push_back(import_sat(sat, value, memo));
			sources.push_back(values);
		}
		vector<int> original = sat.importSig(ff.sig_d);
		vector<int> q = sat.importSig(ff.sig_q);
		int old_enable = sat.ez->CONST_TRUE;
		if (ff.has_ce)
			old_enable = active_signal(sat, ff.sig_ce[0], ff.pol_ce);
		int reset = sat.ez->CONST_FALSE;
		if (ff.has_srst)
			reset = active_signal(sat, ff.sig_srst[0], ff.pol_srst);
		// 按 CE 和同步复位的优先级构造单个寄存器位的下一状态。
		auto next_state = [&](int bit, int data, int enable) {
			if (!ff.has_srst)
				return sat.ez->ITE(enable, data, q[bit]);
			int reset_value = ff.val_srst[bit] == State::S1 ? sat.ez->CONST_TRUE : sat.ez->CONST_FALSE;
			if (ff.ce_over_srst)
				return sat.ez->ITE(enable, sat.ez->ITE(reset, reset_value, data), q[bit]);
			return sat.ez->ITE(reset, reset_value, sat.ez->ITE(enable, data, q[bit]));
		};
		sat.prepare();
		int seen = sat.ez->CONST_FALSE, overlap = sat.ez->CONST_FALSE;
		for (int coefficient : coefficients) {
			overlap = sat.ez->OR(overlap, sat.ez->AND(seen, coefficient));
			seen = sat.ez->OR(seen, coefficient);
		}
		if (sat.ez->solve(overlap)) {
			rejected_nonexclusive++;
			return false;
		}
		int new_enable = old_enable;
		if (candidate.feedback >= 0) {
			int write_enable = sat.ez->NOT(coefficients[candidate.feedback]);
			if (ff.has_srst && ff.ce_over_srst)
				write_enable = sat.ez->OR(write_enable, reset);
			new_enable = sat.ez->AND(old_enable, write_enable);
		}
		int first_source = candidate.feedback == 0 ? 1 : 0;
		vector<int> differences;
		for (int bit = 0; bit < ff.width; bit++) {
			vector<int> products;
			for (int i = 0; i < GetSize(coefficients); i++)
				products.push_back(sat.ez->AND(sources[i][bit], coefficients[i]));
			int expansion = sat.ez->expression(ezSAT::OpOr, products);
			differences.push_back(sat.ez->XOR(original[bit], expansion));
			int replacement = sources[first_source][bit];
			for (int i = first_source + 1; i < GetSize(coefficients); i++)
				if (i != candidate.feedback)
					replacement = sat.ez->ITE(coefficients[i], sources[i][bit], replacement);
			int old_next = next_state(bit, original[bit], old_enable);
			int new_next = next_state(bit, replacement, new_enable);
			differences.push_back(sat.ez->XOR(old_next, new_next));
		}
		if (sat.ez->solve(sat.ez->expression(ezSAT::OpOr, differences))) {
			rejected_inequivalent++;
			return false;
		}
		return true;
	}

	// 按完整 literal 缓存 RTLIL 表达式，复用 AND 和反相单元。
	SigBit materialize(int literal, dict<int, SigBit> &memo)
	{
		if (literal < 2)
			return literal ? State::S1 : State::S0;
		auto cached = memo.find(literal);
		if (cached != memo.end())
			return cached->second;
		const auto &node = aig.nodes[literal >> 1];
		SigBit value;
		if (literal & 1)
			value = module->Not(NEW_ID, materialize(aig.inv(literal), memo));
		else if (node.lhs < 0)
			value = node.leaf;
		else
			value = module->And(NEW_ID, materialize(node.lhs, memo), materialize(node.rhs, memo));
		return memo[literal] = value;
	}

	// 将 RTLIL 控制信号转换为高电平有效。
	SigBit active_rtl(SigBit signal, bool polarity)
	{
		if (polarity)
			return signal;
		return module->Not(NEW_ID, signal);
	}

	// 为已通过证明的寄存器生成共享控制、数据 MUX 和更新使能。
	void transform(FfData &ff, const CrCandidate &candidate, dict<int, SigBit> &memo)
	{
		SigSpec new_data;
		int source_count = 0;
		for (int i = 0; i < GetSize(candidate.branches); i++) {
			if (i == candidate.feedback)
				continue;
			SigSpec source;
			for (int value : candidate.branches[i].source)
				source.append(materialize(value, memo));
			if (source_count++ == 0)
				new_data = source;
			else
				new_data = module->Mux(NEW_ID, new_data, source, materialize(candidate.branches[i].coefficient, memo));
		}
		ff.sig_d = new_data;
		if (candidate.feedback >= 0) {
			SigBit write_enable = materialize(aig.inv(candidate.branches[candidate.feedback].coefficient), memo);
			if (ff.has_srst && ff.ce_over_srst) {
				SigBit reset = active_rtl(ff.sig_srst[0], ff.pol_srst);
				write_enable = module->Or(NEW_ID, write_enable, reset);
			}
			if (ff.has_ce)
				write_enable = module->And(NEW_ID, active_rtl(ff.sig_ce[0], ff.pol_ce), write_enable);
			ff.has_ce = true;
			ff.pol_ce = true;
			ff.sig_ce = write_enable;
		}
		ff.emit();
		restructured++;
		shared_controls += candidate.controls;
		data_inputs += source_count;
		log("Restructured control cone for %s.%s: width=%d controls=%d data_sources=%d muxes=%d.\n", module, ff.name, ff.width,
		    candidate.controls, GetSize(candidate.branches), source_count - 1);
	}

	// 共用原始模块索引完成候选证明，再统一生成通过证明的电路。
	void run()
	{
		FfInitVals initvals(&sigmap, module);
		vector<FfData> registers;
		for (auto cell : module->selected_cells()) {
			if (!StaticCellTypes::categories.is_ff(cell->type))
				continue;
			FfData ff(&initvals, cell);
			if (!ff.has_clk || ff.width < 2 || ff.is_fine)
				continue;
			log_assert(!ff.has_ce || GetSize(ff.sig_ce) == 1);
			registers.push_back(ff);
			for (auto bit : ff.sig_d)
				aig.signal(bit);
			for (auto bit : ff.sig_q)
				aig.signal(bit);
		}
		considered = GetSize(registers);
		if (registers.empty())
			return;
		prepare_references();
		std::unique_ptr<ModWalker> walker;
		vector<pair<FfData, CrCandidate>> changes;
		for (auto &ff : registers) {
			CrCandidate candidate;
			if (!analyze(ff, candidate))
				continue;
			if (!walker)
				walker = std::make_unique<ModWalker>(design, module);
			if (prove(ff, candidate, *walker))
				changes.emplace_back(ff, std::move(candidate));
		}
		dict<int, SigBit> memo;
		for (auto &change : changes)
			transform(change.first, change.second, memo);
	}
};

struct CtrlRestructurePass : public Pass {
	// 注册控制逻辑重构命令。
	CtrlRestructurePass() : Pass("ctrl_restructure", "restructure shared control logic feeding word registers") {}
	// 输出命令用法及转换功能说明。
	void help() override
	{
		log("\n    ctrl_restructure [selection]\n\n");
		log("Extract shared AIG control functions, move feedback to a clock enable,\n");
		log("and rebuild the data path with a minimum selection mux.\n\n");
	}
	// 在选中模块中执行重构并汇总转换统计。
	void execute(vector<string> args, Design *design) override
	{
		log_header(design, "Executing CTRL_RESTRUCTURE pass.\n");
		extra_args(args, 1, design);
		int considered = 0, changed = 0, partial = 0, nonexclusive = 0;
		int inequivalent = 0, controls = 0, data = 0;
		for (auto module : design->selected_modules()) {
			CtrlRestructureWorker worker(design, module);
			worker.run();
			considered += worker.considered;
			changed += worker.restructured;
			partial += worker.rejected_partial;
			nonexclusive += worker.rejected_nonexclusive;
			inequivalent += worker.rejected_inequivalent;
			controls += worker.shared_controls;
			data += worker.data_inputs;
		}
		log("ctrl_restructure: groups_considered=%d groups_restructured=%d groups_rejected_partial=%d "
		    "groups_rejected_nonexclusive=%d groups_rejected_inequivalent=%d shared_controls=%d data_inputs=%d\n",
		    considered, changed, partial, nonexclusive, inequivalent, controls, data);
	}
} CtrlRestructurePass;

PRIVATE_NAMESPACE_END
