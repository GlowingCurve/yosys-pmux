#ifndef MUXLEDGER_H
#define MUXLEDGER_H

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/cost.h"

YOSYS_NAMESPACE_BEGIN

// 端口方向：未知类型的单元（cell_known 为假）的每一个端口同时算输入和输出，
// 这样既不会漏记使用者，也不会漏记驱动关系，避免把还有使用者的单元误判成死亡。
static inline bool muxledger_port_input(const CellTypes &celltypes, const Cell *cell, IdString port)
{
	return !celltypes.cell_known(cell->type) || celltypes.cell_input(cell->type, port);
}

static inline bool muxledger_port_output(const CellTypes &celltypes, const Cell *cell, IdString port)
{
	return !celltypes.cell_known(cell->type) || celltypes.cell_output(cell->type, port);
}

// muxtree_share、opt_muxcomb、opt_muxinfer、opt_muxrebuild、opt_reshape 共用的代价账本。
//
// 这五个 Pass 原先各自估算“这次变换划不划算”，口径互不相同。账本把使用者计数、驱动关系和
// 代价增减集中到一处：变换期间用 drop_cell/drop_port/acquire/add_cost/sub_cost 记账，
// 最后用 dead_cost/net_gain 结算，其中还包括变换之后失去全部使用者的单元带来的连带收益。
//
// 账本内部统一使用 sigmap 之后的信号位：建立使用者计数、释放、占用、判断死亡全部
// 先过一遍 SigMap，因此调用者传原始信号位或 sigmap 之后的信号位都可以。五个 Pass 内部
// 普遍在 sigmap 之后的位上工作，若两边口径不同，某个信号的原始位被释放到计数归零、
// 而新逻辑通过别名位占用它时，驱动单元会被误判成死亡。
// dead_cost 会把结算结果缓存下来，结算之后不应再 drop/acquire。
struct MuxLedger
{
	Module *module;

	// 以下是内部记账状态，不属于对外接口
	SigMap sigmap;                       // 统一信号位口径
	CellTypes celltypes;                 // 端口方向，只装 internals_eval 与 stdcells_eval
	dict<SigBit, int> use_count;         // 使用者计数
	dict<SigBit, Cell *> driver;         // 信号位的驱动单元
	pool<SigBit> port_bits;              // 模块输出端口位，永远算有使用者
	pool<SigBit> freed;                  // drop_cell/drop_port 释放过的信号位，dead_cost 的传播起点
	pool<Cell *> dropped;                // 已经整单元删除的单元，不再计入死亡结果
	pool<Cell *> dead_cells;             // dead_cost 已经计入过的死亡单元
	int64_t removed_gain = 0;            // 删除所得
	int64_t reduced_gain = 0;            // 减少所得
	int64_t added_cost = 0;              // 新增所得（新逻辑的估计代价）
	bool dead_done = false;              // dead_result 是否已经算好
	int64_t dead_result = 0;

	MuxLedger(Module *module) : module(module)
	{
		sigmap.set(module);
		celltypes.setup_internals_eval();
		celltypes.setup_stdcells_eval();

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(SigSpec(wire)))
					if (bit.wire)
						port_bits.insert(bit);

		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				bool input = muxledger_port_input(celltypes, cell, conn.first);
				bool output = muxledger_port_output(celltypes, cell, conn.first);
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire)
						continue;
					if (output)
						driver[bit] = cell;
					if (input)
						use_count[bit]++;
				}
			}
	}

	// 计划删除整个单元：记入删除所得，并释放该单元全部输入端口的信号位
	void drop_cell(Cell *cell)
	{
		dropped.insert(cell);
		removed_gain += cell_cost(cell);
		release_inputs(cell);
	}

	// 计划改写端口，释放旧值的全部信号位；不记账，代价变化由调用者用 sub_cost 补上
	void drop_port(Cell *cell, IdString port)
	{
		release(sigmap(cell->getPort(port)));
	}

	// 计划新增的连接占用的信号位
	void acquire(const SigSpec &sig)
	{
		for (auto bit : sigmap(sig))
			if (bit.wire)
				use_count[bit]++;
	}

	// 计划新增逻辑的估计代价
	void add_cost(int64_t cost)
	{
		added_cost += cost;
	}

	// 单元代价减少的部分（例如端口变短）
	void sub_cost(int64_t cost)
	{
		reduced_gain += cost;
	}

	// 失去全部使用者的单元，代价之和。第一次调用时完成传播并缓存，之后再调用直接返回缓存值
	int64_t dead_cost()
	{
		if (dead_done)
			return dead_result;

		// 传播：从 drop_cell/drop_port 释放过的信号位出发，反向查找驱动它们的单元；
		// 单元死亡就把它输入位的计数继续减一，继续向上传播
		std::vector<SigBit> worklist;
		for (auto bit : freed)
			worklist.push_back(bit);

		while (!worklist.empty()) {
			SigBit bit = worklist.back();
			worklist.pop_back();

			auto it = driver.find(bit);
			if (it == driver.end())
				continue;
			Cell *cell = it->second;
			// drop_cell 删掉的单元代价已经记在删除所得里，不再计入死亡结果；
			// dead_cells 防止一个单元被它的多个输出位重复计入
			if (dropped.count(cell) || dead_cells.count(cell) || !cell_dead(cell))
				continue;

			dead_cells.insert(cell);
			dead_result += cell_cost(cell);
			release_inputs(cell, &worklist);
		}

		dead_done = true;
		return dead_result;
	}

	// 删除所得 + 减少所得 + dead_cost() - 新增所得
	int64_t net_gain()
	{
		return removed_gain + reduced_gain + dead_cost() - added_cost;
	}

	// 单个单元的估计代价：CellCosts::get() 之上叠加 $pmux 与 $lut 两条折算规则
	static int64_t cell_cost(Cell *cell)
	{
		// CellCosts 需要一个 Design 才能构造，而 cell_cost 是静态成员拿不到 module，
		// 所以改用 cell->module->design。函数内的 static 实例用来复用 CellCosts 的缓存；
		// 设计被换掉（旧的设计可能已经销毁）时重新构造，避免复用悬垂指针和过期的模块代价缓存。
		static Design *cached_design = nullptr;
		static CellCosts costs(nullptr);
		if (cached_design != cell->module->design) {
			cached_design = cell->module->design;
			costs = CellCosts(cached_design);
		}

		int64_t cost = costs.get(cell);

		// $mux：CellCosts 按 A/B/S 的最大位宽计价，正好是 WIDTH，也就是一位二选一的价格，无需修正。
		//
		// $pmux：CellCosts 同样按 A/B/S 的最大位宽计价，k 路 $pmux 因此与二选一 $mux 同价；
		// 但 k 选 1 等价于 k-1 级二选一，按 WIDTH * (S_WIDTH - 1) 折算之后才与 $mux 口径连上。
		if (cell->type == ID($pmux)) {
			int width = cell->getParam(ID::WIDTH).as_int();
			int s_width = cell->getParam(ID::S_WIDTH).as_int();
			return (int64_t)width * std::max(s_width - 1, 0);
		}

		// $lut：CellCosts 按 2^WIDTH 计价，那是给展平启发式用的；这里按 4 输入查找表折算，
		// 只有超过 4 输入的部分才指数增长。
		if (cell->type == ID($lut)) {
			int width = cell->getParam(ID::WIDTH).as_int();
			return (int64_t)1 << std::max(width - 4, 0);
		}

		return cost;
	}

	// 整个模块的估计代价，忽略没有使用者的单元。不缓存，调用者自己决定是否缓存
	static int64_t module_cost(Module *module)
	{
		SigMap sigmap;
		sigmap.set(module);

		CellTypes celltypes;
		celltypes.setup_internals_eval();
		celltypes.setup_stdcells_eval();

		pool<SigBit> port_bits;
		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(SigSpec(wire)))
					if (bit.wire)
						port_bits.insert(bit);

		dict<SigBit, int> use_count;
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (muxledger_port_input(celltypes, cell, conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							use_count[bit]++;

		int64_t cost = 0;
		for (auto cell : module->cells()) {
			bool has_output = false, used = false;
			for (auto &conn : cell->connections()) {
				if (!muxledger_port_output(celltypes, cell, conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire)
						continue;
					has_output = true;
					// keep 的线网位永远算有使用者
					if (port_bits.count(bit) || bit.wire->get_bool_attribute(ID::keep) || use_count.at(bit, 0) != 0)
						used = true;
				}
			}
			// 没有任何输出位的单元（例如 formal 单元）也算入
			if (used || !has_output)
				cost += cell_cost(cell);
		}
		return cost;
	}

	// 释放一个信号：使用者计数减一，并记为 dead_cost 的传播起点；
	// bits 非空时把释放的信号位追加进去，供 dead_cost 的传播队列使用
	void release(const SigSpec &sig, std::vector<SigBit> *bits = nullptr)
	{
		for (auto bit : sig) {
			if (!bit.wire)
				continue;
			use_count[bit]--;
			freed.insert(bit);
			if (bits != nullptr)
				bits->push_back(bit);
		}
	}

	// 释放一个单元全部输入端口的信号位
	void release_inputs(Cell *cell, std::vector<SigBit> *bits = nullptr)
	{
		for (auto &conn : cell->connections())
			if (muxledger_port_input(celltypes, cell, conn.first))
				release(sigmap(conn.second), bits);
	}

	// 单元的全部输出位都没有使用者、并且都不是模块输出端口位时，认为它已经死亡
	bool cell_dead(Cell *cell) const
	{
		bool has_output = false;
		for (auto &conn : cell->connections()) {
			if (!muxledger_port_output(celltypes, cell, conn.first))
				continue;
			for (auto bit : sigmap(conn.second)) {
				if (!bit.wire)
					continue;
				has_output = true;
				// keep 的线网位永远算有使用者；计数为负说明被多释放了一次，同样按有使用者处理
				if (port_bits.count(bit) || bit.wire->get_bool_attribute(ID::keep) || use_count.at(bit, 0) != 0)
					return false;
			}
		}
		// 没有实际输出位的单元无法判断死亡，按保守处理
		return has_output;
	}
};

YOSYS_NAMESPACE_END

#endif
