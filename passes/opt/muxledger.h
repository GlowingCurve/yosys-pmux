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
		// 每个候选决策开始时清空 used_bits 缓存：五个 Pass 都是先用账本结算、再改写端口，
		// 一次决策之内端口连接不变，缓存因此不会把改写前的位宽带到改写之后
		// （完整的失效条件见 clear_cost_cache 上方的注释）
		clear_cost_cache();

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

	// 计划删除整个单元：记入删除所得，并释放该单元全部输入端口的信号位。
	// used_width_hint 是调用点已知的有效位宽（口径同 cell_cost），默认 0 表示由账本自行推断；
	// 它只影响代价估计，不影响删除与释放的行为。
	void drop_cell(Cell *cell, int64_t used_width_hint = 0)
	{
		dropped.insert(cell);
		removed_gain += cell_cost(cell, used_width_hint);
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

	// ------------------------------------------------------------------
	// LUT4 当量折算
	// ------------------------------------------------------------------
	//
	// 记账单位是“4 输入查找表（LUT4）当量”：一个 LUT4 有 4 个输入、1 个输出，所以
	//   * 每个输出位都要占一个 LUT4 的算子（$mux、按位逻辑）按位折算；
	//   * 能把 4 位一组塞进同一个 LUT4 的算子（$eq 一类分组比较、$reduce_* 一类归约）
	//     按“4 位一组”折算。
	// 五个 Pass 原先直接使用 kernel/cost.cc 的 CellCosts 抽象门数：8 位 $eq 记 16 分、
	// 16 位 $lt 记 112 分，比真实 LUT4 数高 5~10 倍，账本因此把亏本的树重构判成有收益。
	// 下面每个算子旁边一行注释说明折算依据；折算表没有覆盖的类型仍然回退 CellCosts::get()。

	// 4 位一组的组数：ceil(W/4)
	static int64_t lut4_groups(int64_t width) { return width > 0 ? (width + 3) / 4 : 0; }

	// 把 w4 个分组结果用 LUT4 归约掉需要的个数：ceil(max(w4-1,0)/3)
	static int64_t lut4_reduce(int64_t w4) { return (std::max<int64_t>(w4 - 1, 0) + 2) / 3; }

	// 一个信号上真正“有用”的位：常量位与未连接的位（bit.wire 为假）不计价；
	// live 非空时，live 中计数不大于 0 的位（没有任何使用者）也不计价；
	// live 为空表示只看连接关系，所有 wire 位都算有用。
	static int64_t sig_bits(const SigSpec &sig, const dict<SigBit,int> *live)
	{
		int64_t n = 0;
		for (auto bit : sig) {
			if (!bit.wire)
				continue;
			if (live != nullptr && live->at(bit, 0) <= 0)
				continue;
			n++;
		}
		return n;
	}

	// 端口 port 上的有用位数；端口不存在时 getPort 返回空信号，计 0
	static int64_t port_used_bits(const Cell *cell, IdString port, const dict<SigBit,int> *live)
	{
		return sig_bits(cell->getPort(port), live);
	}

	// used_bits 的默认规则需要端口方向。和 MuxLedger 的成员 celltypes 一样只装
	// internals_eval 与 stdcells_eval；表构造一次后只读，多个 Pass 共用。
	// 用指针且不释放：避免静态析构顺序问题，也避免每次调用重建端口表。
	static const CellTypes &static_celltypes()
	{
		static CellTypes *celltypes = nullptr;
		if (celltypes == nullptr) {
			celltypes = new CellTypes();
			celltypes->setup_internals_eval();
			celltypes->setup_stdcells_eval();
		}
		return *celltypes;
	}

	// used_bits() 结果的缓存：候选枚举的内层循环对同一批单元反复问价，缓存把“遍历端口”
	// 这一步省掉，cell_cost 因此不会在每次调用时重新扫描单元端口，更不会扫描整个模块。
	// 失效条件（任一条不满足就重新计算）：
	//   * 缓存项记录的 module / design / 单元名 / 单元类型与当前单元不一致：Cell* 地址在
	//     module->remove() 之后可能被新单元复用，而单元名在模块内唯一，用它可以识别复用；
	//     design 换了说明整个代价缓存都已过期；
	//   * 缓存条数达到 kUsedBitsCacheLimit，整体清空，避免跨 Pass 无限增长；
	//   * MuxLedger 构造函数（每个候选决策开始时）清空：五个 Pass 都是先结算、后改写端口，
	//     一次决策之内端口连接不变，所以缓存只在一个决策内有效，不会把改写前的位宽带到
	//     改写之后；调用点需要更细的失效点时可以自己调用 clear_cost_cache()。
	static const int kUsedBitsCacheLimit = 4096;

	struct UsedBitsEntry {
		Module *module;
		Design *design;
		IdString name, type;
		int64_t bits;
	};

	static dict<Cell *, UsedBitsEntry> &used_bits_cache()
	{
		static dict<Cell *, UsedBitsEntry> cache;
		return cache;
	}

	static void clear_cost_cache()
	{
		used_bits_cache().clear();
	}

	// 缓存命中返回缓存值，没有可用缓存返回 -1
	static int64_t used_bits_cached(Cell *cell)
	{
		auto &cache = used_bits_cache();
		auto it = cache.find(cell);
		if (it == cache.end())
			return -1;
		Module *module = cell->module;
		if (module == nullptr || it->second.module != module || it->second.design != module->design ||
				it->second.name != cell->name || it->second.type != cell->type) {
			cache.erase(it);
			return -1;
		}
		return it->second.bits;
	}

	static void used_bits_store(Cell *cell, int64_t bits)
	{
		if (cell->module == nullptr)
			return;
		auto &cache = used_bits_cache();
		if (GetSize(cache) >= kUsedBitsCacheLimit)
			cache.clear();
		UsedBitsEntry entry;
		entry.module = cell->module;
		entry.design = cell->module->design;
		entry.name = cell->name;
		entry.type = cell->type;
		entry.bits = bits;
		cache[cell] = entry;
	}

	static int64_t used_bits_uncached(Cell *cell, const dict<SigBit,int> *live)
	{
		IdString type = cell->type;

		// $mux/$pmux：数据位宽取 A/B/Y 三个端口有用位计数的最小值 —— 三条支路在同一个
		// 位置上都是真实信号时这一位才有一级二选一逻辑；任一端口缺失或全为常量都按 0 计。
		if (type.in(ID($mux), ID($pmux)))
			return std::min(port_used_bits(cell, ID::A, live),
					std::min(port_used_bits(cell, ID::B, live), port_used_bits(cell, ID::Y, live)));

		// 比较器：规模由操作数决定（Y 只有一位，按输出位宽会永远得到 1），取 A/B 中较大的
		// 有用位计数；常量操作数会折进 LUT 的输入，不减少 LUT4 个数。$eqx/$nex 结构相同。
		if (type.in(ID($eq), ID($ne), ID($eqx), ID($nex), ID($lt), ID($le), ID($gt), ID($ge)))
			return std::max(port_used_bits(cell, ID::A, live), port_used_bits(cell, ID::B, live));

		// 归约与逻辑非：把 A 的每一位归约掉（$reduce_bool 就是 |A| != 0），宽度是 A 的有用位数
		if (type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool), ID($logic_not)))
			return port_used_bits(cell, ID::A, live);

		// 逻辑与/或：两个操作数各自归约，宽度按两个有用位数之和折算
		if (type.in(ID($logic_and), ID($logic_or)))
			return port_used_bits(cell, ID::A, live) + port_used_bits(cell, ID::B, live);

		// 按位逻辑：每一位结果占一个 LUT4，只有三个端口在同一位置都是真实信号时才有逻辑
		if (type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($andnot), ID($ornot), ID($bweqx)))
			return std::min(port_used_bits(cell, ID::A, live),
					std::min(port_used_bits(cell, ID::B, live), port_used_bits(cell, ID::Y, live)));

		// 单目取反：A 与 Y 都真实的位才有逻辑
		if (type == ID($not))
			return std::min(port_used_bits(cell, ID::A, live), port_used_bits(cell, ID::Y, live));

		// 算术：宽度就是结果宽度
		if (type.in(ID($add), ID($sub), ID($alu), ID($neg)))
			return port_used_bits(cell, ID::Y, live);

		// 默认：所有输出端口上真正被使用的位（bit.wire 为真，且 live 为空或计数大于 0）
		int64_t n = 0;
		for (auto &conn : cell->connections())
			if (muxledger_port_output(static_celltypes(), cell, conn.first))
				n += sig_bits(conn.second, live);
		return n;
	}

	// 单元“真正用到”的位宽 W：折算公式里的 W 就是这个数。
	// 默认规则：只统计输出端口上 bit.wire 为真、且（live 为空或 live 中计数大于 0）的位，
	// 未连接的位、常量位、没有使用者的位都不计价；Y 只有一位而规模由输入决定的算子、
	// 以及 $mux/$pmux 按各自结构特判，见 used_bits_uncached 各分支。
	//
	// live 的键必须与 cell 端口上的信号位同一口径：账本内部的 use_count 是 sigmap 之后的，
	// 而单元端口上是原始信号位，所以账本内部一律不传 live（live 只给在 sigmap 之后建表、
	// 又确认过别名关系的调用点用）。不传 live 时会查缓存，传了 live 就不缓存。
	static int64_t used_bits(Cell *cell, const dict<SigBit,int> *live = nullptr)
	{
		if (live == nullptr) {
			int64_t cached = used_bits_cached(cell);
			if (cached >= 0)
				return cached;
		}
		int64_t bits = used_bits_uncached(cell, live);
		if (live == nullptr)
			used_bits_store(cell, bits);
		return bits;
	}

	// 折算公式里的有效位宽：调用点给了 hint 就用 hint，否则由 used_bits() 推断（带缓存）
	static int64_t effective_width(Cell *cell, int64_t used_width_hint)
	{
		return used_width_hint > 0 ? used_width_hint : used_bits(cell);
	}

	// 单个单元的 LUT4 当量代价。
	// used_width_hint 是调用点已知的有效位宽（口径与 used_bits() 的返回值一致），大于 0 时
	// 优先使用：候选枚举的内层循环里调用点自己知道这次变换涉及多少位，传进来可以省掉一次
	// 端口遍历；0 表示由 used_bits() 推断（有缓存）。折算表覆盖不到的类型回退 CellCosts::get()。
	static int64_t cell_cost(Cell *cell, int64_t used_width_hint = 0)
	{
		IdString type = cell->type;

		// $mux：每位一个 LUT4（一个 LUT4 是 4 输入 1 输出，2:1 选择的每个输出位各占一个）
		if (type == ID($mux))
			return effective_width(cell, used_width_hint);

		// $pmux：k 选 1 等价于 k-1 级二选一，每位 max(S_WIDTH-1,1) 个 LUT4；
		// S_WIDTH 为 1 时它退化成 $mux，所以下界取 1（这一档 CellCosts 会记 0）
		if (type == ID($pmux))
			return effective_width(cell, used_width_hint) * std::max<int64_t>((int64_t)cell->getParam(ID::S_WIDTH).as_int() - 1, 1);

		// $eq/$ne（$eqx/$nex 结构相同）：4 位一组做分组相等，w4 = ceil(W/4) 个 LUT4
		// —— 比较器一侧是常量时 4 个信号位正好占满 LUT4 的 4 个输入，这五个 Pass 里的
		// 选择译码正是 base == const 的形式，账本就按这个口径 —— 再用 LUT4 把 w4 个结果
		// 按 4 个一组归约，即 w4 + ceil(max(w4-1,0)/3)。
		// 例：8 位 $eq = 2 个 LUT4 做 4 位分组相等 + 1 个 LUT4 归约 = 3 个 LUT4。
		if (type.in(ID($eq), ID($ne), ID($eqx), ID($nex))) {
			int64_t w4 = lut4_groups(effective_width(cell, used_width_hint));
			return w4 + lut4_reduce(w4);
		}

		// $lt/$le/$gt/$ge：每个 4 位小组 2 个 LUT4（组内相等、组内大小），小组之间再按
		// 3 个一组归约，即 2*w4 + ceil(max(w4-1,0)/3)；16 位 = 8 + 1 = 9，落在实测的 8~11 之内。
		// （任务清单写的 w4 + ceil(max(w4-1,0)/3) 在 16 位只有 5，低于实测，所以按大小比较
		// 每个小组多一个 LUT4 做了修正。）
		if (type.in(ID($lt), ID($le), ID($gt), ID($ge))) {
			int64_t w4 = lut4_groups(effective_width(cell, used_width_hint));
			return 2 * w4 + lut4_reduce(w4);
		}

		// $reduce_* 与 $logic_not：每 4 位一个 LUT4 归约，宽度是操作数 A 的位数
		if (type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool), ID($logic_not)))
			return lut4_groups(effective_width(cell, used_width_hint));

		// $logic_and/$logic_or：两个操作数各自归约，按 ceil(W/4)，W 取两个操作数位数之和
		if (type.in(ID($logic_and), ID($logic_or)))
			return lut4_groups(effective_width(cell, used_width_hint));

		// $add/$sub/$alu/$neg：进位链按 W 位线性建模，W 位加法约 W 个 LUT4
		// （进位的归约不是 4 位一组，所以不能套 lut4_groups）
		if (type.in(ID($add), ID($sub), ID($alu), ID($neg)))
			return effective_width(cell, used_width_hint);

		// 按位逻辑（$not/$and/$or/$xor/$xnor/$andnot/$ornot/$bweqx）：每个输出位都要一个 LUT4，
		// 所以按位宽线性折算，与 $mux 每比特 1 个 LUT4 的口径一致（4 位一组在这里不适用）
		if (type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($andnot), ID($ornot), ID($bweqx)))
			return effective_width(cell, used_width_hint);

		// $lut：W 个输入的查找表，4 输入以内 1 个 LUT4，之后每多一个输入翻一倍。
		// 这里不需要 used_bits()，也就不做端口遍历。
		if (type == ID($lut))
			return (int64_t)1 << std::max((int64_t)cell->getParam(ID::WIDTH).as_int() - 4, (int64_t)0);

		// 折算表没有覆盖的类型：回退 CellCosts 的抽象门数。
		// CellCosts 需要一个 Design 才能构造，而 cell_cost 是静态成员拿不到 module，
		// 所以改用 cell->module->design。函数内的 static 实例用来复用 CellCosts 的缓存；
		// 设计被换掉（旧的设计可能已经销毁）时重新构造，避免复用悬垂指针和过期的模块代价缓存。
		static Design *cached_design = nullptr;
		static CellCosts costs(nullptr);
		if (cached_design != cell->module->design) {
			cached_design = cell->module->design;
			costs = CellCosts(cached_design);
		}
		return costs.get(cell);
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
