#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/satgen.h"
#include "kernel/qcsat.h"
#include "passes/techmap/simplemap.h"
#include "passes/opt/muxtree_index.h"
#include "passes/opt/muxledger.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// smaRTLy section II: walk each muxtree from the root, collect the control values implied
// by the path, and prove further control/data bits constant on a small sub-graph with
// inference rules first and SAT second
//
// 每一处改写都先用 MuxLedger 结算收益；已证明的数据端口常量传播实际改变端口且
// 不增加逻辑时施加，选择端口与结构改写需要正净收益；-force 忽略账本门槛
// SAT 求解的传播步数受 opt_muxinfer.sat_effort 限制，预算耗尽之后不再发起新的求解
struct Cone {
	pool<SigBit> bits;
	pool<Cell *> cells;
};

// 真实端口计划：每批记录(cell名称,port,offset)与原目标。游标只标记实际完成检查的位置。
struct MuxPortAtom {
	IdString cell, port;
	int offset;
	SigBit target;
	bool control = false;
	bool seen = false;
};

struct MuxPortPlan {
	std::vector<MuxPortAtom> atoms;
	dict<std::tuple<IdString, IdString, int>, int> index;
	pool<IdString> cells;
	uint64_t generation = 0;
	int data_pending = 0, control_pending = 0;
	int attempts = 0, proved = 0;
	int data_attempts = 0, control_attempts = 0;

	int find(IdString cell, IdString port, int offset) const
	{
		auto found = index.find(std::make_tuple(cell, port, offset));
		return found == index.end() ? -1 : found->second;
	}
	int add(const MuxPortAtom &atom)
	{
		auto key = std::make_tuple(atom.cell, atom.port, atom.offset);
		if (index.count(key))
			return index.at(key);
		int id = GetSize(atoms);
		index[key] = id;
		atoms.push_back(atom);
		if (atom.control)
			control_pending++;
		else
			data_pending++;
		return id;
	}
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
	int64_t cone_bytes = 0;
	Cone empty_cone;
	struct SolverModel {
		ezSatPtr ez;
		SatGen satgen;
		pool<IdString> names;
		uint64_t generation;
		SolverModel(SigMap &sigmap, uint64_t generation) : satgen(ez.get(), &sigmap), generation(generation) { }
	};
	std::unique_ptr<SolverModel> solver;
	int64_t solver_bytes = 0;
	dict<std::pair<SigBit, std::vector<std::pair<SigBit, bool>>>, int> inference_cache;
	int64_t inference_bytes = 0;
	int64_t search_stop = 0;
	bool search_finished = false;
	pool<IdString> batch_cells, traversal_cells, proof_cells;
	MuxPortPlan *plan = nullptr;
	MuxWorkspace *batch_workspace = nullptr;
	MuxWorkspace *plan_workspace = nullptr;
	std::unique_ptr<MuxBatchReservation> batch_reservation;
	uint64_t batch_generation = 0;
	int batch_data_bits = 0, batch_occurrences = 0, batch_number = 0;
	int batch_atom_begin = 0, batch_atom_end = 0;
	bool batch_data_pending = false;
	int module_batches = 0, roots_done = 0, splits = 0, root_limit_stops = 0;
	int64_t root_data_attempts = 0, root_control_attempts = 0;
	// 当前根已成功登记的generation与完整有序candidates window。
	bool registered_valid = false;
	uint64_t registered_generation = 0;
	std::vector<IdString> registered_window;
	int64_t proof_bytes = 0, solver_prop_margin = 0, joint_prop_margin = 0;
	int64_t joint_model_work = 0, joint_copy_work = 0, joint_sat_work = 0;
	int64_t finish_reserved = 0, finish_consumed = 0;
	int joint_calls = 0, joint_proved = 0, batches_committed = 0;
	MuxResources::Result batch_result = MuxResources::Kept;
	int result_counts[MuxResources::NoGain + 1] = {};

	// (cell, select index) -> constant value, applied after the traversal
	dict<std::pair<Cell *, int>, bool> sel_fix;
	// (cell, data port, offset) -> constant value
	dict<std::tuple<Cell *, IdString, int>, bool> data_fix;

	int sat_calls = 0, rule_hits = 0, sat_hits = 0;
	int rewrites = 0;
	int removed_cells = 0;

	InferWorker(MuxTreeIndex &idx, int max_depth, int max_cells, int max_inputs, bool infer_data,
			bool dry_run, bool force) :
			idx(idx), sigmap(idx.sigmap), max_depth(max_depth), max_cells(max_cells),
			max_inputs(max_inputs), infer_data(infer_data), dry_run(dry_run), force(force),
			sat_effort(idx.costs.resources.sat_limit)
	{
		sat_spent = idx.costs.resources.sat_used;
		if (idx.costs.resources.limit > 0)
			search_stop = idx.costs.resources.used + std::max<int64_t>(0, idx.costs.resources.limit - idx.costs.resources.used) * 3 / 4;
	}
	~InferWorker()
	{
		clear_search();
	}
	void clear_solver()
	{
		solver.reset();
		idx.costs.resources.release(solver_bytes);
		solver_bytes = 0;
	}

	static int64_t occurrences(Cell *cell)
	{
		int64_t result = 0;
		for (const auto &port : cell->connections()) result += GetSize(port.second);
		return result;
	}
	static int64_t model_operations(Cell *cell)
	{
		if (!MuxCostContext::modelled(cell->type)) return 0;
		int64_t count = occurrences(cell), width = GetSize(cell->getPort(ID::Y));
		if (cell->type == ID($mux)) return width;
		if (cell->type == ID($pmux)) return GetSize(cell->getPort(ID::S)) + width * (2 * GetSize(cell->getPort(ID::S)) + 1);
		if (cell->type == ID($lut)) {
			int inputs = GetSize(cell->getPort(ID::A));
			return inputs <= 12 ? (int64_t(1) << inputs) : 0;
		}
		if (cell->type.in(ID($lt), ID($le), ID($gt), ID($ge)))
			return std::max(GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::B))) * 10 + 8;
		if (cell->type.in(ID($eq), ID($ne)))
			return std::max(GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::B))) * 3 + 2;
		if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
			ID($logic_not), ID($logic_and), ID($logic_or))) return count + 4;
		return width * (cell->type.in(ID($andnot), ID($ornot)) ? 2 : 1);
	}
	bool inference_model_units(Cell *cell, int64_t &units) const
	{
		int64_t maximum = idx.costs.resources.memory_limit / 512;
		int64_t count = std::max<int64_t>(1, occurrences(cell));
		units = count + model_operations(cell) * 8;
		int complexity = QuickConeSat::cell_complexity(cell);
		if (!MuxCostContext::modelled(cell->type)) {
			units = 32;
			int dimensions = complexity == 3 ? 2 : complexity == 4 ? 3 : 1;
			for (int dimension = 0; dimension < dimensions; dimension++) {
				if (units > maximum / count) return false;
				units *= count;
			}
		}
		for (const auto &parameter : cell->parameters) {
			if (!parameter.first.in(ID::LUT, ID::TABLE)) continue;
			if (parameter.second.size() > maximum / 8) return false;
			units += parameter.second.size() * 8;
			if (units > maximum) return false;
		}
		return units <= maximum;
	}
	// 证明资格：类型与真值表可建模，组合环、别名冲突与静态未知输入保持边界。
	bool proof_supported(Cell *cell) const
	{
		if (cell == nullptr) return false;
		bool supported = MuxCostContext::modelled(cell->type) || cell->type.in(ID($_AND_), ID($_OR_), ID($_XOR_), ID($_XNOR_),
			ID($_NOT_), ID($_BUF_), ID($_NAND_), ID($_NOR_), ID($_ANDNOT_), ID($_ORNOT_), ID($_MUX_));
		if (!supported || has_undef_input(cell) || idx.costs.cyclic.count(cell->name) ||
			(idx.costs.cells.count(cell->name) && idx.costs.cells.at(cell->name).result == MuxResources::AliasConflict)) return false;
		for (const auto &port : cell->connections())
			if (muxledger_port_output(idx.costs.types, cell, port.first))
				for (SigBit bit : sigmap(port.second))
					if (!bit.wire || idx.costs.unique_driver(bit) != cell) return false;
		return cell->type != ID($lut) || GetSize(cell->getPort(ID::A)) <= 12;
	}
	// 预登记集合内的单元作为证明支持，集合之外的证据单元只作为观察边界。
	bool registered_support(Cell *cell) const
	{
		return cell != nullptr && idx.registered.count(cell->name);
	}
	void clear_search()
	{
		clear_solver(); cone_cache = dict<SigBit, Cone>(); inference_cache = decltype(inference_cache)();
		idx.costs.resources.release(cone_bytes + inference_bytes);
		cone_bytes = 0; inference_bytes = 0;
	}

	// 原始受限cone：只沿真实组合驱动展开，不依赖预登记资格，作为登记引导阶段使用。
	// 返回false表示真实资源中止；depth自然完成或max_cells有界支持边界返回true。
	bool raw_cone(SigBit bit, Cone &c)
	{
		std::vector<SigBit> frontier = {bit};
		c.bits.insert(bit);
		for (int depth = 0; depth < max_depth && !frontier.empty(); depth++) {
			std::vector<SigBit> next;
			for (SigBit current : frontier) {
				if (!idx.costs.resources.can_spend(1))
					return false;
				log_assert(idx.costs.resources.charge(1));
				auto driver = idx.driver.find(current);
				if (driver == idx.driver.end())
					continue;
				Cell *cell = driver->second;
				if (!idx.costs.combinational.cell_known(cell->type) || c.cells.count(cell) || !proof_supported(cell))
					continue;
				if (GetSize(c.cells) >= max_cells)
					return true;
				// 只有真实新登记才收取登记费用。
				if (!idx.registered.count(cell->name)) {
					if (!idx.costs.resources.can_spend(8 + occurrences(cell)))
						return false;
					log_assert(idx.costs.resources.charge(8 + occurrences(cell), MuxResources::Candidates));
					idx.registered.insert(cell->name);
				}
				c.cells.insert(cell);
				for (const auto &port : cell->connections()) {
					bool output = muxledger_port_output(idx.costs.types, cell, port.first);
					for (SigBit input : sigmap(port.second)) {
						if (!idx.costs.resources.can_spend(1))
							return false;
						log_assert(idx.costs.resources.charge(1));
						if (!input.wire || c.bits.count(input))
							continue;
						c.bits.insert(input);
						if (!output)
							next.push_back(input);
					}
				}
			}
			frontier.swap(next);
			if (idx.costs.resources.exhausted)
				return false;
		}
		return true;
	}

	// 从根沿真实父子关系收集本根的全部修改单元，建立按名称与端口位置的真实端口计划。
	// 计划覆盖整棵树（单元与端口出现位置各自有界），批次再从计划中取有限窗口。
	bool build_plan(Cell *root, MuxPortPlan &built)
	{
		MuxPortPlan result;
		result.generation = idx.costs.generation;
		std::vector<Cell *> todo = {root};
		int64_t occurrences_total = 0;
		for (int i = 0; i < GetSize(todo); i++) {
			Cell *cell = todo[i];
			if (!idx.costs.resources.can_spend(1)) {
				batch_result = MuxResources::CommitReservationLimit;
				return false;
			}
			log_assert(idx.costs.resources.charge(1, MuxResources::Candidates));
			if (result.cells.count(cell->name) || !proof_supported(cell))
				continue;
			int64_t count = occurrences(cell);
			if (count > 4096 - occurrences_total)
				continue;
			result.cells.insert(cell->name);
			occurrences_total += count;
			for (int side = 0; side < mux_port_count(cell); side++) {
				auto children = idx.children.find({cell, side});
				if (children == idx.children.end())
					continue;
				for (Cell *child : children->second) {
					if (GetSize(todo) >= 4096)
						break;
					if (!plan_workspace->reserve(128)) {
						batch_result = MuxResources::WorkspaceLimit;
						return false;
					}
					todo.push_back(child);
				}
			}
		}
		std::vector<IdString> names(result.cells.begin(), result.cells.end());
		std::sort(names.begin(), names.end());
		for (IdString name : names) {
			Cell *cell = idx.module->cell(name);
			if (cell == nullptr)
				continue;
			for (int side = 0; side < mux_port_count(cell); side++) {
				IdString data_port = side == 0 ? ID::A : ID::B;
				int base = (cell->type == ID($pmux) && side > 0) ? (side - 1) * mux_width(cell) : 0;
				SigSpec data = mux_port_sig(sigmap, cell, side);
				for (int offset = 0; offset < GetSize(data); offset++) {
					MuxPortAtom atom;
					atom.cell = name; atom.port = data_port; atom.offset = base + offset;
					atom.target = data[offset];
					atom.control = false;
					result.add(atom);
				}
				if (side == 0)
					continue;
				SigBit ctrl = mux_port_ctrl(sigmap, cell, side);
				MuxPortAtom atom;
				atom.cell = name; atom.port = ID::S;
				atom.offset = cell->type == ID($mux) ? 0 : side - 1;
				atom.target = ctrl;
				atom.control = true;
				result.add(atom);
			}
		}
		built = std::move(result);
		return !built.atoms.empty();
	}

	// 登记引导：先用原始受限cone登记本窗口目标与原真实控制位的支持，再用登记资格推断。
	bool pre_register(MuxPortPlan &current, const std::vector<IdString> &window)
	{
		// 相同generation、相同window的登记结果直接复用。
		if (registered_valid && registered_generation == idx.costs.generation && registered_window == window)
			return true;
		pool<IdString> window_cells;
		for (IdString name : window)
			window_cells.insert(name);
		// possible_known来自本窗口每个原真实祖先路径的控制位，包含默认分支与各分支控制。
		pool<SigBit> known;
		std::vector<SigBit> targets;
		clear_cone_cache();
		for (IdString name : window_cells) {
			Cell *cell = idx.module->cell(name);
			if (cell == nullptr)
				continue;
			for (int side = 1; side < mux_port_count(cell); side++)
				known.insert(mux_port_ctrl(sigmap, cell, side));
		}
		for (const MuxPortAtom &atom : current.atoms) {
			if (atom.seen || !window_cells.count(atom.cell))
				continue;
			targets.push_back(atom.target);
			if (atom.control)
				known.insert(atom.target);
		}
		// 第一阶段：不依赖预登记资格，登记每个target与possible_known的真实支持单元。
		std::vector<SigBit> walk = targets;
		walk.insert(walk.end(), known.begin(), known.end());
		std::sort(walk.begin(), walk.end());
		walk.erase(std::unique(walk.begin(), walk.end()), walk.end());
		for (SigBit bit : walk) {
			Cone c;
			if (!raw_cone(bit, c)) {
				batch_result = MuxResources::CommitReservationLimit;
				return false;
			}
		}
		// 祖先选择路径整体进入证明支持。
		for (IdString name : current.cells) {
			Cell *cell = idx.module->cell(name);
			for (auto parent = idx.parent.find(cell); parent != idx.parent.end(); parent = idx.parent.find(cell)) {
				cell = parent->second.cell;
				if (idx.registered.insert(cell->name).second) {
					if (!idx.costs.resources.can_spend(8 + occurrences(cell))) {
						batch_result = MuxResources::CommitReservationLimit;
						return false;
					}
					log_assert(idx.costs.resources.charge(8 + occurrences(cell), MuxResources::Candidates));
				}
			}
		}
		clear_cone_cache();
		// 完整walk与祖先登记都成功之后才记录可复用身份。
		registered_valid = true;
		registered_generation = idx.costs.generation;
		registered_window = window;
		log("MUXPREREG module=%s generation=%llu cells=%d registered=%d targets=%d known=%d work=%lld\n",
			log_id(idx.module), (unsigned long long)current.generation, GetSize(current.cells), GetSize(idx.registered),
			GetSize(targets), GetSize(known), (long long)idx.costs.resources.used);
		return true;
	}
	void clear_cone_cache()
	{
		cone_cache = dict<SigBit, Cone>();
		idx.costs.resources.release(cone_bytes);
		cone_bytes = 0;
	}

	// 批次准入：真实端口计划上的一次有限窗口。本批次负责的端口位置为
	// [batch_atom_begin, batch_atom_end)，局部证明集合P由实际改写单元、真实祖先选择路径与登记支持组成。
	bool begin_batch(std::vector<IdString> &candidates, MuxPortPlan &current, MuxWorkspace &batch_workspace,
			int atom_begin, int atom_end)
	{
		log_assert(!batch_reservation && this->batch_workspace == nullptr && data_fix.empty() && sel_fix.empty());
		batch_number++; module_batches++;
		batch_result = MuxResources::Kept;
		batch_cells.clear(); traversal_cells.clear(); proof_cells.clear();
		batch_data_bits = 0; batch_occurrences = 0; search_finished = false; batch_data_pending = false;
		batch_atom_begin = atom_begin; batch_atom_end = atom_end;
		batch_generation = idx.costs.generation;
		plan = &current;
		this->batch_workspace = &batch_workspace;
		if (idx.costs.resources.exhausted) { batch_result = idx.costs.resources.result; return false; }
		if (!batch_workspace.reserve(8192)) { batch_result = MuxResources::WorkspaceLimit; return false; }
		int64_t planned_work = 0;
		for (IdString name : candidates) {
			Cell *cell = idx.module->cell(name);
			if (cell == nullptr || !proof_supported(cell))
				continue;
			// 32个修改单元与4096个端口出现位置是真实执行条件。
			if (GetSize(batch_cells) >= 32 || occurrences(cell) > 4096 - batch_occurrences)
				break;
			if (!batch_workspace.reserve(128)) { batch_result = MuxResources::WorkspaceLimit; return false; }
			batch_cells.insert(name);
			batch_occurrences += occurrences(cell);
			planned_work += 32 + occurrences(cell);
		}
		if (batch_cells.empty())
			return false;
		if (!idx.costs.resources.can_spend(planned_work) || !batch_workspace.reserve(batch_occurrences * 128) ||
				!idx.costs.resources.charge(planned_work, MuxResources::Candidates)) {
			batch_result = idx.costs.resources.exhausted ? idx.costs.resources.result : MuxResources::CommitReservationLimit;
			return false;
		}
		// 局部证明集合P = 实际改写单元 + 真实祖先选择路径 + 登记支持单元。
		traversal_cells = batch_cells;
		for (IdString name : batch_cells) {
			Cell *cell = idx.module->cell(name);
			for (auto parent = idx.parent.find(cell); parent != idx.parent.end(); parent = idx.parent.find(cell)) {
				cell = parent->second.cell;
				if (!traversal_cells.insert(cell->name).second)
					break;
				if (!batch_workspace.reserve(512)) { batch_result = MuxResources::WorkspaceLimit; return false; }
			}
		}
		for (IdString name : idx.registered) {
			Cell *cell = idx.module->cell(name);
			if (cell == nullptr)
				continue;
			if (!traversal_cells.insert(name).second)
				continue;
			if (!batch_workspace.reserve(512)) { batch_result = MuxResources::WorkspaceLimit; return false; }
		}
		for (IdString name : traversal_cells) {
			Cell *cell = idx.module->cell(name);
			if (cell == nullptr || !proof_supported(cell)) {
				proof_cells.clear();
				batch_result = MuxResources::UnsupportedModel;
				return false;
			}
			proof_cells.insert(name);
		}
		// 联合证明的实际规模只取决于P，成本区域不在这里预遍历。
		int64_t sat_ports = 0, imported = 0, pmux_gates = 0, proof_metadata = 0, gate_metadata = 0;
		for (IdString name : proof_cells) {
			Cell *cell = idx.module->cell(name);
			sat_ports += occurrences(cell);
			proof_metadata += MuxCostContext::snapshot_bytes(cell);
			if (cell->type == ID($lut)) sat_ports += model_operations(cell) * 8;
			if (cell->type == ID($pmux)) {
				int64_t width = GetSize(cell->getPort(ID::Y)), select = GetSize(cell->getPort(ID::S));
				int64_t gates = select - 1 + width * (2 * select);
				if (cell->attributes.count(ID::src)) gate_metadata += gates * cell->attributes.at(ID::src).size() * 2;
				pmux_gates += gates; imported += gates; sat_ports += gates * 4;
			} else imported++;
		}
		proof_bytes = 16384 + sat_ports * 1024 + pmux_gates * 4096 + (proof_metadata + gate_metadata) * 2;
		joint_model_work = 1024 + sat_ports * 32;
		joint_copy_work = (proof_metadata + gate_metadata) * 2;
		joint_prop_margin = 1024 + sat_ports * 32;
		// 联合证明SAT额度：两个副本的真实模型导入加有限传播额度，不使用内存字节。
		joint_sat_work = 2 * imported * SatEffortBudget::import_cell_cost +
			std::max<int64_t>(32768, sat_ports * 64) + joint_prop_margin;
		if (!batch_workspace.reserve(proof_bytes + batch_occurrences * 256)) {
			batch_result = MuxResources::WorkspaceLimit; return false;
		}
		log("MUXBATCHRESERVE module=%s batch=%d generation=%llu atoms=%d..%d cells=%d occurrences=%d proof_cells=%d proof_bytes=%lld\n",
			log_id(idx.module), batch_number, (unsigned long long)batch_generation, atom_begin, atom_end,
			GetSize(batch_cells), batch_occurrences, GetSize(proof_cells),
			(long long)proof_bytes);
		return true;
	}

	// 从 bit 向输入方向展开 max_depth 层组合逻辑，得到 bit 的祖先集合。预登记集合内的单元
	// 才进入推断模型，集合之外只是观察边界。
	const Cone &cone(SigBit bit)
	{
		auto root_driver = idx.driver.find(bit);
		if (root_driver != idx.driver.end() && root_driver->second->hasPort(ID::Y) &&
			GetSize(root_driver->second->getPort(ID::Y)) > 0)
			bit = sigmap(root_driver->second->getPort(ID::Y)[0]);
		auto it = cone_cache.find(bit);
		if (it != cone_cache.end())
			return it->second;
		if (cone_bytes > 2 * 1024 * 1024)
			clear_cone_cache();
		Cone c;
		std::vector<SigBit> frontier = {bit};
		int64_t reserved = 256;
		if (!idx.costs.resources.can_reserve(reserved))
			return empty_cone;
		log_assert(idx.costs.resources.reserve(reserved));
		c.bits.insert(bit);
		for (int depth = 0; depth < max_depth && !frontier.empty(); depth++) {
			std::vector<SigBit> next;
			for (auto b : frontier) {
				if (!idx.costs.resources.can_spend(1))
					break;
				log_assert(idx.costs.resources.charge(1));
				auto drv = idx.driver.find(b);
				if (drv == idx.driver.end())
					continue;
				Cell *cell = drv->second;
				if (!idx.costs.combinational.cell_known(cell->type) || !registered_support(cell) || c.cells.count(cell))
					continue;
				if (GetSize(c.cells) >= max_cells)
					break;
				if (!idx.costs.resources.can_reserve(128))
					break;
				log_assert(idx.costs.resources.reserve(128));
				reserved += 128;
				c.cells.insert(cell);
				for (auto &conn : cell->connections()) {
					bool output = cell->output(conn.first);
					for (auto in : sigmap(conn.second)) {
						if (!idx.costs.resources.can_spend(1))
							break;
						log_assert(idx.costs.resources.charge(1));
						if (in.wire && !c.bits.count(in)) {
							if (!idx.costs.resources.can_reserve(128))
								break;
							log_assert(idx.costs.resources.reserve(128));
							reserved += 128;
							c.bits.insert(in);
							if (!output)
								next.push_back(in);
						}
					}
				}
			}
			frontier.swap(next);
			if (idx.costs.resources.exhausted)
				break;
		}
		cone_bytes += reserved;
		return cone_cache[bit] = std::move(c);
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
	int propagate(const pool<Cell *> &cells, dict<SigBit, bool> &values, SigBit target)
	{
		val = &values;
		conflict = false;
		for (int iter = 0; iter < 64; iter++) {
			changed = false;
			for (auto cell : cells) {
				if (!idx.costs.resources.can_spend(32))
					return -1;
				log_assert(idx.costs.resources.charge(32));
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
	bool budget_spent()
	{
		return idx.costs.resources.exhausted || (sat_effort > 0 && sat_spent >= search_sat_share());
	}
	// 搜索阶段只使用真实额度的一部分，其余留给结束预留的联合证明。
	int64_t search_sat_share() const
	{
		if (sat_effort <= 0)
			return 0;
		return sat_effort - (sat_effort - sat_spent) / 4;
	}
	bool solve_with_budget(ezSAT *ez, const std::vector<int> &model_exprs, std::vector<bool> &model_values,
			const std::vector<int> &assumptions)
	{
		solve_budget_abort = false;
		if (budget_spent() || !idx.costs.resources.can_spend(256 + GetSize(assumptions))) {
			solve_budget_abort = true;
			return false;
		}
		log_assert(idx.costs.resources.charge(256 + GetSize(assumptions), MuxResources::SatQuery));
		if (sat_effort > 0) {
			int64_t available = search_sat_share() - sat_spent;
			if (available <= solver_prop_margin) {
				solve_budget_abort = true; batch_result = MuxResources::SatLimit; return false;
			}
			ez->setSolverPropLimit(available - solver_prop_margin);
		}
		bool result = ez->solve(model_exprs, model_values, assumptions);
		sat_spent += ez->getSolverProps();
		idx.costs.resources.sat_used = sat_spent;
		if (sat_effort > 0) {
			log_assert(sat_spent <= sat_effort);
			if (ez->getSolverPropLimitStatus())
				solve_budget_abort = true;
		}
		return result;
	}
	int infer(SigBit target, const dict<SigBit, bool> &known)
	{
		std::vector<std::pair<SigBit, bool>> conditions(known.begin(), known.end());
		std::sort(conditions.begin(), conditions.end());
		auto key = std::make_pair(sigmap(target), conditions);
		auto cached = inference_cache.find(key);
		if (cached != inference_cache.end()) {
			infer_budget_abort = false;
			return cached->second;
		}
		int result = infer_impl(target, known);
		if (infer_budget_abort && batch_result == MuxResources::Kept)
			batch_result = idx.costs.resources.exhausted ? idx.costs.resources.result : MuxResources::SatLimit;
		if (!infer_budget_abort) {
			if (inference_bytes > 1024 * 1024) {
				inference_cache = decltype(inference_cache)();
				idx.costs.resources.release(inference_bytes);
				inference_bytes = 0;
			}
			int64_t bytes = 128 + GetSize(conditions) * 64;
			if (idx.costs.resources.can_reserve(bytes)) {
				log_assert(idx.costs.resources.reserve(bytes));
				inference_bytes += bytes;
				inference_cache[key] = result;
			}
		}
		return result;
	}
	int infer_impl(SigBit target, const dict<SigBit, bool> &known)
	{
		infer_budget_abort = false;
		if (search_stop > 0 && idx.costs.resources.used >= search_stop) {
			search_finished = true;
			batch_result = MuxResources::SearchSliceLimit;
			infer_budget_abort = true;
			return -1;
		}
		if (!idx.costs.resources.can_spend(32 + GetSize(known))) {
			infer_budget_abort = true;
			return -1;
		}
		log_assert(idx.costs.resources.charge(32 + GetSize(known)));
		target = sigmap(target);
		if (!target.wire)
			return target == State::S0 ? 0 : target == State::S1 ? 1 : -1;
		auto kit = known.find(target);
		if (kit != known.end())
			return kit->second;
		if (known.empty())
			return -1;
		const Cone &target_cone = cone(target);
		MuxWorkspace group_workspace(idx.costs.resources);
		if (!group_workspace.reserve(512 + (GetSize(target_cone.bits) + GetSize(target_cone.cells)) * 128)) {
			infer_budget_abort = true;
			return -1;
		}
		pool<SigBit> group_bits = target_cone.bits;
		pool<Cell *> cells = target_cone.cells;
		dict<SigBit, bool> values;
		pool<SigBit> used;
		for (bool grown = true; grown;) {
			grown = false;
			for (auto &it : known) {
				if (!idx.costs.resources.can_spend(1))
					break;
				log_assert(idx.costs.resources.charge(1));
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
					if (!group_bits.count(bit)) {
						if (!group_workspace.reserve(128))
							break;
						group_bits.insert(bit);
					}
				for (auto cell : kc.cells)
					if (!cells.count(cell)) {
						if (!group_workspace.reserve(128))
							break;
						cells.insert(cell);
					}
			}
			if (GetSize(cells) > 4 * max_cells)
				break;
			if (idx.costs.resources.exhausted)
				break;
		}
		if (idx.costs.resources.exhausted) {
			infer_budget_abort = true;
			return -1;
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
		if (budget_spent()) {
			infer_budget_abort = true;
			return -1;
		}
		pool<IdString> names;
		for (Cell *cell : cells) names.insert(cell->name);
		if (!solver || solver->generation != idx.costs.generation || solver->names != names) {
			int64_t occurrences_count = 0, import_units = 0, import_count = 0;
			for (Cell *cell : cells) {
				for (const auto &port : cell->connections())
					occurrences_count += GetSize(port.second);
				if (cell->type != ID($pmux) && !has_undef_input(cell)) {
					int64_t units;
					if (!inference_model_units(cell, units)) {
						infer_budget_abort = true; batch_result = MuxResources::WorkspaceLimit; return -1;
					}
					import_units += units;
					import_count++;
				}
			}
			clear_solver();
			int64_t import_effort = import_count * SatEffortBudget::import_cell_cost;
			if (sat_effort > 0 && import_effort > search_sat_share() - sat_spent) {
				infer_budget_abort = true; batch_result = MuxResources::SatLimit; return -1;
			}
			int64_t bytes = 8192 + occurrences_count * 256 + import_units * 512;
			if (!idx.costs.resources.can_spend(1024 + occurrences_count * 8 + import_units * 8) ||
					!idx.costs.resources.can_reserve(bytes)) {
				infer_budget_abort = true;
				return -1;
			}
			log_assert(idx.costs.resources.charge(1024 + occurrences_count * 8 + import_units * 8, MuxResources::SatModel));
			log_assert(idx.costs.resources.reserve(bytes));
			solver_bytes = bytes;
			solver_prop_margin = 1024 + import_units * 32;
			sat_spent += import_effort;
			idx.costs.resources.sat_used = sat_spent;
			solver.reset(new SolverModel(sigmap, idx.costs.generation));
			solver->names = names;
			// $pmux 在多个选择位同时有效时的取值依赖实现，不导入，输出作为自由变量。
			for (auto cell : cells)
				if (cell->type != ID($pmux) && !has_undef_input(cell))
					solver->satgen.importCell(cell);
		}
		sat_calls++;
		ezSAT *ez = solver->ez.get();
		SatGen &satgen = solver->satgen;
		std::vector<int> assumptions;
		for (auto &it : values) {
			int lit = satgen.importSigSpec(it.first)[0];
			assumptions.push_back(it.second ? lit : ez->NOT(lit));
		}
		int t = satgen.importSigSpec(target)[0];
		std::vector<int> model_exprs;
		std::vector<bool> model_values;
		assumptions.push_back(t);
		bool can_one = solve_with_budget(ez, model_exprs, model_values, assumptions);
		if (solve_budget_abort) {
			infer_budget_abort = true;
			return -1;
		}
		if (!can_one) {
			sat_hits++;
			return 0;
		}
		assumptions.back() = ez->NOT(t);
		bool can_zero = solve_with_budget(ez, model_exprs, model_values, assumptions);
		if (solve_budget_abort) {
			infer_budget_abort = true;
			return -1;
		}
		if (can_zero)
			return -1;
		sat_hits++;
		return 1;
	}

	// 本批次负责的端口位置。
	bool atom_in_batch(int id) const
	{
		return id < 0 || (id >= batch_atom_begin && id < batch_atom_end);
	}

	int infer_control(Cell *cell, SigBit bit, int offset, const dict<SigBit, bool> &known)
	{
		int id = bit.wire && plan != nullptr ? plan->find(cell->name, ID::S, offset) : -1;
		if (!batch_cells.count(cell->name) || !bit.wire || !atom_in_batch(id) ||
			(id >= 0 && plan->atoms[id].seen))
			return -1;
		plan->control_attempts++;
		int value = infer(bit, known);
		plan->atoms[id].seen = true;
		plan->attempts++;
		if (value >= 0) {
			plan->proved++;
			sel_fix[{cell, offset}] = value;
		}
		return value;
	}

	// 数据端口位置的实际检查：64个数据位限额包括失败的实际检查，控制位按端口有界登记。
	bool visit_port(Cell *cell, int index, const dict<SigBit, bool> &known)
	{
		if (search_finished) return true;
		MuxWorkspace port_workspace(idx.costs.resources);
		if (!port_workspace.reserve(512 + mux_width(cell) * 128)) {
			search_finished = true; batch_result = MuxResources::WorkspaceLimit; return false;
		}
		pool<SigBit> child_bits;
		auto cit = idx.children.find({cell, index});
		if (cit != idx.children.end())
			for (auto child : cit->second) {
				for (auto bit : sigmap(child->getPort(ID::Y)))
					child_bits.insert(bit);
				if (!visit(child, known))
					return false;
			}
		if (!infer_data || known.empty() || !batch_cells.count(cell->name))
			return true;
		IdString port = index == 0 ? ID::A : ID::B;
		int base = (cell->type == ID($pmux) && index > 0) ? (index - 1) * mux_width(cell) : 0;
		SigSpec sig = mux_port_sig(sigmap, cell, index);
		for (int i = 0; i < GetSize(sig); i++) {
			if (search_finished) return true;
			SigBit bit = sig[i];
			if (!bit.wire || child_bits.count(bit))
				continue;
			int id = plan == nullptr ? -1 : plan->find(cell->name, port, base + i);
			if (id >= 0 && plan->atoms[id].seen)
				continue;
			// 属于其它子计划的端口位置留给对应子批次，保持真实游标。
			if (!atom_in_batch(id))
				continue;
			if (batch_data_bits >= 64) {
				search_finished = true; batch_data_pending = true;
				batch_result = MuxResources::SearchSliceLimit; return true;
			}
			batch_data_bits++;
			if (id >= 0) {
				plan->atoms[id].seen = true;
				plan->attempts++;
				plan->data_attempts++;
			}
			int v = infer(bit, known);
			if (id >= 0 && v >= 0)
				plan->proved++;
			if (v >= 0)
				data_fix[std::make_tuple(cell, port, base + i)] = v;
		}
		return true;
	}

	bool visit(Cell *cell, const dict<SigBit, bool> &known)
	{
		if (search_finished || !traversal_cells.count(cell->name))
			return true;
		MuxWorkspace path_workspace(idx.costs.resources);
		if (!path_workspace.reserve(512 + (GetSize(known) + GetSize(cell->getPort(ID::S)) + 1) * 128)) {
			search_finished = true; batch_result = MuxResources::WorkspaceLimit; return false;
		}
		if (!idx.costs.resources.can_spend(32 + GetSize(known)))
			return false;
		log_assert(idx.costs.resources.charge(32 + GetSize(known)));
		if (!idx.costs.mutable_cell(cell))
			return true;
		if (cell->type == ID($mux)) {
			SigBit s = sigmap(cell->getPort(ID::S)[0]);
			int v = infer_control(cell, s, 0, known);
			if (v >= 0)
				return visit_port(cell, v, known);
			for (int side = 0; side < 2; side++) {
				dict<SigBit, bool> sub = known;
				if (s.wire)
					sub[s] = side;
				if (!visit_port(cell, side, sub))
					return false;
			}
			return true;
		}
		SigSpec s = sigmap(cell->getPort(ID::S));
		int n = GetSize(s);
		std::vector<int> sv(n);
		for (int i = 0; i < n; i++)
			sv[i] = infer_control(cell, s[i], i, known);
		for (int i = 0; i < n; i++) {
			if (sv[i] == 0)
				continue;
			dict<SigBit, bool> sub = known;
			if (s[i].wire)
				sub[s[i]] = true;
			if (!visit_port(cell, i + 1, sub))
				return false;
		}
		if (!search_finished) {
			bool any_one = false;
			for (int i = 0; i < n; i++)
				if (sv[i] == 1)
					any_one = true;
			if (!any_one) {
				dict<SigBit, bool> sub = known;
				for (int i = 0; i < n; i++)
					if (s[i].wire)
						sub[s[i]] = false;
				if (!visit_port(cell, 0, sub))
					return false;
			}
		}
		return true;
	}

	void log_candidate(int cand, const char *decision, int64_t gain, int64_t removed, int64_t dead, int64_t added, const char *note)
	{
		log("MUXLEDGER pass=opt_muxinfer module=%s cand=%d decision=%s gain=%lld removed=%lld dead=%lld added=%lld note=%s\n",
				log_id(idx.module), cand, decision, (long long)gain, (long long)removed, (long long)dead,
				(long long)added, note);
	}

	// 联合miter复制全部真实旧连接与最终ports替换，比较全部观察输出的差异析取。
	// 最终求解不附加known/path assumptions。
	bool prove_joint(const dict<IdString, dict<IdString, SigSpec>> &ports)
	{
		log_assert(batch_reservation && batch_reservation->finishing && batch_generation == idx.costs.generation);
		MuxWorkspace workspace(idx.costs.resources);
		log_assert(workspace.reserve(proof_bytes));
		log_assert(idx.costs.resources.charge(joint_copy_work, MuxResources::SatModel));
		Design proof_design;
		Module *old_module = proof_design.addModule(ID(muxinfer_old));
		Module *new_module = proof_design.addModule(ID(muxinfer_new));
		ezSatPtr ez;
		SatGen old_sat(ez.get(), &sigmap, "muxinfer_old:"), new_sat(ez.get(), &sigmap, "muxinfer_new:");
		pool<SigBit> driven, inputs, observed;
		int64_t imported = 0, model_ports = 0;
		for (IdString name : proof_cells) {
			Cell *cell = idx.module->cell(name);
			log_assert(cell != nullptr && proof_supported(cell));
			for (const auto &port : cell->connections())
				if (muxledger_port_output(idx.costs.types, cell, port.first))
					for (SigBit bit : sigmap(port.second))
						driven.insert(bit);
		}
		for (IdString name : proof_cells) {
			Cell *cell = idx.module->cell(name);
			for (const auto &port : cell->connections()) {
				if (muxledger_port_input(idx.costs.types, cell, port.first))
					for (SigBit bit : sigmap(port.second)) if (bit.wire && !driven.count(bit)) inputs.insert(bit);
				if (!muxledger_port_output(idx.costs.types, cell, port.first)) continue;
				for (SigBit bit : sigmap(port.second)) {
					if (idx.costs.output_bits.count(bit) || idx.costs.protected_bits.count(bit)) observed.insert(bit);
					auto users = idx.costs.users.find(bit);
					if (users != idx.costs.users.end())
						for (const auto &user : users->second) if (!proof_cells.count(user.cell)) observed.insert(bit);
				}
			}
			auto copy = [&](Module *destination, bool replacement) {
				Cell *copy = destination->addCell(cell->name, cell->type);
				copy->parameters = cell->parameters; copy->attributes = cell->attributes;
				const auto &connections = replacement && ports.count(name) ? ports.at(name) : cell->connections();
				for (const auto &port : connections) copy->setPort(port.first, port.second);
				if (copy->type == ID($pmux)) { simplemap(destination, copy); destination->remove(copy); }
			};
			copy(old_module, false); copy(new_module, true);
		}
		for (Cell *cell : old_module->cells()) { log_assert(old_sat.importCell(cell)); imported++; model_ports += occurrences(cell); }
		for (Cell *cell : new_module->cells()) { log_assert(new_sat.importCell(cell)); imported++; model_ports += occurrences(cell); }
		int64_t import_effort = imported * SatEffortBudget::import_cell_cost;
		log_assert(import_effort <= batch_reservation->sat);
		batch_reservation->sat -= import_effort;
		sat_spent += import_effort;
		idx.costs.resources.sat_used = sat_spent;
		for (SigBit bit : inputs) ez->SET(old_sat.importSigSpec(bit)[0], new_sat.importSigSpec(bit)[0]);
		std::vector<int> differences;
		for (SigBit bit : observed)
			differences.push_back(ez->XOR(old_sat.importSigSpec(bit)[0], new_sat.importSigSpec(bit)[0]));
		int difference = ez->expression(ezSAT::OpOr, differences);
		log_assert(idx.costs.resources.charge(joint_model_work, MuxResources::SatModel));
		log_assert(idx.costs.resources.charge(256 + GetSize(observed), MuxResources::SatQuery));
		int64_t margin = joint_prop_margin;
		if (sat_effort > 0 && batch_reservation->sat <= margin) { batch_result = MuxResources::SatLimit; return false; }
		ez->setSolverPropLimit(sat_effort > 0 ? batch_reservation->sat - margin : 0);
		joint_calls++;
		bool different = ez->solve(difference);
		if (sat_effort > 0) {
			log_assert(ez->getSolverProps() <= batch_reservation->sat);
			batch_reservation->sat -= ez->getSolverProps();
			sat_spent += ez->getSolverProps(); idx.costs.resources.sat_used = sat_spent;
			log_assert(sat_spent <= sat_effort);
		} else { sat_spent += ez->getSolverProps(); idx.costs.resources.sat_used = sat_spent; }
		bool proved = !different && !ez->getSolverPropLimitStatus();
		if (proved) joint_proved++;
		else batch_result = ez->getSolverPropLimitStatus() ? MuxResources::SatLimit : MuxResources::UnsupportedModel;
		log("MUXJOINTPROOF module=%s batch=%d cells=%d inputs=%d observations=%d imports=%lld ports=%lld result=%s sat_work=%lld\n",
			log_id(idx.module), batch_number, GetSize(proof_cells), GetSize(inputs), GetSize(observed),
			(long long)imported, (long long)model_ports, proved ? "Unsat" : different ? "Sat" : "LimitReached",
			(long long)(import_effort + ez->getSolverProps()));
		return proved;
	}

	// 结束预留：联合证明、实际commit索引、原地回收、idx.rebuild与候选释放的共同峰值。
	int64_t finish_work_estimate(MuxLedger &ledger)
	{
		int64_t commit_work = 4096;
		for (const auto &entry : ledger.prepared)
			commit_work += 64 + (GetSize(entry.second.dependencies) + GetSize(entry.second.outputs)) * 32;
		for (const auto &entry : ledger.joint_ports)
			for (const auto &port : entry.second)
				commit_work += 16 + GetSize(port.second) * 16;
		return commit_work + joint_model_work + joint_copy_work +
			idx.costs.reclaim_work() + idx.costs.index_work();
	}
	int64_t finish_bytes_estimate(MuxLedger &ledger)
	{
		int64_t result = proof_bytes + 32768;
		for (const auto &entry : ledger.prepared)
			result += 256 + GetSize(entry.second.outputs) * 16 + GetSize(entry.second.dependencies) * 16;
		return result + idx.costs.reclaim_bytes() + 65536;
	}

	bool apply_ports(int64_t &reserved, int64_t &consumed)
	{
		log_assert(batch_generation == idx.costs.generation);
		dict<IdString, dict<IdString, SigSpec>> ports;
		for (const auto &entry : data_fix) {
			Cell *cell = std::get<0>(entry.first);
			log_assert(batch_cells.count(cell->name));
			if (!ports.count(cell->name)) ports[cell->name] = cell->connections();
			ports.at(cell->name).at(std::get<1>(entry.first))[std::get<2>(entry.first)] = entry.second ? State::S1 : State::S0;
		}
		for (const auto &entry : sel_fix) {
			Cell *cell = entry.first.first;
			log_assert(batch_cells.count(cell->name));
			if (!ports.count(cell->name)) ports[cell->name] = cell->connections();
			ports.at(cell->name).at(ID::S)[entry.first.second] = entry.second ? State::S1 : State::S0;
		}
		MuxLedger ledger(idx.costs);
		auto report = [&](const char *decision) {
			log_candidate(batch_number, decision, ledger.gain, ledger.removed_gain, ledger.dead_result,
				ledger.added_cost, MuxResources::result_name(batch_result));
		};
		ledger.replace_joint(ports);
		if (!ledger.settle()) {
			batch_result = ledger.result != MuxResources::Kept ? ledger.result : MuxResources::WorkspaceLimit;
			report("reject");
			return false;
		}
		// prepared确定之后预留联合证明、提交、回收与索引重建费用。
		int64_t finish_work = finish_work_estimate(ledger);
		int64_t finish_bytes = finish_bytes_estimate(ledger);
		batch_reservation.reset(new MuxBatchReservation(idx.costs.resources));
		if (!batch_reservation->reserve(finish_work, finish_bytes, joint_sat_work)) {
			batch_result = idx.costs.resources.result;
			batch_reservation.reset();
			report("reject");
			return false;
		}
		reserved = finish_work;
		batch_reservation->begin();
		bool accepted = false;
		// 提交需要的索引工作在修改Module之前已经进入预留。
		bool commit_ready = idx.costs.resources.can_spend(idx.costs.index_work());
		if (prove_joint(ports)) {
			ledger.joint_proof_complete = true;
			bool enough = force || (sel_fix.empty() ? ledger.gain >= 0 : ledger.gain > 0);
			if (enough && !dry_run && !commit_ready) {
				batch_result = MuxResources::CommitReservationLimit;
				report("reject");
			} else {
				batch_result = enough ? MuxResources::Kept : MuxResources::NoGain;
				report(enough ? force ? "forced" : "accept" : "reject");
				if (enough) {
					rewrites += GetSize(ports); removed_cells += GetSize(ledger.dead);
					if (!dry_run) {
						int64_t before = idx.costs.resources.used;
						ledger.commit_joint();
						log_assert(idx.costs.resources.charge(idx.costs.index_work(), MuxResources::Index));
						idx.rebuild();
						batches_committed++; accepted = true;
						log("MUXBATCHCOMMIT module=%s batch=%d cells=%d data_bits=%d control_bits=%d work=%lld generation=%llu\n",
							log_id(idx.module), batch_number, GetSize(ports), GetSize(data_fix), GetSize(sel_fix),
							(long long)(idx.costs.resources.used - before), (unsigned long long)idx.costs.generation);
					}
				}
			}
		} else {
			log_candidate(batch_number, "reject", 0, 0, 0, 0, MuxResources::result_name(batch_result));
		}
		consumed = reserved - batch_reservation->work;
		finish_reserved += reserved;
		finish_consumed += consumed;
		batch_reservation->end();
		return accepted;
	}

	bool apply(MuxPortPlan &current, int attempts_before, int data_before, int control_before)
	{
		clear_search();
		int batch_attempts = plan != nullptr ? plan->attempts - attempts_before : 0;
		int64_t reserved = 0, consumed = 0;
		MuxResources::Result search_result = batch_result;
		bool accepted = (!data_fix.empty() || !sel_fix.empty()) && apply_ports(reserved, consumed);
		if (batch_result != MuxResources::Kept) result_counts[batch_result]++;
		if (search_result != MuxResources::Kept && search_result != batch_result) result_counts[search_result]++;
		log("MUXBATCHEND module=%s batch=%d attempted_ports=%d data_attempts=%d control_attempts=%d data_attempt_bits=%d committed=%d finish_reserved=%lld finish_consumed=%lld result=%s search_result=%s work=%lld peak=%lld\n",
			log_id(idx.module), batch_number, batch_attempts,
			current.data_attempts - data_before, current.control_attempts - control_before,
			batch_data_bits, accepted,
			(long long)reserved, (long long)consumed,
			MuxResources::result_name(batch_result), MuxResources::result_name(search_result),
			(long long)idx.costs.resources.used, (long long)idx.costs.resources.peak_bytes);
		cleanup_batch();
		return accepted;
	}

	// 批次不能准入时按真实端口位置二分拆分；每个子批次重新检查资格、支持、资源与完整联合证明。
	bool subrun(IdString root_name, MuxPortPlan &current, std::vector<IdString> subset,
			int atom_begin, int atom_end, int depth)
	{
		if (subset.empty() || atom_begin >= atom_end)
			return false;
		MuxWorkspace batch_workspace(idx.costs.resources);
		// 本轮批次的真实起点，嵌套分裂的子批次不会覆盖外层的增量基准。
		int attempts_before = current.attempts, data_before = current.data_attempts, control_before = current.control_attempts;
		bool ready = begin_batch(subset, current, batch_workspace, atom_begin, atom_end);
		if (!ready) {
			MuxResources::Result failure = batch_result;
			// 先完成失败作用域清理，再处理子计划。
			cleanup_batch();
			bool admission_failure = failure == MuxResources::WorkspaceLimit ||
				failure == MuxResources::CommitReservationLimit || failure == MuxResources::TotalWorkLimit ||
				failure == MuxResources::SatLimit;
			if (admission_failure && !idx.costs.resources.exhausted && depth < 8) {
				if (atom_end - atom_begin > 1) {
					int middle = atom_begin + (atom_end - atom_begin) / 2;
					splits++;
					log("MUXSPLIT module=%s root=%s depth=%d atoms=%d..%d first=%d..%d second=%d..%d reason=%s work=%lld live=%lld\n",
						log_id(idx.module), log_id(root_name), depth, atom_begin, atom_end, atom_begin, middle, middle, atom_end,
						MuxResources::result_name(failure), (long long)idx.costs.resources.used,
						(long long)idx.costs.resources.live_bytes);
					if (subrun(root_name, current, subset, middle, atom_end, depth + 1))
						return true;
					if (idx.costs.resources.exhausted)
						return false;
					return subrun(root_name, current, subset, atom_begin, middle, depth + 1);
				}
				if (subset.size() > 1) {
					std::vector<IdString> first(subset.begin(), subset.begin() + subset.size() / 2);
					std::vector<IdString> second(subset.begin() + subset.size() / 2, subset.end());
					splits++;
					log("MUXSPLIT module=%s root=%s depth=%d cells=%d first=%d second=%d reason=%s work=%lld live=%lld\n",
						log_id(idx.module), log_id(root_name), depth, GetSize(subset), GetSize(first), GetSize(second),
						MuxResources::result_name(failure), (long long)idx.costs.resources.used,
						(long long)idx.costs.resources.live_bytes);
					if (subrun(root_name, current, second, atom_begin, atom_end, depth + 1))
						return true;
					if (idx.costs.resources.exhausted)
						return false;
					return subrun(root_name, current, first, atom_begin, atom_end, depth + 1);
				}
			}
			return false;
		}
		Cell *live_root = idx.module->cell(root_name);
		if (live_root != nullptr)
			visit(live_root, {});
		// 本批次范围内还有未检查的位置时保留单元，下一轮按真实游标继续。
		if (!batch_data_pending && plan != nullptr) {
			for (int id = atom_begin; id < atom_end && id < GetSize(plan->atoms); id++) {
				const MuxPortAtom &atom = plan->atoms[id];
				if (batch_cells.count(atom.cell) && !atom.seen) {
					batch_data_pending = true;
					break;
				}
			}
		}
		bool committed = apply(current, attempts_before, data_before, control_before);
		if (committed || !batch_data_pending) {
			// 只移除本代真正检查完成的单元，未检查的端口位置保留游标。
			pool<IdString> incomplete;
			for (const MuxPortAtom &atom : current.atoms)
				if (!atom.seen)
					incomplete.insert(atom.cell);
			for (IdString cell : subset)
				if (!incomplete.count(cell))
					current.cells.erase(cell);
		}
		return committed;
	}
	// 失败出口统一清理批次作用域，避免残留预留或悬空地址。
	void cleanup_batch()
	{
		batch_reservation.reset();
		plan = nullptr;
		batch_workspace = nullptr;
		data_fix.clear(); sel_fix.clear();
		batch_cells.clear(); traversal_cells.clear(); proof_cells.clear();
	}

	void run()
	{
		std::vector<IdString> roots;
		for (Cell *root : idx.roots) roots.push_back(root->name);
		std::sort(roots.begin(), roots.end());
		for (IdString name : roots) {
			if (idx.costs.resources.exhausted)
				break;
			if (module_batches >= 8 * std::max<int>(1, GetSize(roots)))
				break;
			Cell *root = idx.module->cell(name);
			if (root == nullptr || !idx.costs.mutable_cell(root))
				continue;
			clear_search();
			idx.registered.clear();
			registered_valid = false;
			MuxPortPlan current;
			{
				MuxWorkspace build_workspace(idx.costs.resources);
				plan_workspace = &build_workspace;
				bool built = build_plan(root, current);
				plan_workspace = nullptr;
				if (!built)
					continue;
			}
			if (current.cells.empty()) {
				idx.registered.clear();
				continue;
			}
			log("MUXPLAN module=%s root=%s generation=%llu data_pending=%d control_pending=%d cells=%d registered=%d atoms=%d\n",
				log_id(idx.module), log_id(name), (unsigned long long)current.generation,
				current.data_pending, current.control_pending, GetSize(current.cells), GetSize(idx.registered),
				GetSize(current.atoms));
			int quota = 0;
			for (int iteration = 0; iteration < 8; iteration++) {
				// 每次批次按名字取得当前根，并按当前网络重建计划与游标。
				Cell *live_root = idx.module->cell(name);
				if (live_root == nullptr || !idx.costs.mutable_cell(live_root))
					break;
				std::vector<IdString> candidates(current.cells.begin(), current.cells.end());
				std::sort(candidates.begin(), candidates.end());
				if (candidates.empty())
					break;
				// 一个批次最多32个修改单元。
				if (candidates.size() > 32)
					candidates.resize(32);
				// iteration=0使用根入口已构造的current；generation未变直接复用seen与pending cells。
				if (current.generation != idx.costs.generation) {
					// 真实提交改变generation：移动保存原pending cells，重建后恢复其语义。
					pool<IdString> pending_cells = std::move(current.cells);
					MuxWorkspace build_workspace(idx.costs.resources);
					plan_workspace = &build_workspace;
					bool built = build_plan(live_root, current);
					plan_workspace = nullptr;
					if (!built)
						break;
					current.cells = std::move(pending_cells);
				}
				if (!pre_register(current, candidates))
					break;
				// 本轮的attempts/proved使用真实增量，根累计值不重复累计。
				int attempts_before = current.attempts, proved_before = current.proved;
				int data_attempts_before = current.data_attempts, control_attempts_before = current.control_attempts;
				bool committed = subrun(name, current, candidates, 0, GetSize(current.atoms), 0);
				int round_attempts = current.attempts - attempts_before;
				int round_proved = current.proved - proved_before;
				root_data_attempts += current.data_attempts - data_attempts_before;
				root_control_attempts += current.control_attempts - control_attempts_before;
				if (committed)
					quota++;
				// 每轮结束过滤失效单元：不存在或不再proof_supported的单元删除。
				for (IdString removed : std::vector<IdString>(current.cells.begin(), current.cells.end())) {
					Cell *cell = idx.module->cell(removed);
					if (!proof_supported(cell))
						current.cells.erase(removed);
				}
				log("MUXROOT module=%s root=%s iteration=%d attempts=%d proved=%d pending=%d module_batches=%d splits=%d committed=%d\n",
					log_id(idx.module), log_id(name), iteration, round_attempts,
					round_proved, GetSize(current.cells), module_batches, splits, committed);
				// 整轮没有实际尝试且没有提交：本根没有可做的位置，结束不变搜索。
				if (!committed && round_attempts == 0)
					break;
				if (idx.costs.resources.exhausted)
					break;
				if (quota >= 8) {
					root_limit_stops++;
					break;
				}
				if (current.atoms.empty() || current.cells.empty())
					break;
				if (!committed && !batch_data_pending)
					break;
			}
			idx.registered.clear();
			roots_done++;
		}
		log("MUXPORTSTATS module=%s batches=%d batches_committed=%d splits=%d roots=%d data_attempts=%d control_attempts=%d root_limit_stops=%d finish_reserved=%lld finish_consumed=%lld\n",
			log_id(idx.module), batch_number, batches_committed, splits, roots_done, root_data_attempts,
			root_control_attempts, root_limit_stops, (long long)finish_reserved, (long long)finish_consumed);
		log("MUXBATCHSTATS module=%s batches=%d joint_calls=%d joint_proved=%d commits=%d UnsupportedModel=%d AliasConflict=%d WorkspaceLimit=%d SearchSliceLimit=%d CommitReservationLimit=%d TotalWorkLimit=%d SatLimit=%d NoGain=%d\n",
			log_id(idx.module), batch_number, joint_calls, joint_proved, batches_committed, result_counts[MuxResources::UnsupportedModel],
			result_counts[MuxResources::AliasConflict], result_counts[MuxResources::WorkspaceLimit], result_counts[MuxResources::SearchSliceLimit],
			result_counts[MuxResources::CommitReservationLimit], result_counts[MuxResources::TotalWorkLimit], result_counts[MuxResources::SatLimit], result_counts[MuxResources::NoGain]);
	}
};

struct OptMuxInferPass : public Pass {
	OptMuxInferPass() : Pass("opt_muxinfer", "remove muxtree redundancy implied by path conditions") { }
	void help() override
	{
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
		log("user. Proven data-port constant propagation is applied when it changes the\n");
		log("mapped port signals and adds no logic (predicted gain >= 0). Control-port and\n");
		log("structural rewrites require positive predicted gain. Each candidate is\n");
		log("reported on a line starting with \"MUXLEDGER\".\n");
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
		log("the scratchpad key opt_muxinfer.sat_effort (default min(2000000,\n");
		log("100000 + port occurrences * 256), 0 means\n");
		log("unlimited). Once the budget is used up no further SAT call is made and the\n");
		log("remaining candidates are left unproven.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int max_depth = 6, max_cells = 64, max_inputs = 64;
		bool infer_data = true;
		bool dry_run = false, force = false;

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

		if (dry_run)
			force = false;

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			MuxTreeIndex idx(module);
			if (!idx.costs.type_scan([](const Cell *cell) { return cell->type.in(ID($mux), ID($pmux)); }, 1, "muxinfer"))
				continue;
			idx.costs.refresh();
			idx.rebuild();
			InferWorker worker(idx, max_depth, max_cells, max_inputs, infer_data, dry_run, force);
			worker.run();

			std::string effort;
			if (worker.sat_effort > 0)
				effort = stringf("sat effort %lld of %lld left", (long long)std::max<int64_t>(worker.sat_effort - worker.sat_spent, 0),
						(long long)worker.sat_effort);
			else
				effort = "sat effort unlimited";
			log("  %s: %d rewrites, ledger predicted %d removed cells, %d rule hits, %d sat hits, %d sat calls, %s.\n",
					log_id(module), worker.rewrites, worker.removed_cells,
					worker.rule_hits, worker.sat_hits, worker.sat_calls, effort.c_str());
		}
	}
} OptMuxInferPass;

PRIVATE_NAMESPACE_END
