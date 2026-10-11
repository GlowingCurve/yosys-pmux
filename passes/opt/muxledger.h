#ifndef MUXLEDGER_H
#define MUXLEDGER_H

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

#include <array>
#include <algorithm>
#include <functional>
#include <unordered_map>

YOSYS_NAMESPACE_BEGIN

inline dict<int, dict<std::string, int64_t>> &mux_shared_work()
{
	static dict<int, dict<std::string, int64_t>> scopes;
	return scopes;
}

// 模块内的真实工作、容量与SAT累计，同一个scope与key只存在一个账户。
struct MuxResources
{
	enum Result { Kept, UnsupportedModel, AliasConflict, WorkspaceLimit, SearchSliceLimit,
		CommitReservationLimit, TotalWorkLimit, SatLimit, NoGain };
	static const char *result_name(Result result)
	{
		static const char *names[] = {"Kept", "UnsupportedModel", "AliasConflict", "WorkspaceLimit", "SearchSliceLimit",
			"CommitReservationLimit", "TotalWorkLimit", "SatLimit", "NoGain"};
		return names[result];
	}
	Result result = Kept;
	Module *module;
	std::string key;
	int64_t used = 0, limit = 0;
	int64_t live_bytes = 0, peak_bytes = 0;
	int64_t memory_limit = 16 * 1024 * 1024;
	bool exhausted = false;
	int scope = 0;
	enum Phase { Functions, Index, Dependencies, Candidates, SatModel, SatQuery, Commit, Reclaim, PhaseCount };
	int64_t phase_work[PhaseCount] = {};
	int64_t commit_reserved = 0;
	int64_t restore_reserved = 0;
	int64_t batch_reserved = 0;
	int64_t *finish_work = nullptr, *finish_bytes = nullptr;
	int64_t sat_used = 0, sat_limit = 0;
	MuxResources(Module *module) : module(module), key("muxledger.work." + module->name.str())
	{
		int64_t occurrences = 0, inspection = 0;
		for (Wire *wire : module->wires())
			inspection += 4 + wire->width * 2 + GetSize(wire->attributes) * 8;
		for (Cell *cell : module->cells()) {
			for (const auto &port : cell->connections()) {
				occurrences += GetSize(port.second);
				inspection += 4 + GetSize(port.second) * 2;
			}
			inspection += 16 + (GetSize(cell->parameters) + GetSize(cell->attributes)) * 8;
		}
		limit = module->design->scratchpad_get_int("muxledger.work_limit", std::min<int64_t>(8000000, 262144 + occurrences * 512));
		memory_limit = module->design->scratchpad_get_int("muxledger.workspace_bytes", memory_limit);
		sat_limit = module->design->scratchpad_get_int("opt_muxinfer.sat_effort", std::min<int64_t>(2000000, 100000 + occurrences * 256));
		log_assert(limit >= 0 && memory_limit > 0 && sat_limit >= 0);
		scope = module->design->scratchpad_get_int("muxledger.scope", 0);
		if (scope) {
			log_assert(mux_shared_work().count(scope));
			auto &shared = mux_shared_work().at(scope);
			used = shared.at(key, 0);
			sat_used = shared.at(key + ".sat_used", 0);
			if (shared.count(key + ".limit"))
				limit = shared.at(key + ".limit");
			else
				shared[key + ".limit"] = limit;
		}
		// 校准遍历的真实费用先核查再累计。
		if (!can_spend(inspection)) {
			exhausted = true;
			result = TotalWorkLimit;
		} else {
			log_assert(charge(inspection, Index));
		}
	}
	~MuxResources()
	{
		if (scope) {
			mux_shared_work().at(scope)[key] = used;
			mux_shared_work().at(scope)[key + ".sat_used"] = sat_used;
		}
		log_assert(batch_reserved == 0 && finish_work == nullptr && finish_bytes == nullptr);
		log("MUXRESOURCES module=%s work=%lld limit=%lld workspace_peak=%lld workspace_limit=%lld exhausted=%d\n",
			log_id(module), (long long)used, (long long)limit, (long long)peak_bytes,
			(long long)memory_limit, exhausted);
		log("MUXRESOURCES phases functions=%lld index=%lld dependencies=%lld candidates=%lld sat_model=%lld sat_query=%lld commit=%lld reclaim=%lld sat_work=%lld sat_limit=%lld\n",
			(long long)phase_work[Functions], (long long)phase_work[Index], (long long)phase_work[Dependencies],
			(long long)phase_work[Candidates], (long long)phase_work[SatModel], (long long)phase_work[SatQuery],
			(long long)phase_work[Commit], (long long)phase_work[Reclaim], (long long)sat_used, (long long)sat_limit);
	}
	// 预检查与charge的消费顺序一致：先处理finish预留窗口，再判断耗尽，最后按可用余额。
	bool can_spend(int64_t work) const
	{
		log_assert(work >= 0);
		if (finish_work != nullptr)
			return work <= *finish_work;
		if (exhausted) return false;
		if (limit <= 0) return true;
		return work <= limit - used - commit_reserved - restore_reserved - batch_reserved;
	}
	// 预检查与reserve的消费顺序一致：先处理finish预留窗口，再判断耗尽，最后按容量余额。
	bool can_reserve(int64_t bytes) const
	{
		log_assert(bytes >= 0);
		if (finish_bytes != nullptr)
			return bytes <= *finish_bytes;
		if (exhausted) return false;
		return bytes <= memory_limit - live_bytes;
	}
	bool can_query(int64_t sat) const
	{
		log_assert(sat >= 0);
		return sat == 0 || sat_limit <= 0 || sat <= sat_limit - sat_used;
	}
	// 局部增长只记录峰值与核查，不改变live_bytes，也不设置全局exhausted。
	bool approve_peak(int64_t additional)
	{
		log_assert(additional >= 0);
		if (!can_reserve(additional))
			return false;
		if (finish_bytes == nullptr)
			peak_bytes = std::max(peak_bytes, live_bytes + additional);
		return true;
	}
	void charge_finish(int64_t work, Phase phase)
	{
		log_assert(work <= *finish_work && work <= batch_reserved);
		*finish_work -= work;
		batch_reserved -= work;
		used += work;
		phase_work[phase] += work;
		log_assert(limit == 0 || used <= limit);
	}
	bool charge(int64_t work, Phase phase = Functions)
	{
		log_assert(work >= 0);
		if (finish_work != nullptr) {
			charge_finish(work, phase);
			return true;
		}
		if (exhausted) return false;
		if (limit > 0 && work > limit - used - commit_reserved - restore_reserved - batch_reserved) {
			exhausted = true;
			result = TotalWorkLimit;
			return false;
		}
		used += work;
		phase_work[phase] += work;
		return true;
	}
	void account(int64_t work, Phase phase)
	{
		log_assert(work >= 0);
		if (finish_work != nullptr) {
			charge_finish(work, phase);
			return;
		}
		if (phase == Commit) {
			log_assert(work <= commit_reserved);
			commit_reserved -= work;
		}
		used += work;
		phase_work[phase] += work;
		log_assert(limit == 0 || used <= limit);
		if (limit > 0 && used >= limit)
			exhausted = true;
	}
	bool reserve_commit(int64_t work)
	{
		log_assert(work >= 0 && commit_reserved == 0);
		if (exhausted || (limit > 0 && work > limit - used - restore_reserved - batch_reserved)) {
			result = CommitReservationLimit;
			return false;
		}
		commit_reserved = work;
		return true;
	}
	bool reserve(int64_t bytes)
	{
		log_assert(bytes >= 0);
		if (finish_bytes != nullptr) {
			log_assert(bytes <= *finish_bytes);
			*finish_bytes -= bytes;
			return true;
		}
		if (exhausted) return false;
		if (bytes > memory_limit - live_bytes) {
			exhausted = true;
			result = WorkspaceLimit;
			return false;
		}
		live_bytes += bytes;
		peak_bytes = std::max(peak_bytes, live_bytes);
		return true;
	}
	// 已经批准的容量增长：提交live_bytes与峰值。
	void commit_growth(int64_t bytes)
	{
		log_assert(bytes >= 0);
		if (finish_bytes != nullptr) {
			log_assert(bytes <= *finish_bytes);
			*finish_bytes -= bytes;
		}
		live_bytes += bytes;
		peak_bytes = std::max(peak_bytes, live_bytes);
		log_assert(live_bytes <= memory_limit);
	}
	void release(int64_t bytes)
	{
		log_assert(bytes >= 0 && bytes <= live_bytes);
		live_bytes -= bytes;
	}
};

// 结束预留：联合证明与实际提交期间的一次性额度。
struct MuxBatchReservation
{
	MuxResources &resources;
	int64_t work = 0, bytes = 0, sat = 0;
	bool finishing = false;
	explicit MuxBatchReservation(MuxResources &resources) : resources(resources) { }
	~MuxBatchReservation()
	{
		log_assert(!finishing && work <= resources.batch_reserved);
		resources.batch_reserved -= work;
		resources.release(bytes);
	}
	bool reserve(int64_t work_amount, int64_t byte_amount, int64_t sat_amount)
	{
		log_assert(work == 0 && bytes == 0 && work_amount >= 0 && byte_amount >= 0 && sat_amount >= 0);
		MuxResources::Result failure = resources.exhausted ? MuxResources::TotalWorkLimit :
			!resources.can_spend(work_amount) ? MuxResources::CommitReservationLimit :
			!resources.can_reserve(byte_amount) ? MuxResources::WorkspaceLimit :
			!resources.can_query(sat_amount) ? MuxResources::SatLimit : MuxResources::Kept;
		if (failure != MuxResources::Kept) {
			resources.result = failure;
			return false;
		}
		work = work_amount; bytes = byte_amount; sat = sat_amount;
		resources.batch_reserved += work;
		log_assert(resources.reserve(bytes));
		return true;
	}
	void begin()
	{
		log_assert(!finishing && resources.finish_work == nullptr && resources.finish_bytes == nullptr && work > 0);
		finishing = true;
		resources.finish_work = &work;
		resources.finish_bytes = &bytes;
	}
	void end()
	{
		log_assert(finishing && resources.finish_work == &work && resources.finish_bytes == &bytes);
		resources.finish_work = nullptr; resources.finish_bytes = nullptr;
		finishing = false;
	}
};

struct MuxWorkspace
{
	MuxResources &resources;
	int64_t bytes = 0;
	explicit MuxWorkspace(MuxResources &resources) : resources(resources) { }
	~MuxWorkspace() { resources.release(bytes); }
	bool reserve(int64_t amount)
	{
		if (!resources.can_reserve(amount))
			return false;
		log_assert(resources.reserve(amount));
		bytes += amount;
		return true;
	}
	bool charge(int64_t amount, MuxResources::Phase phase = MuxResources::Functions)
	{
		if (!resources.can_spend(amount))
			return false;
		log_assert(resources.charge(amount, phase));
		return true;
	}
};

static inline bool muxledger_port_input(const CellTypes &types, const Cell *cell, IdString port)
{
	return !types.cell_known(cell->type) || types.cell_input(cell->type, port);
}

static inline bool muxledger_port_output(const CellTypes &types, const Cell *cell, IdString port)
{
	return !types.cell_known(cell->type) || types.cell_output(cell->type, port);
}

// 引用编码。全局表：0..3为四值常量，>=4为节点下标。
// 暂存表：0..3为暂存常量，>=4为暂存节点下标，<0表示既有全局函数（值为 -(global+1)）。
static inline int mux_global_entry(int global) { return -global - 1; }
static inline bool mux_is_global_entry(int ref) { return ref < 0; }
static inline int mux_global_index(int ref) { return -ref - 1; }

// 固定内容的四输入函数节点：至多四个输入Ref、有效输入数、16行各两位四值真值表合计一个uint32_t。
struct Lut4Functions
{
	using Ref = int;
	using Word = std::vector<Ref>;
	static constexpr int max_inputs = 4;
	static constexpr int max_rows = 1 << max_inputs;
	struct Node {
		std::array<Ref, max_inputs> inputs;
		SigBit signal;
		uint32_t table = 0;
		int arity = 0;
		bool leaf = false;
		Node() : inputs{{0, 0, 0, 0}} { }
	};
	// 每行两位：0=S0、1=S1、2=Sx、3=Sz。
	static constexpr uint32_t row_bits(State state)
	{
		return state == State::S0 ? 0u : state == State::S1 ? 1u : state == State::Sx ? 2u : 3u;
	}
	static constexpr State bits_row(uint32_t bits)
	{
		return bits == 0 ? State::S0 : bits == 1 ? State::S1 : bits == 2 ? State::Sx : State::Sz;
	}
	static uint32_t pack_table(const Const &values)
	{
		log_assert(GetSize(values) <= max_rows);
		uint32_t result = 0;
		for (int i = 0; i < GetSize(values); i++)
			result |= row_bits(values[i]) << (2 * i);
		return result;
	}
	static State table_row(uint32_t table, int index)
	{
		log_assert(index >= 0 && index < max_rows);
		return bits_row((table >> (2 * index)) & 3u);
	}
	struct FunctionKey {
		std::array<Ref, max_inputs> inputs;
		uint32_t table = 0;
		int arity = 0;
		FunctionKey() : inputs{{0, 0, 0, 0}} { }
		bool operator==(const FunctionKey &other) const
		{
			if (arity != other.arity || table != other.table)
				return false;
			for (int i = 0; i < arity; i++)
				if (inputs[i] != other.inputs[i])
					return false;
			return true;
		}
	};
	struct FunctionKeyHash {
		size_t operator()(const FunctionKey &key) const
		{
			Hasher hasher;
			hasher.eat(key.arity);
			hasher.eat(key.table);
			for (int i = 0; i < key.arity; i++)
				hasher.eat(key.inputs[i]);
			return (size_t)hasher.yield();
		}
	};
	struct SigBitHash {
		size_t operator()(const SigBit &bit) const { return (size_t)hashlib::hash_ops<SigBit>::hash(bit).yield(); }
	};

	std::vector<Node> nodes;
	std::unordered_map<SigBit, Ref, SigBitHash> signals;
	std::unordered_map<FunctionKey, Ref, FunctionKeyHash> functions;
	std::vector<Ref> boundaries;
	MuxResources *account = nullptr;
	MuxWorkspace *workspace = nullptr;
	int64_t growth_headroom = 0;
	int64_t bound = 0, synced_bytes = 0;
	int64_t work = 0, work_budget = 0, byte_budget = 0;
	bool exhausted = false;
	static constexpr int max_nodes = 200000;

	Lut4Functions() { add_constants(); }
	void add_constants()
	{
		for (State state : {State::S0, State::S1, State::Sx, State::Sz}) {
			Node node;
			node.signal = SigBit(state);
			node.table = row_bits(state);
			node.leaf = true;
			nodes.push_back(node);
		}
	}
	bool staged() const { return workspace != nullptr; }
	void begin_scratch(MuxWorkspace *scratch, int64_t work_limit, int64_t byte_limit)
	{
		workspace = scratch;
		work_budget = work_limit;
		byte_budget = byte_limit;
	}
	// 容器真实规模：vector capacity与标准散列表bucket数量。
	static int64_t table_bytes(size_t buckets, size_t entry_size)
	{
		return (int64_t)buckets * (int64_t)(sizeof(void *) + entry_size + sizeof(void *));
	}
	int64_t allocated_bytes() const
	{
		int64_t result = (int64_t)nodes.capacity() * (int64_t)sizeof(Node) +
			(int64_t)boundaries.capacity() * (int64_t)sizeof(Ref);
		result += table_bytes(signals.bucket_count(), sizeof(std::pair<const SigBit, Ref>));
		result += table_bytes(functions.bucket_count(), sizeof(std::pair<const FunctionKey, Ref>));
		return result;
	}
	void reset()
	{
		nodes.clear(); signals.clear(); functions.clear(); boundaries.clear();
		work = 0; exhausted = false; bound = 0;
		add_constants();
		// clear保留的capacity继续计费，只有真实销毁才返还空间。
		sync_account();
	}
	// 把容器容量的真实变化计入账户；只有真实销毁才返还空间。
	void sync_account()
	{
		if (account == nullptr)
			return;
		int64_t now = allocated_bytes();
		int64_t delta = now - synced_bytes;
		if (delta > 0)
			account->commit_growth(delta);
		else if (delta < 0)
			account->release(-delta);
		synced_bytes = now;
	}
	// 增长之前核查旧容器、新容器与回收工作区的并存峰值，局部失败只结束当前对象。
	bool approve_growth(int64_t additional)
	{
		log_assert(additional >= 0);
		int64_t current = allocated_bytes();
		if (staged() && current + additional > byte_budget)
			return false;
		int64_t wanted = additional + growth_headroom;
		if (account != nullptr && !account->approve_peak(wanted))
			return false;
		bound = std::max(bound, current + wanted);
		return true;
	}
	void verify_growth(const char *what)
	{
		int64_t current = allocated_bytes();
		if (current > bound)
			log_error("muxledger: %s 实际容器容量 %lld 字节超过批准上界 %lld。\n", what,
				(long long)current, (long long)bound);
		sync_account();
	}
	bool reserve_nodes(int64_t slots)
	{
		if ((int64_t)nodes.capacity() >= slots)
			return true;
		int64_t old_slots = (int64_t)nodes.capacity();
		int64_t growth = (slots - old_slots) * (int64_t)sizeof(Node);
		int64_t transient = old_slots * (int64_t)sizeof(Node);
		if (!approve_growth(growth + transient))
			return false;
		nodes.reserve((size_t)slots);
		verify_growth("nodes");
		return true;
	}
	template<typename Table>
	bool reserve_table(Table &table, size_t wanted, const char *name)
	{
		// 只有wanted超出当前load容量才reserve，增长按实际当前load容量的几何倍数预留。
		size_t capacity = (size_t)((double)table.bucket_count() * table.max_load_factor());
		if (capacity >= wanted)
			return true;
		size_t target = std::max(wanted, capacity * 2);
		int64_t estimate = (int64_t)(target * 2 + 16) *
			(int64_t)(sizeof(void *) + sizeof(typename Table::value_type) + sizeof(void *));
		if (!approve_growth(estimate))
			return false;
		table.reserve(target);
		verify_growth(name);
		return true;
	}
	bool reserve_signals(size_t wanted) { return reserve_table(signals, wanted, "signals"); }
	bool reserve_functions(size_t wanted) { return reserve_table(functions, wanted, "functions"); }
	// 额度不足时标记当前对象耗尽并返回false。
	bool charge_work(int64_t amount, MuxResources::Phase phase = MuxResources::Functions)
	{
		log_assert(amount >= 0);
		if (staged()) {
			if (amount > work_budget - work) {
				exhausted = true;
				return false;
			}
			if (!workspace->charge(amount, phase)) {
				exhausted = true;
				return false;
			}
		} else if (account != nullptr) {
			if (!account->can_spend(amount)) {
				exhausted = true;
				return false;
			}
			log_assert(account->charge(amount, phase));
		}
		work += amount;
		return true;
	}
	bool allocate_node()
	{
		if (GetSize(nodes) >= max_nodes) {
			exhausted = true;
			return false;
		}
		if ((int64_t)nodes.size() + 1 > (int64_t)nodes.capacity()) {
			int64_t slots = (int64_t)nodes.capacity() > 0 ? (int64_t)nodes.capacity() * 2 : 8;
			if (!reserve_nodes(slots)) {
				exhausted = true;
				return false;
			}
		}
		nodes.push_back(Node());
		return true;
	}
	// 失败清理追加节点与唯一表条目；clear/resize保留的真实capacity继续计费。
	void truncate(int count)
	{
		log_assert(count >= 4 && count <= GetSize(nodes));
		// 相同数量没有追加节点需要清理。
		if (GetSize(nodes) == count)
			return;
		// 只删除被截断尾部节点对应的唯一表条目，存活Ref与同名函数条目保持不动。
		for (int i = count; i < GetSize(nodes); i++) {
			const Node &node = nodes[i];
			if (node.leaf) {
				auto found = signals.find(node.signal);
				if (found != signals.end() && found->second == i)
					signals.erase(found);
				continue;
			}
			FunctionKey key;
			key.arity = node.arity;
			key.table = node.table;
			for (int j = 0; j < node.arity; j++)
				key.inputs[j] = node.inputs[j];
			auto found = functions.find(key);
			if (found != functions.end() && found->second == i)
				functions.erase(found);
		}
		nodes.resize(count);
		// 候选边界只清理指向已截断Ref的条目，保留vector容量。
		for (int i = GetSize(boundaries) - 1; i >= 0; i--)
			if (boundaries[i] >= count)
				boundaries.erase(boundaries.begin() + i);
		if (account != nullptr && !staged())
			sync_account();
	}
	Ref constant(State state) const
	{
		log_assert(state == State::S0 || state == State::S1 || state == State::Sx || state == State::Sz);
		return state == State::S0 ? 0 : state == State::S1 ? 1 : state == State::Sz ? 3 : 2;
	}
	static State constant_state(Ref ref)
	{
		log_assert(ref >= 0 && ref < 4);
		return ref == 0 ? State::S0 : ref == 1 ? State::S1 : ref == 3 ? State::Sz : State::Sx;
	}
	// 既有全局Ref在暂存表中的表示：常量直接复用，其余用负数编码。
	// 暂存表用负数入口引用已有全局函数，普通全局表直接使用原global Ref，四值常量始终保持0..3。
	Ref global_value(Ref global) const { return global < 4 ? global : staged() ? mux_global_entry(global) : global; }
	Ref signal(SigBit bit)
	{
		if (!bit.wire)
			return constant(bit.data);
		auto found = signals.find(bit);
		if (found != signals.end())
			return found->second;
		if (!allocate_node())
			return 2;
		Ref result = GetSize(nodes) - 1;
		nodes.back().signal = bit;
		nodes.back().leaf = true;
		if (!reserve_signals(signals.size() + 1)) {
			exhausted = true;
			return 2;
		}
		signals.emplace(bit, result);
		return result;
	}
	static State operation(IdString type, const std::vector<State> &args, uint32_t table = 0)
	{
		// $lut在args[0]访问之前分派，零参数直接取第0行。
		if (type == ID($lut))
			return resolve(table, GetSize(args), args);
		Const a(args[0]), b(args.size() > 1 ? args[1] : State::S0);
		if (type == ID($mux))
			return const_mux(a, b, Const(args[2]))[0];
		return CellTypes::eval(type, a, b, false, false, 1)[0];
	}
	// 与本项目采用的const_bmux掩码选择语义一致：X/Z子项在两侧结果不同时产生X。
	// 子项全部确定为S0/S1时，以child[i]作为索引第i位直接取表值，表值本身可为Sx/Sz。
	static State resolve(uint32_t table, int arity, const std::vector<State> &child)
	{
		log_assert(arity == GetSize(child) && arity <= max_inputs);
		int index = 0;
		bool known = true;
		for (int i = 0; i < arity; i++) {
			if (child[i] == State::S0)
				continue;
			if (child[i] == State::S1)
				index |= 1 << i;
			else {
				known = false;
				break;
			}
		}
		if (known)
			return table_row(table, index);
		std::vector<State> rows;
		rows.reserve(1 << arity);
		for (int i = 0; i < (1 << arity); i++)
			rows.push_back(table_row(table, i));
		return const_bmux(Const(rows), Const(child))[0];
	}
	// 取一个Ref在给定支持与二进制掩码下的四值状态。
	State evaluate(Ref ref, const Word &support, int mask) const
	{
		auto found = std::find(support.begin(), support.end(), ref);
		if (found != support.end())
			return (mask >> (found - support.begin())) & 1 ? State::S1 : State::S0;
		if (mux_is_global_entry(ref)) {
			log_assert(false);
			return State::Sx;
		}
		if (ref < 4)
			return constant_state(ref);
		const Node &node = nodes[ref];
		log_assert(!node.leaf && node.arity >= 1);
		std::vector<State> child;
		child.reserve(node.arity);
		for (int i = 0; i < node.arity; i++)
			child.push_back(evaluate(node.inputs[i], support, mask));
		return resolve(node.table, node.arity, child);
	}
	// 支持集合按Ref规范排序，真值随排序重排，并删除不改变函数结果的输入。
	Ref table(Word support, Const values)
	{
		int count = GetSize(support);
		log_assert(count <= max_inputs && GetSize(values) == (1 << count));
		if (count > 1) {
			// 已排序的支持直接沿用，只有真实乱序才分配order执行原有重排。
			if (!std::is_sorted(support.begin(), support.end())) {
				std::vector<int> order(count);
				for (int i = 0; i < count; i++) order[i] = i;
				std::sort(order.begin(), order.end(), [&](int a, int b) { return support[a] < support[b]; });
				Word sorted_support;
				std::vector<State> sorted_values(1 << count);
				for (int i = 0; i < count; i++)
					sorted_support.push_back(support[order[i]]);
				for (int m = 0; m < (1 << count); m++) {
					int source = 0;
					for (int i = 0; i < count; i++)
						if (m & (1 << i))
							source |= 1 << order[i];
					sorted_values[m] = values[source];
				}
				support = std::move(sorted_support);
				values = Const(std::move(sorted_values));
			}
			for (int i = 1; i < count; i++)
				log_assert(support[i - 1] != support[i]);
		}
		for (int i = GetSize(support) - 1; i >= 0; i--) {
			// 找到首个不同真值行即结束该输入的扫描。
			bool used = false;
			for (int m = 0; m < GetSize(values); m++)
				if (!(m & (1 << i)) && values[m] != values[m | (1 << i)]) {
					used = true;
					break;
				}
			if (used)
				continue;
			std::vector<State> reduced;
			for (int m = 0; m < GetSize(values); m++)
				if (!(m & (1 << i)))
					reduced.push_back(values[m]);
			values = Const(std::move(reduced));
			support.erase(support.begin() + i);
		}
		if (support.empty())
			return constant(values[0]);
		if (GetSize(support) == 1 && values[0] == State::S0 && values[1] == State::S1)
			return support[0];
		FunctionKey key;
		key.arity = GetSize(support);
		key.table = pack_table(values);
		for (int i = 0; i < key.arity; i++)
			key.inputs[i] = support[i];
		auto found = functions.find(key);
		if (found != functions.end())
			return found->second;
		if (!charge_work(GetSize(values)))
			return 2;
		if (!allocate_node())
			return 2;
		Ref result = GetSize(nodes) - 1;
		Node &node = nodes.back();
		node.inputs = key.inputs;
		node.arity = key.arity;
		node.table = key.table;
		node.leaf = false;
		if (!reserve_functions(functions.size() + 1)) {
			exhausted = true;
			return 2;
		}
		functions.emplace(key, result);
		return result;
	}
	// 已确定结果的化简在支持构造之前完成，简化路径按Ref检查与常量求值计费，普通路径保持原有费用。
	// $lut以packed四值真值表求值，args[i]对应行索引第i位；其余操作沿用原语义。
	Ref apply(IdString type, const Word &args, uint32_t packed_table = 0)
	{
		if (exhausted)
			return 2;
		// 先确定当前操作是否已有明确结果，随后按路径计费。
		bool determined = false;
		Ref value = 0;
		if (type == ID($and)) {
			for (Ref ref : args)
				if (ref == 0) {
					determined = true;
					break;
				}
		} else if (type == ID($or)) {
			for (Ref ref : args)
				if (ref == 1) {
					value = 1;
					determined = true;
					break;
				}
		} else if (type == ID($mux)) {
			if (args[2] == 0) {
				value = args[0];
				determined = true;
			} else if (args[2] == 1) {
				value = args[1];
				determined = true;
			} else if (args[0] == args[1]) {
				value = args[0];
				determined = true;
			}
		}
		if (!determined) {
			// 全常量先计入Ref检查与唯一operation求值的费用，再用既有operation求值；负数全局入口不作为常量。
			bool constants = true;
			for (Ref ref : args)
				if (ref < 0 || ref >= 4)
					constants = false;
			if (constants) {
				if (!charge_work(2 * GetSize(args) + 1))
					return 2;
				std::vector<State> states;
				states.reserve(GetSize(args));
				for (Ref ref : args)
					states.push_back(constant_state(ref));
				return constant(operation(type, states, packed_table));
			}
		}
		if (!charge_work(determined ? GetSize(args) : 32))
			return 2;
		if (determined)
			return value;
		// 已有的子函数Ref与叶子一样先作为LUT输入；只有展开后的支持并集不超过四个才吸收相邻函数。
		Word support;
		support.reserve(args.size());
		for (Ref ref : args)
			if (mux_is_global_entry(ref) || ref >= 4)
				support.push_back(ref);
		std::sort(support.begin(), support.end());
		support.erase(std::unique(support.begin(), support.end()), support.end());
		// 合并相邻函数，只在四个真实输入以内生成一个LUT4；既有全局函数与边界保持原子。
		for (int round = 0; round < 4; round++) {
			bool changed = false;
			for (Ref ref : support) {
				if (mux_is_global_entry(ref) || ref < 4 || nodes[ref].leaf || is_boundary(ref))
					continue;
				Word expanded;
				for (Ref input : support)
					if (input != ref)
						expanded.push_back(input);
				const Node &node = nodes[ref];
				for (int i = 0; i < node.arity; i++)
					expanded.push_back(node.inputs[i]);
				std::sort(expanded.begin(), expanded.end());
				expanded.erase(std::unique(expanded.begin(), expanded.end()), expanded.end());
				if (GetSize(expanded) <= max_inputs) {
					support.swap(expanded);
					changed = true;
					break;
				}
			}
			if (!changed)
				break;
		}
		std::vector<State> result;
		result.reserve(1 << GetSize(support));
		std::vector<State> values(GetSize(args));
		for (int mask = 0; mask < (1 << GetSize(support)); mask++) {
			for (int i = 0; i < GetSize(args); i++)
				values[i] = evaluate(args[i], support, mask);
			result.push_back(operation(type, values, packed_table));
		}
		if (!charge_work(GetSize(result) * (GetSize(args) + 1)))
			return 2;
		return table(std::move(support), Const(std::move(result)));
	}
	Ref invert(Ref ref) { return apply(ID($not), {ref}); }
	Ref mux(Ref a, Ref b, Ref s) { return apply(ID($mux), {a, b, s}); }
	bool is_boundary(Ref ref) const { return std::find(boundaries.begin(), boundaries.end(), ref) != boundaries.end(); }
	void boundary(const Word &outputs)
	{
		for (Ref ref : outputs)
			if (!is_boundary(ref))
				boundaries.push_back(ref);
	}
	pool<Ref> boundary_pool() const
	{
		pool<Ref> result;
		for (Ref ref : boundaries)
			result.insert(ref);
		return result;
	}
	Ref reduce(IdString type, Word inputs)
	{
		Ref identity = type == ID($and) ? 1 : 0;
		if (inputs.empty())
			return identity;
		while (GetSize(inputs) > 1) {
			Word next;
			for (int i = 0; i < GetSize(inputs); i += 4) {
				Ref value = inputs[i];
				for (int j = i + 1; j < std::min(i + 4, GetSize(inputs)); j++)
					value = apply(type, {value, inputs[j]});
				next.push_back(value);
			}
			inputs.swap(next);
		}
		return inputs[0];
	}
	pool<Ref> dependencies(const Word &roots, const pool<Ref> *inputs = nullptr)
	{
		pool<Ref> result;
		Word todo = roots;
		while (!todo.empty()) {
			if (!charge_work(1, MuxResources::Dependencies)) {
				exhausted = true;
				break;
			}
			Ref ref = todo.back();
			todo.pop_back();
			if (mux_is_global_entry(ref) || ref < 4 || nodes[ref].leaf ||
					(inputs != nullptr && inputs->count(ref)) || !result.insert(ref).second)
				continue;
			const Node &node = nodes[ref];
			for (int i = 0; i < node.arity; i++)
				todo.push_back(node.inputs[i]);
		}
		return result;
	}
	// 只把输出与input_functions需要的最终可达闭包intern到目标唯一表。
	// intern以最终子Ref重新规范化排序与真值重排，重复子Ref合并，常量子Ref代入。
	Word intern(Lut4Functions &target, const Word &roots, pool<Ref> *inputs)
	{
		std::vector<unsigned char> mark(GetSize(nodes), 0);
		Word order, todo = roots;
		while (!todo.empty()) {
			Ref ref = todo.back();
			todo.pop_back();
			if (ref < 0)
				continue;
			log_assert(ref < GetSize(nodes));
			if (mark[ref])
				continue;
			mark[ref] = 1;
			order.push_back(ref);
			if (ref < 4 || nodes[ref].leaf)
				continue;
			const Node &node = nodes[ref];
			for (int i = 0; i < node.arity; i++)
				todo.push_back(node.inputs[i]);
		}
		std::sort(order.begin(), order.end());
		Word mapped(GetSize(nodes), -1);
		for (Ref ref : order) {
			if (ref < 4) {
				mapped[ref] = ref;
				continue;
			}
			const Node &node = nodes[ref];
			if (node.leaf) {
				mapped[ref] = target.signal(node.signal);
				if (target.exhausted) {
					exhausted = true;
					return Word();
				}
				continue;
			}
			Word child;
			for (int i = 0; i < node.arity; i++) {
				Ref input = node.inputs[i];
				if (mux_is_global_entry(input))
					child.push_back(mux_global_index(input));
				else {
					log_assert(mapped[input] >= 0);
					child.push_back(mapped[input]);
				}
			}
			Word free_refs;
			std::vector<int> position;
			for (int i = 0; i < GetSize(child); i++) {
				if (child[i] < 4) {
					position.push_back(-child[i] - 1);
					continue;
				}
				int at = -1;
				for (int j = 0; j < GetSize(free_refs); j++)
					if (free_refs[j] == child[i]) { at = j; break; }
				if (at < 0) {
					at = GetSize(free_refs);
					free_refs.push_back(child[i]);
				}
				position.push_back(at);
			}
			std::vector<State> values;
			values.reserve(1 << GetSize(free_refs));
			std::vector<State> child_state(GetSize(position));
			for (int mask = 0; mask < (1 << GetSize(free_refs)); mask++) {
				for (int i = 0; i < GetSize(position); i++) {
					int slot = position[i];
					child_state[i] = slot < 0 ? constant_state(-slot - 1) :
						((mask >> slot) & 1 ? State::S1 : State::S0);
				}
				values.push_back(resolve(node.table, node.arity, child_state));
			}
			mapped[ref] = target.table(std::move(free_refs), Const(std::move(values)));
			if (target.exhausted) {
				exhausted = true;
				return Word();
			}
		}
		Word result;
		for (Ref ref : roots) {
			if (mux_is_global_entry(ref))
				result.push_back(mux_global_index(ref));
			else {
				log_assert(mapped[ref] >= 0);
				result.push_back(mapped[ref]);
			}
		}
		if (inputs != nullptr) {
			std::vector<Ref> original(inputs->begin(), inputs->end());
			inputs->clear();
			for (Ref ref : original) {
				Ref value = mux_is_global_entry(ref) ? mux_global_index(ref) : mapped[ref];
				log_assert(value >= 0);
				inputs->insert(value);
			}
		}
		return result;
	}
};

struct MuxPortBit {
	IdString cell, port;
	int offset;
};

struct MuxCellCost {
	IdString type;
	dict<IdString, SigSpec> connections;
	dict<IdString, Const> parameters, attributes;
	uint64_t generation = 0;
	Lut4Functions::Word outputs;
	pool<Lut4Functions::Ref> input_functions;
	pool<Lut4Functions::Ref> dependencies;
	bool supported = false;
	bool removed = false;
	int rank = -1;
	MuxResources::Result result = MuxResources::UnsupportedModel;
};

struct MuxResourceScope
{
	Design *design;
	int id;
	bool had_scope;
	std::string saved_scope;
	MuxResourceScope(Design *design) : design(design), had_scope(design->scratchpad.count("muxledger.scope")),
		saved_scope(design->scratchpad_get_string("muxledger.scope"))
	{
		static int next_id = 0;
		id = ++next_id;
		mux_shared_work()[id] = {};
		design->scratchpad_set_int("muxledger.scope", id);
	}
	~MuxResourceScope()
	{
		mux_shared_work().erase(id);
		if (had_scope)
			design->scratchpad_set_string("muxledger.scope", saved_scope);
		else
			design->scratchpad_unset("muxledger.scope");
	}
};

// 模块成本上下文：每次调用自行拥有本模块的函数存储与组合拓扑顺序。
struct MuxCostContext
{
	using Ref = Lut4Functions::Ref;
	using Word = Lut4Functions::Word;
	using PortBit = MuxPortBit;
	using CellCostInfo = MuxCellCost;
	Module *module;
	MuxResources resources;
	SigMap sigmap;
	CellTypes types;
	CellTypes combinational;
	Lut4Functions functions;
	uint64_t generation = 0;
	dict<SigBit, std::vector<PortBit>> drivers, users;
	dict<SigBit, int> use_count;
	pool<SigBit> protected_bits, output_bits;
	pool<IdString> cyclic;
	dict<IdString, CellCostInfo> cells;
	dict<Ref, int> owners;
	dict<SigBit, Ref> output_functions;
	const dict<SigBit, Ref> *planned_outputs = nullptr;
	int committed_nodes = 4;
	// 初建完成或最近一次真正完成GC之后的节点基数，只由这两处更新。
	size_t collect_nodes = 0;
	// 小提交之间保留的真实失效累计，只有完成实际回收才清零。
	int64_t invalidated_cells = 0;
	bool model_complete = false;
	int64_t boundary_cells = 0, budget_incomplete_cells = 0;
	MuxResources::Result result_note = MuxResources::Kept;

	explicit MuxCostContext(Module *module) : module(module), resources(module)
	{
		types.setup(module->design);
		combinational.setup_internals_eval();
		combinational.setup_stdcells_eval();
		functions.account = &resources;
	}

	// 结构必要扫描：只读当前selection的类型，达到阈值立即停止。
	template<typename Predicate>
	bool type_scan(Predicate matched, int threshold, const char *purpose)
	{
		int matching_seen = 0;
		int64_t before = resources.used;
		for (Cell *cell : module->selected_cells()) {
			if (!resources.can_spend(4)) {
				resources.result = MuxResources::TotalWorkLimit;
				log("MUXSCAN module=%s purpose=%s matching_seen=%d threshold=%d scan_complete=0 eligible=0 index_built=0 reason=TotalWorkLimit\n",
					log_id(module), purpose, matching_seen, threshold);
				return false;
			}
			log_assert(resources.charge(4, MuxResources::Index));
			if (matched(cell)) {
				matching_seen++;
				if (matching_seen >= threshold)
					break;
			}
		}
		bool eligible = matching_seen >= threshold;
		log("MUXSCAN module=%s purpose=%s work=%lld matching_seen=%d threshold=%d scan_complete=1 eligible=%d index_built=0\n",
			log_id(module), purpose, (long long)(resources.used - before), matching_seen,
			threshold, eligible);
		return eligible;
	}

	void discard_candidate()
	{
		functions.truncate(committed_nodes);
		functions.boundaries.clear();
	}
	int64_t index_work() const
	{
		int64_t result = GetSize(module->cells()) * 16;
		for (Wire *wire : module->wires())
			result += wire->width * 4;
		for (Cell *cell : module->cells())
			for (const auto &port : cell->connections())
				result += 8 + GetSize(port.second) * 8;
		return result;
	}
	// 回收工作的真实并存空间：mark、old_to_new、owners重建与唯一表迁移。
	int64_t reclaim_bytes() const
	{
		int64_t count = GetSize(functions.nodes);
		int64_t owners_bytes = (int64_t)GetSize(owners) * (int64_t)sizeof(std::pair<Ref, int>) * 2 + 64;
		int64_t tables = (int64_t)(functions.signals.size() + functions.functions.size()) *
			(int64_t)(sizeof(void *) + 32) * 2 + 512;
		return 2048 + (count + 7) / 8 + count * (int64_t)(sizeof(Ref) + sizeof(std::pair<Ref, int>)) + owners_bytes + tables;
	}
	int64_t reclaim_work() const
	{
		int64_t work = GetSize(functions.nodes) * 32 + GetSize(cells) * 8 + GetSize(output_functions) * 4;
		for (const auto &entry : cells)
			work += (GetSize(entry.second.outputs) + GetSize(entry.second.input_functions) +
				GetSize(entry.second.dependencies)) * 8;
		return work;
	}
	// 安全回收位置：完整CellCostInfo安装之后、下一单元尚未开始且没有候选或暂存Ref。
	void collect_functions(Word *retained = nullptr, bool force = false)
	{
		if (planned_outputs != nullptr)
			return;
		if (!force && functions.allocated_bytes() < resources.memory_limit / 8 && GetSize(functions.nodes) < 4096)
			return;
		int64_t temporary = reclaim_bytes();
		int64_t work = reclaim_work() + (retained == nullptr ? 0 : GetSize(*retained) * 4);
		if (resources.exhausted || !resources.can_reserve(temporary) || !resources.can_spend(work))
			return;
		MuxWorkspace workspace(resources);
		if (!workspace.reserve(temporary))
			return;
		int64_t before_work = resources.used;
		if (!resources.charge(work, MuxResources::Reclaim))
			return;
		int count = GetSize(functions.nodes);
		std::vector<unsigned char> mark((count + 7) / 8, 0);
		Word mapping(count, -1);
		auto marked = [&](Ref ref) { log_assert(ref >= 0 && ref < count); return (mark[ref / 8] >> (ref % 8)) & 1; };
		auto retain = [&](Ref ref) { log_assert(ref >= 0 && ref < count); mark[ref / 8] |= 1 << (ref % 8); };
		for (Ref ref = 0; ref < 4; ref++)
			retain(ref);
		for (const auto &entry : cells) {
			const auto &info = entry.second;
			for (Ref ref : info.outputs) retain(ref);
			for (Ref ref : info.input_functions) retain(ref);
			for (Ref ref : info.dependencies) retain(ref);
		}
		for (const auto &entry : output_functions)
			retain(entry.second);
		for (const auto &entry : owners)
			if (entry.second > 0) retain(entry.first);
		for (Ref ref : functions.boundaries) retain(ref);
		if (retained != nullptr)
			for (Ref ref : *retained) retain(ref);
		for (Ref ref = count - 1; ref >= 0; ref--) {
			if (!marked(ref) || functions.nodes[ref].leaf)
				continue;
			for (int i = 0; i < functions.nodes[ref].arity; i++) {
				Ref input = functions.nodes[ref].inputs[i];
				log_assert(input < ref);
				retain(input);
			}
		}
		// 清除唯一表后复用其既有capacity，Node arena只在原容器内移动。
		functions.signals.clear(); functions.functions.clear();
		int next = 0;
		for (Ref ref = 0; ref < count; ref++) {
			if (!marked(ref))
				continue;
			mapping[ref] = next;
			if (next != ref)
				functions.nodes[next] = std::move(functions.nodes[ref]);
			auto &node = functions.nodes[next];
			for (int i = 0; i < node.arity; i++) {
				log_assert(mapping[node.inputs[i]] >= 0);
				node.inputs[i] = mapping[node.inputs[i]];
				log_assert(node.inputs[i] < next);
			}
			if (next >= 4) {
				if (node.leaf) {
					log_assert(functions.signals.emplace(node.signal, next).second);
				} else {
					Lut4Functions::FunctionKey key;
					key.arity = node.arity;
					key.table = node.table;
					key.inputs = node.inputs;
					log_assert(functions.functions.emplace(key, next).second);
				}
			}
			next++;
		}
		functions.nodes.resize(next);
		auto remap = [&](Ref &ref) { log_assert(ref >= 0 && ref < count && mapping[ref] >= 0); ref = mapping[ref]; };
		auto remap_pool = [&](pool<Ref> &refs) {
			Word values(refs.begin(), refs.end());
			refs.clear();
			for (Ref ref : values) { remap(ref); log_assert(refs.insert(ref).second); }
		};
		generation++;
		for (auto &entry : cells) {
			for (Ref &ref : entry.second.outputs)
				remap(ref);
			remap_pool(entry.second.input_functions);
			remap_pool(entry.second.dependencies);
			entry.second.generation = generation;
		}
		for (auto &entry : output_functions)
			remap(entry.second);
		std::vector<std::pair<Ref, int>> owner_values(owners.begin(), owners.end());
		owners.clear();
		for (const auto &entry : owner_values)
			if (entry.second > 0) { Ref ref = entry.first; remap(ref); log_assert(owners.emplace(ref, entry.second).second); }
		for (Ref &ref : functions.boundaries)
			remap(ref);
		if (retained != nullptr)
			for (Ref &ref : *retained) remap(ref);
		committed_nodes = GetSize(functions.nodes);
		collect_nodes = GetSize(functions.nodes);
		invalidated_cells = 0;
		functions.sync_account();
		log("MUXGC module=%s nodes_before=%d nodes_after=%d allocated_bytes=%lld work=%lld temporary_bytes=%lld live_bytes=%lld generation=%llu\n",
			log_id(module), count, next, (long long)functions.allocated_bytes(),
			(long long)(resources.used - before_work), (long long)workspace.bytes,
			(long long)resources.live_bytes, (unsigned long long)generation);
	}

	bool live(SigBit bit) const
	{
		bit = sigmap(bit);
		return bit.wire && (protected_bits.count(bit) || output_bits.count(bit) || use_count.at(bit, 0) > 0);
	}
	static bool modelled(IdString type)
	{
		return type.in(ID($mux), ID($pmux), ID($not), ID($pos), ID($buf), ID($and), ID($or), ID($xor), ID($xnor),
			ID($andnot), ID($ornot), ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor),
			ID($reduce_bool), ID($logic_not), ID($logic_and), ID($logic_or), ID($eq), ID($ne),
			ID($lt), ID($le), ID($gt), ID($ge), ID($lut));
	}
	static int64_t snapshot_bytes(Cell *cell)
	{
		int64_t bytes = 256 + (GetSize(cell->connections()) + GetSize(cell->parameters) + GetSize(cell->attributes)) * 256;
		for (const auto &entry : cell->parameters) bytes += entry.second.size() * 2;
		for (const auto &entry : cell->attributes) bytes += entry.second.size() * 2;
		return bytes;
	}
	Word word(const SigSpec &sig, Lut4Functions &fn)
	{
		Word result;
		for (SigBit bit : sigmap(sig)) {
			const Ref *planned = nullptr;
			if (planned_outputs != nullptr) {
				auto found = planned_outputs->find(bit);
				if (found != planned_outputs->end())
					planned = &found->second;
			}
			auto existing = output_functions.find(bit);
			Ref ref;
			if (planned != nullptr)
				ref = fn.global_value(*planned);
			else if (existing != output_functions.end())
				ref = fn.global_value(existing->second);
			else
				ref = fn.signal(bit);
			if (planned != nullptr || existing != output_functions.end())
				fn.boundary({ref});
			result.push_back(ref);
		}
		return result;
	}
	Word word(const SigSpec &sig) { return word(sig, functions); }

	// 单元完整函数在有限暂存DAG内求值，只把输出与input_functions需要的最终可达闭包intern。
	bool model(Cell *cell, const dict<IdString, SigSpec> &ports, bool &supported, Word &outputs,
			pool<Ref> *inputs = nullptr, bool *alias_conflict = nullptr)
	{
		if (alias_conflict != nullptr) *alias_conflict = false;
		IdString type = cell->type;
		supported = modelled(type);
		int64_t occurrences = 0;
		for (const auto &port : ports)
			occurrences += GetSize(port.second);
		if (!resources.can_spend(32 + occurrences)) {
			supported = false;
			result_note = MuxResources::TotalWorkLimit;
			return false;
		}
		log_assert(resources.charge(32 + occurrences));
		if (!supported) {
			result_note = MuxResources::UnsupportedModel;
			return false;
		}
		int checkpoint = GetSize(functions.nodes);
		MuxWorkspace scratch_workspace(resources);
		Lut4Functions staged;
		staged.begin_scratch(&scratch_workspace, std::max<int64_t>(4096, occurrences * 64 + 8192),
			std::min<int64_t>(resources.memory_limit / 8, std::max<int64_t>(65536, occurrences * 512 + 32768)));
		Word staged_outputs;
		bool ok = true;
		if (!build_model(cell, ports, type, staged, staged_outputs, ok) || staged.exhausted) {
			supported = false;
			result_note = staged.exhausted ? MuxResources::WorkspaceLimit : MuxResources::UnsupportedModel;
			functions.truncate(checkpoint);
			return false;
		}
		staged_outputs.resize(GetSize(ports.at(ID::Y)), 0);
		pool<Ref> interned_inputs = staged.boundary_pool();
		Word roots = staged_outputs;
		for (Ref ref : interned_inputs)
			roots.push_back(ref);
		Word interned = staged.intern(functions, roots, &interned_inputs);
		if (GetSize(interned) != GetSize(roots) || functions.exhausted) {
			supported = false;
			result_note = functions.exhausted ? MuxResources::WorkspaceLimit : MuxResources::UnsupportedModel;
			functions.truncate(checkpoint);
			return false;
		}
		outputs.assign(interned.begin(), interned.begin() + GetSize(ports.at(ID::Y)));
		dict<SigBit, Ref> identities;
		SigSpec destinations = sigmap(ports.at(ID::Y));
		for (int i = 0; i < GetSize(outputs); i++) {
			if (identities.count(destinations[i]) && identities.at(destinations[i]) != outputs[i]) {
				supported = false;
				if (alias_conflict != nullptr) *alias_conflict = true;
			}
			identities[destinations[i]] = outputs[i];
		}
		if (!supported) {
			functions.truncate(checkpoint);
			return false;
		}
		if (inputs != nullptr)
			*inputs = interned_inputs;
		return true;
	}

	bool build_model(Cell *cell, const dict<IdString, SigSpec> &ports, IdString type, Lut4Functions &fn,
			Word &result, bool &ok)
	{
		int width = GetSize(ports.at(ID::Y));
		SigSpec a = sigmap(ports.at(ID::A));
		SigSpec b = sigmap(ports.at(ID::B, SigSpec()));
		bool as = cell->hasParam(ID::A_SIGNED) && cell->getParam(ID::A_SIGNED).as_bool();
		bool bs = cell->hasParam(ID::B_SIGNED) && cell->getParam(ID::B_SIGNED).as_bool();
		if (type.in(ID($mux), ID($pmux))) {
			// 相邻两项合成四输入函数((B0&S0)|(B1&S1))，输入顺序[B0,S0,B1,S1]；该真值表只转换一次。
			static const uint32_t pair_table = Lut4Functions::pack_table(Const(0xf888, 16));
			Word aa = word(a, fn), bb = word(b, fn), ss = word(ports.at(ID::S), fn);
			log_assert(GetSize(aa) == width && GetSize(bb) == width * GetSize(ss));
			Ref any = type == ID($pmux) ? fn.reduce(ID($or), ss) : ss.at(0);
			for (int i = 0; i < width; i++) {
				Ref branch;
				if (type == ID($mux))
					branch = bb[i];
				else {
					Word products;
					int j = 0;
					for (; j + 1 < GetSize(ss); j += 2) {
						Ref b0 = bb[j * width + i], s0 = ss[j];
						Ref b1 = bb[(j + 1) * width + i], s1 = ss[j + 1];
						// 配对参数出现四值常量时保持原AND/OR求值；负数全局入口属于非常量。
						if ((b0 >= 0 && b0 < 4) || (s0 >= 0 && s0 < 4) ||
								(b1 >= 0 && b1 < 4) || (s1 >= 0 && s1 < 4)) {
							Ref left = fn.apply(ID($and), {b0, s0});
							Ref right = fn.apply(ID($and), {b1, s1});
							products.push_back(fn.apply(ID($or), {left, right}));
						} else
							products.push_back(fn.apply(ID($lut), {b0, s0, b1, s1}, pair_table));
					}
					// 奇数尾项沿用一次AND。
					if (j < GetSize(ss))
						products.push_back(fn.apply(ID($and), {bb[j * width + i], ss[j]}));
					branch = fn.reduce(ID($or), std::move(products));
				}
				result.push_back(fn.mux(aa[i], branch, any));
			}
		} else if (type == ID($lut)) {
			int n = GetSize(a);
			if (n > 12) {
				ok = false;
				return false;
			}
			Word lut_inputs = word(a, fn);
			Const values = cell->getParam(ID::LUT);
			std::vector<State> truth = values.to_bits();
			truth.resize(1 << n, State::S0);
			values = Const(truth);
			// A[0]为最低地址位：零参数直接取常量，n<=4一次四输入组合，n>4沿用原递归。
			if (n == 0)
				result.push_back(fn.constant(values[0]));
			else if (n <= Lut4Functions::max_inputs)
				result.push_back(fn.apply(ID($lut), lut_inputs, Lut4Functions::pack_table(values)));
			else
				result.push_back(build_table(fn, values, lut_inputs, 0, n));
		} else if (type.in(ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge))) {
			if (!type.in(ID($eq), ID($ne)))
				for (const SigSpec &operand : {a, b})
					for (SigBit bit : operand)
						if (!bit.wire && bit != State::S0 && bit != State::S1) {
							ok = false;
							return false;
						}
			int n = std::max(GetSize(a), GetSize(b));
			a.extend_u0(n, as && bs);
			b.extend_u0(n, as && bs);
			Word aa = word(a, fn), bb = word(b, fn);
			Ref value;
			if (type.in(ID($eq), ID($ne))) {
				Word equals;
				for (int i = 0; i < n; i++)
					equals.push_back(fn.invert(fn.apply(ID($xor), {aa[i], bb[i]})));
				Ref eq = fn.reduce(ID($and), std::move(equals));
				value = type == ID($eq) ? eq : fn.invert(eq);
			} else {
				if (as && bs && n > 0) {
					aa[n - 1] = fn.invert(aa[n - 1]);
					bb[n - 1] = fn.invert(bb[n - 1]);
				}
				if (type.in(ID($gt), ID($ge)))
					std::swap(aa, bb);
				// 非严格比较保存逐位equal并归约。
				bool strict = type.in(ID($lt), ID($gt));
				Word equals;
				value = 0;
				for (int i = 0; i < n; i++) {
					Ref less = fn.apply(ID($and), {fn.invert(aa[i]), bb[i]});
					Ref equal = fn.invert(fn.apply(ID($xor), {aa[i], bb[i]}));
					if (!strict)
						equals.push_back(equal);
					value = fn.apply(ID($or), {less, fn.apply(ID($and), {equal, value})});
				}
				if (!strict)
					value = fn.apply(ID($or), {value, fn.reduce(ID($and), std::move(equals))});
			}
			result.push_back(value);
		} else if (type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($logic_not), ID($reduce_xor), ID($reduce_xnor), ID($logic_and), ID($logic_or))) {
			IdString op = type == ID($reduce_and) ? ID($and) : type.in(ID($reduce_xor), ID($reduce_xnor)) ? ID($xor) : ID($or);
			Ref value = fn.reduce(op, word(a, fn));
			if (type.in(ID($logic_and), ID($logic_or)))
				value = fn.apply(type == ID($logic_and) ? ID($and) : ID($or), {value, fn.reduce(ID($or), word(b, fn))});
			if (type.in(ID($logic_not), ID($reduce_xnor)))
				value = fn.invert(value);
			result.push_back(value);
		} else {
			bool binary = !type.in(ID($not), ID($pos), ID($buf));
			a.extend_u0(width, binary ? as && bs : as);
			b.extend_u0(width, as && bs);
			Word aa = word(a, fn), bb = word(b, fn);
			for (int i = 0; i < width; i++) {
				Ref value;
				if (type.in(ID($pos), ID($buf)))
					value = aa[i];
				else if (type == ID($not))
					value = fn.invert(aa[i]);
				else if (type.in(ID($andnot), ID($ornot)))
					value = fn.apply(type == ID($andnot) ? ID($and) : ID($or), {aa[i], fn.invert(bb[i])});
				else
					value = fn.apply(type, {aa[i], bb[i]});
				result.push_back(value);
			}
		}
		if (fn.exhausted) {
			ok = false;
			return false;
		}
		return true;
	}
	Ref build_table(Lut4Functions &fn, const Const &values, const Word &inputs, int offset, int bits)
	{
		if (bits == 0)
			return fn.constant(values[offset]);
		return fn.mux(build_table(fn, values, inputs, offset, bits - 1),
			build_table(fn, values, inputs, offset + (1 << (bits - 1)), bits - 1), inputs[bits - 1]);
	}

	bool mutable_cell(Cell *cell) const
	{
		if (!modelled(cell->type) || cell->has_keep_attr() || cell->get_bool_attribute(ID::lut_keep) ||
			cell->attributes.count(ID::init) || cyclic.count(cell->name))
			return false;
		for (const auto &port : cell->connections())
			if (muxledger_port_output(types, cell, port.first))
				for (SigBit bit : sigmap(port.second))
					if (!bit.wire || protected_bits.count(bit) || unique_driver(bit) != cell)
						return false;
		return true;
	}
	Cell *unique_driver(SigBit bit) const
	{
		bit = sigmap(bit);
		auto it = drivers.find(bit);
		if (it == drivers.end() || it->second.empty())
			return nullptr;
		IdString name = it->second.front().cell;
		if (name.empty())
			return nullptr;
		for (const PortBit &driver : it->second)
			if (driver.cell != name)
				return nullptr;
		return module->cell(name);
	}

	CellCostInfo build_cell_info(Cell *cell)
	{
		int checkpoint = GetSize(functions.nodes);
		CellCostInfo info;
		info.type = cell->type; info.connections = cell->connections();
		info.parameters = cell->parameters; info.attributes = cell->attributes; info.generation = generation;
		bool alias_conflict = false;
		result_note = MuxResources::Kept;
		bool built = model(cell, info.connections, info.supported, info.outputs, &info.input_functions, &alias_conflict);
		info.result = alias_conflict ? MuxResources::AliasConflict :
			built ? MuxResources::Kept : result_note != MuxResources::Kept ? result_note : MuxResources::UnsupportedModel;
		if (built) {
			Word active;
			SigSpec y = cell->getPort(ID::Y);
			for (int i = 0; i < GetSize(y); i++)
				if (live(y[i]) || cell->has_keep_attr())
					active.push_back(info.outputs[i]);
			info.dependencies = functions.dependencies(active, &info.input_functions);
			built &= !functions.exhausted;
		}
		if (!built) {
			info.outputs.clear(); info.input_functions.clear(); info.dependencies.clear();
			info.supported = false;
			functions.truncate(checkpoint);
			if (info.result == MuxResources::WorkspaceLimit || info.result == MuxResources::TotalWorkLimit ||
					info.result == MuxResources::SatLimit)
				budget_incomplete_cells++;
			return info;
		}
		for (Ref ref : info.dependencies)
			owners[ref]++;
		if (mutable_cell(cell)) {
			SigSpec y = cell->getPort(ID::Y);
			for (int i = 0; i < GetSize(y); i++)
				output_functions[sigmap(y[i])] = info.outputs[i];
		} else {
			boundary_cells++;
		}
		return info;
	}

	// 轻量回收触发：累计真实失效与新增长，只有完成实际回收才清零累计量。
	bool reclaim_due() const
	{
		return invalidated_cells > 0 && (invalidated_cells >= 32 || GetSize(functions.nodes) - collect_nodes >= 1024);
	}
	// 无新增别名连接的提交：只更新实际修改的单元及其函数后继，禁止全部TFO重建。
	void update(const pool<IdString> &modified)
	{
		discard_candidate();
		resources.account(GetSize(modified) * 32, MuxResources::Commit);
		generation++;
		pool<SigBit> touched;
		dict<SigBit, int> old_uses;
		dict<SigBit, std::vector<PortBit>> old_drivers;
		auto touch = [&](SigBit bit) {
			if (touched.insert(bit).second) {
				old_uses[bit] = use_count.at(bit, 0);
				auto found = drivers.find(bit);
				if (found != drivers.end())
					old_drivers[bit] = found->second;
			}
		};
		pool<IdString> dirty = modified;
		for (IdString name : modified) {
			auto it = cells.find(name);
			if (it != cells.end()) {
				const auto &info = it->second;
				for (const auto &port : info.connections)
					for (SigBit bit : sigmap(port.second)) {
						resources.account(4, MuxResources::Commit);
						if (!bit.wire)
							continue;
						touch(bit);
						auto remove_ports = [&](dict<SigBit, std::vector<PortBit>> &index) {
							auto found = index.find(bit);
							if (found != index.end()) {
								auto &ports = found->second;
								ports.erase(std::remove_if(ports.begin(), ports.end(),
									[&](const PortBit &entry) { return entry.cell == name; }), ports.end());
							}
						};
						remove_ports(users); remove_ports(drivers);
						use_count[bit] = GetSize(users.at(bit, std::vector<PortBit>()));
					}
			}
			Cell *cell = module->cell(name);
			if (cell == nullptr)
				continue;
			for (const auto &port : cell->connections()) {
				resources.account(4 + GetSize(port.second), MuxResources::Commit);
				SigSpec mapped = sigmap(port.second);
				for (int i = 0; i < GetSize(mapped); i++) {
					SigBit bit = mapped[i];
					if (!bit.wire)
						continue;
					touch(bit);
					if (muxledger_port_input(types, cell, port.first)) {
						users[bit].push_back({name, port.first, i});
						use_count[bit]++;
					}
					if (muxledger_port_output(types, cell, port.first))
						drivers[bit].push_back({name, port.first, i});
				}
			}
		}
		for (SigBit bit : touched) {
			auto driver_it = drivers.find(bit);
			bool liveness_changed = (old_uses.at(bit, 0) > 0) != (use_count.at(bit, 0) > 0);
			if (liveness_changed && driver_it != drivers.end())
				for (const PortBit &driver : driver_it->second)
					if (!driver.cell.empty())
						dirty.insert(driver.cell);
			pool<std::tuple<IdString, IdString, int>> before, after;
			auto old_it = old_drivers.find(bit);
			if (old_it != old_drivers.end())
				for (const PortBit &driver : old_it->second)
					before.insert({driver.cell, driver.port, driver.offset});
			if (driver_it != drivers.end())
				for (const PortBit &driver : driver_it->second)
					after.insert({driver.cell, driver.port, driver.offset});
			auto user_it = users.find(bit);
			if (before != after && user_it != users.end())
				for (const PortBit &user : user_it->second)
					dirty.insert(user.cell);
		}
		std::vector<IdString> todo(dirty.begin(), dirty.end());
		for (int i = 0; i < GetSize(todo); i++) {
			resources.account(8, MuxResources::Commit);
			auto it = cells.find(todo[i]);
			if (it == cells.end())
				continue;
			Cell *source = module->cell(todo[i]);
			if (source != nullptr && !combinational.cell_known(source->type))
				continue;
			for (const auto &port : it->second.connections) {
				Cell *cell = module->cell(todo[i]);
				bool output = cell == nullptr ? port.first == ID::Y : muxledger_port_output(types, cell, port.first);
				if (!output)
					continue;
				for (SigBit bit : sigmap(port.second)) {
					auto user_it = users.find(bit);
					if (user_it == users.end())
						continue;
					for (const PortBit &user : user_it->second)
						if (dirty.insert(user.cell).second)
							todo.push_back(user.cell);
				}
			}
		}
		for (IdString name : dirty) {
			resources.account(8, MuxResources::Commit);
			auto it = cells.find(name);
			if (it == cells.end())
				continue;
			for (Ref ref : it->second.dependencies) {
				log_assert(owners.at(ref, 0) > 0);
				owners.at(ref)--;
			}
			if (it->second.connections.count(ID::Y))
				for (SigBit bit : sigmap(it->second.connections.at(ID::Y)))
					output_functions.erase(bit);
			cells.erase(it);
			// 真实删除的旧CellCostInfo在这一既有位置累计，同时覆盖后续真实替换。
			invalidated_cells++;
		}
		dict<IdString, int> incoming;
		dict<IdString, pool<IdString>> outgoing;
		for (IdString name : dirty) {
			Cell *cell = module->cell(name);
			if (cell == nullptr)
				continue;
			pool<IdString> predecessors;
			if (combinational.cell_known(cell->type))
				for (const auto &port : cell->connections())
					if (muxledger_port_input(types, cell, port.first))
						for (SigBit bit : sigmap(port.second)) {
							Cell *driver = unique_driver(bit);
							if (driver != nullptr && dirty.count(driver->name) && combinational.cell_known(driver->type))
								predecessors.insert(driver->name);
						}
			incoming[name] = GetSize(predecessors);
			for (IdString pred : predecessors)
				outgoing[pred].insert(name);
		}
		std::vector<IdString> ready;
		for (const auto &entry : incoming)
			if (entry.second == 0)
				ready.push_back(entry.first);
		while (!ready.empty()) {
			IdString name = ready.back(); ready.pop_back();
			Cell *cell = module->cell(name);
			cells[name] = build_cell_info(cell);
			auto outgoing_it = outgoing.find(name);
			if (outgoing_it != outgoing.end())
				for (IdString successor : outgoing_it->second)
					if (--incoming.at(successor) == 0)
						ready.push_back(successor);
		}
		// 受保护的既有组合环保持边界身份，其函数不会供候选使用。
		for (const auto &entry : incoming)
			if (!cells.count(entry.first)) {
				Cell *cell = module->cell(entry.first);
				CellCostInfo info;
				info.type = cell->type; info.connections = cell->connections();
				info.parameters = cell->parameters; info.attributes = cell->attributes; info.generation = generation;
				cells[entry.first] = info;
				cyclic.insert(entry.first);
			}
		if (reclaim_due())
			collect_functions();
		committed_nodes = GetSize(functions.nodes);
	}

	// 完整原图：全部支持单元按原组合拓扑安装真实成本记录与全模块owners，拓扑次序同时供后继dirty队列复用。
	void refresh()
	{
		// 每次构建从零恢复当前构建必要计数，完整性与资格在安装完成后设置。
		model_complete = false;
		boundary_cells = 0;
		budget_incomplete_cells = 0;
		result_note = MuxResources::Kept;
		// 索引刷新在已准入提交时消费该提交预留中的索引费用，普通初建收取Index费用。
		int64_t index_work = this->index_work();
		if (resources.commit_reserved > 0) {
			resources.account(index_work, MuxResources::Commit);
		} else {
			if (!resources.can_spend(index_work)) {
				resources.result = MuxResources::TotalWorkLimit;
				resources.exhausted = true;
				return;
			}
			resources.account(index_work, MuxResources::Index);
		}
		generation++;
		sigmap.set(module);
		functions.reset();
		drivers.clear(); users.clear(); use_count.clear(); protected_bits.clear(); output_bits.clear();
		cyclic.clear(); cells.clear(); owners.clear(); output_functions.clear();
		for (Wire *wire : module->wires())
			for (SigBit bit : sigmap(wire)) {
				if (!bit.wire)
					continue;
				if (wire->port_input)
					drivers[bit].push_back({IdString(), wire->name, bit.offset});
				if (wire->port_output)
					output_bits.insert(bit);
				if (wire->get_bool_attribute(ID::keep) || wire->get_bool_attribute(ID::lut_keep) || wire->attributes.count(ID::init))
					protected_bits.insert(bit);
			}
		for (Cell *cell : module->cells())
			for (const auto &port : cell->connections()) {
				SigSpec mapped = sigmap(port.second);
				for (int i = 0; i < GetSize(mapped); i++) {
					SigBit bit = mapped[i];
					if (!bit.wire)
						continue;
					if (muxledger_port_input(types, cell, port.first)) {
						users[bit].push_back({cell->name, port.first, i});
						use_count[bit]++;
					}
					if (muxledger_port_output(types, cell, port.first))
						drivers[bit].push_back({cell->name, port.first, i});
				}
			}
		dict<IdString, int> incoming;
		dict<IdString, pool<IdString>> outgoing;
		for (Cell *cell : module->cells())
			if (combinational.cell_known(cell->type))
				incoming[cell->name] = 0;
		for (Cell *cell : module->cells()) {
			if (!incoming.count(cell->name))
				continue;
			pool<IdString> predecessors;
			for (const auto &port : cell->connections())
				if (muxledger_port_input(types, cell, port.first))
					for (SigBit bit : sigmap(port.second)) {
						auto driver_it = drivers.find(bit);
						if (driver_it == drivers.end())
							continue;
						for (const PortBit &driver : driver_it->second)
							if (incoming.count(driver.cell))
								predecessors.insert(driver.cell);
					}
			incoming[cell->name] = GetSize(predecessors);
			for (IdString pred : predecessors)
				outgoing[pred].insert(cell->name);
		}
		std::vector<IdString> ready;
		std::vector<IdString> order;
		for (const auto &entry : incoming)
			if (entry.second == 0)
				ready.push_back(entry.first);
		while (!ready.empty()) {
			IdString name = ready.back(); ready.pop_back();
			order.push_back(name);
			auto outgoing_it = outgoing.find(name);
			if (outgoing_it != outgoing.end())
				for (IdString successor : outgoing_it->second)
					if (--incoming.at(successor) == 0)
						ready.push_back(successor);
		}
		for (const auto &entry : incoming)
			if (entry.second > 0)
				cyclic.insert(entry.first);
		for (Cell *cell : module->cells())
			if (!incoming.count(cell->name) || cyclic.count(cell->name))
				order.push_back(cell->name);
		dict<IdString, int> ranks;
		for (int i = 0; i < GetSize(order); i++)
			ranks[order[i]] = i;
		for (IdString name : order) {
			Cell *cell = module->cell(name);
			functions.growth_headroom = reclaim_bytes();
			cells[cell->name] = build_cell_info(cell);
			cells.at(cell->name).rank = ranks.at(cell->name, -1);
		}
		// 初建完全省去回收：最终roots可达闭包已经intern，只登记初建节点基数。
		committed_nodes = GetSize(functions.nodes);
		collect_nodes = GetSize(functions.nodes);
		invalidated_cells = 0;
		model_complete = budget_incomplete_cells == 0 && !resources.exhausted &&
			(int64_t)cells.size() == module->cells_size();
		log("MUXGRAPH module=%s generation=%llu cells=%d owners=%d boundary=%lld budget_incomplete=%lld model_complete=%d nodes=%d allocated_bytes=%lld live_bytes=%lld peak_bytes=%lld\n",
			log_id(module), (unsigned long long)generation, GetSize(cells),
			GetSize(owners), (long long)boundary_cells, (long long)budget_incomplete_cells,
			(int)model_complete, GetSize(functions.nodes), (long long)functions.allocated_bytes(),
			(long long)resources.live_bytes, (long long)resources.peak_bytes);
	}
};

// 候选保存计数差量与函数引用。预构造完成后禁止修改，提交直接安装prepared。
struct MuxLedger
{
	using Ref = Lut4Functions::Ref;
	using Word = Lut4Functions::Word;
	MuxCostContext &context;
	uint64_t generation;
	dict<SigBit, int> delta;
	pool<IdString> dropped, changed, dead;
	pool<SigBit> freed;
	Word added_roots;
	dict<IdString, MuxCostContext::CellCostInfo> prepared;
	dict<IdString, dict<IdString, SigSpec>> joint_ports;
	bool joint = false;
	bool joint_proof_complete = false;
	MuxResources::Result result = MuxResources::Kept;
	MuxWorkspace workspace;
	bool settled = false, valid = true;
	bool alias_commit = false;
	int64_t removed_gain = 0, added_cost = 0, dead_result = 0, gain = 0;

	MuxLedger(MuxCostContext &context) : context(context), generation(context.generation), workspace(context.resources)
	{
		context.discard_candidate();
		if (!context.resources.can_spend(64) || !context.model_complete) {
			valid = false;
			result = context.model_complete ? MuxResources::CommitReservationLimit : MuxResources::UnsupportedModel;
		} else {
			log_assert(context.resources.charge(64, MuxResources::Candidates));
		}
	}
	~MuxLedger()
	{
		context.resources.commit_reserved = 0;
		if (generation == context.generation)
			context.discard_candidate();
	}
	void editable() const { log_assert(!settled && generation == context.generation); }
	// 局部额度内的费用：正常不足返回未完成，不设置全模块exhausted。
	bool charge_local(int64_t work, MuxResources::Phase phase)
	{
		if (!context.resources.can_spend(work)) {
			result = MuxResources::CommitReservationLimit;
			valid = false;
			return false;
		}
		log_assert(context.resources.charge(work, phase));
		return true;
	}
	void adjust(const SigSpec &sig, int amount)
	{
		for (SigBit bit : context.sigmap(sig)) {
			valid &= context.resources.charge(1);
			if (!bit.wire)
				continue;
			if (!delta.count(bit) && !workspace.reserve(256)) {
				valid = false;
				result = MuxResources::WorkspaceLimit;
				return;
			}
			delta[bit] += amount;
			log_assert(context.use_count.at(bit, 0) + delta.at(bit, 0) >= 0);
			if (amount < 0)
				freed.insert(bit);
		}
	}
	bool check(Cell *cell)
	{
		auto it = context.cells.find(cell->name);
		log_assert(it != context.cells.end() && it->second.generation <= generation);
		const auto &info = it->second;
		log_assert(info.type == cell->type && info.connections == cell->connections() &&
			info.parameters == cell->parameters && info.attributes == cell->attributes);
		if (!info.supported) {
			valid = false;
			result = info.result;
		} else if (!context.mutable_cell(cell)) {
			valid = false;
			result = MuxResources::UnsupportedModel;
		}
		return valid;
	}
	void release_inputs(Cell *cell)
	{
		for (const auto &port : cell->connections())
			if (muxledger_port_input(context.types, cell, port.first))
				adjust(port.second, -1);
	}
	void drop_cell(Cell *cell)
	{
		editable();
		log_assert(!changed.count(cell->name) && dropped.insert(cell->name).second);
		check(cell);
		release_inputs(cell);
	}
	void replace_outputs(Cell *cell, const Word &outputs)
	{
		editable();
		log_assert(!dropped.count(cell->name) && changed.insert(cell->name).second);
		check(cell);
		release_inputs(cell);
		add_outputs(cell->getPort(ID::Y), outputs);
	}
	void acquire(const SigSpec &sig)
	{
		editable();
		adjust(sig, 1);
	}
	void add_outputs(const SigSpec &destination, const Word &outputs)
	{
		editable();
		log_assert(GetSize(destination) == GetSize(outputs));
		Word active;
		dict<SigBit, Ref> identities;
		for (int i = 0; i < GetSize(destination); i++) {
			SigBit bit = context.sigmap(destination[i]);
			if (identities.count(bit) && identities.at(bit) != outputs[i]) {
				valid = false;
				result = MuxResources::AliasConflict;
			}
			identities[bit] = outputs[i];
			if (context.live(destination[i]))
				active.push_back(outputs[i]);
		}
		added_roots.insert(added_roots.end(), active.begin(), active.end());
		valid &= workspace.reserve(GetSize(active) * 32);
		valid &= !context.functions.exhausted;
	}
	bool cell_dead(Cell *cell) const
	{
		if (!context.module->selected(cell) || !context.mutable_cell(cell) || !context.cells.at(cell->name).supported)
			return false;
		bool output = false;
		for (const auto &port : cell->connections())
			if (muxledger_port_output(context.types, cell, port.first))
				for (SigBit bit : context.sigmap(port.second)) {
					if (!bit.wire)
						continue;
					output = true;
					if (context.output_bits.count(bit) || context.protected_bits.count(bit) ||
						context.use_count.at(bit, 0) + delta.at(bit, 0) > 0)
						return false;
				}
		return output;
	}
	// 多个端口属于同一次变更，组合后继采用本次变更的真实新前驱函数。
	void replace_joint(const dict<IdString, dict<IdString, SigSpec>> &ports)
	{
		editable();
		log_assert(!joint && !ports.empty());
		joint = true;
		joint_ports = ports;
		for (const auto &entry : joint_ports) {
			Cell *cell = context.module->cell(entry.first);
			int64_t copy_work = 32;
			for (const auto &port : entry.second) copy_work += GetSize(port.second) * 8;
			valid &= charge_local(copy_work, MuxResources::Candidates);
			log_assert(cell != nullptr && changed.insert(entry.first).second && entry.second.count(ID::Y));
			check(cell);
			release_inputs(cell);
			for (const auto &port : entry.second)
				if (muxledger_port_input(context.types, cell, port.first))
					adjust(port.second, 1);
		}
	}
	// 逐输出活跃性：旧端口使用当前真实use_count，新端口使用use_count加本次差量。
	std::vector<bool> liveness(const SigSpec &y, bool planned) const
	{
		std::vector<bool> result;
		for (SigBit bit : context.sigmap(y)) {
			int uses = context.use_count.at(bit, 0) + (planned ? delta.at(bit, 0) : 0);
			bool live = bit.wire && (context.output_bits.count(bit) || context.protected_bits.count(bit) || uses > 0);
			result.push_back(live);
		}
		return result;
	}
	// 输出别名身份：Y端口连到的实际位序列。
	std::vector<SigBit> aliases(const dict<IdString, SigSpec> &connections) const
	{
		std::vector<SigBit> result;
		if (!connections.count(ID::Y))
			return result;
		for (SigBit bit : context.sigmap(connections.at(ID::Y)))
			result.push_back(bit);
		return result;
	}

	// 准确预构造：真实dirty起点按本模块组合拓扑推进，只有逐输出Ref/活跃性/别名身份改变才向使用者传播。
	// 死亡闭包成员同样进入prepared，owners差量随之完整结算。
	bool prepare_joint()
	{
		log_assert(joint && context.planned_outputs == nullptr);
		if (!valid) { settled = true; return false; }
		pool<IdString> dirty = changed;
		std::vector<SigBit> todo(freed.begin(), freed.end());
		pool<SigBit> seen;
		while (!todo.empty()) {
			if (!charge_local(1, MuxResources::Candidates))
				return false;
			SigBit bit = todo.back(); todo.pop_back();
			if (!seen.insert(bit).second)
				continue;
			auto drivers = context.drivers.find(bit);
			if (drivers == context.drivers.end())
				continue;
			for (const auto &driver : drivers->second) {
				if (driver.cell.empty() || changed.count(driver.cell) || dead.count(driver.cell))
					continue;
				Cell *cell = context.module->cell(driver.cell);
				log_assert(cell != nullptr);
				if (!cell_dead(cell))
					continue;
				log_assert(dead.insert(driver.cell).second);
				for (const auto &port : cell->connections())
					if (muxledger_port_input(context.types, cell, port.first)) {
						adjust(port.second, -1);
						for (SigBit input : context.sigmap(port.second))
							if (input.wire) { seen.erase(input); todo.push_back(input); }
					}
			}
		}
		for (const auto &entry : delta)
			if ((context.use_count.at(entry.first, 0) > 0) != (context.use_count.at(entry.first, 0) + entry.second > 0)) {
				Cell *driver = context.unique_driver(entry.first);
				if (driver != nullptr)
					dirty.insert(driver->name);
			}
		// 真实dirty起点按本模块组合拓扑rank有序推进；只有输出身份改变的边继续加入直接使用者。
		auto successors_of = [&](Cell *cell, pool<IdString> &out) {
			if (cell == nullptr || !context.combinational.cell_known(cell->type))
				return;
			for (const auto &port : cell->connections())
				if (muxledger_port_output(context.types, cell, port.first))
					for (SigBit bit : context.sigmap(port.second)) {
						auto users = context.users.find(bit);
						if (users == context.users.end())
							continue;
						for (const MuxPortBit &user : users->second)
							if (context.cells.count(user.cell))
								out.insert(user.cell);
					}
		};
		auto rank_order = [&](IdString left, IdString right) {
			int left_rank = context.cells.at(left).rank;
			int right_rank = context.cells.at(right).rank;
			return left_rank != right_rank ? left_rank < right_rank : left < right;
		};
		std::vector<IdString> pending(dirty.begin(), dirty.end());
		std::sort(pending.begin(), pending.end(), rank_order);
		dict<SigBit, Ref> outputs;
		pool<IdString> changed_output;
		context.planned_outputs = &outputs;
		while (!pending.empty()) {
			IdString name = pending.front();
			pending.erase(pending.begin());
			if (prepared.count(name))
				continue;
			Cell *cell = context.module->cell(name);
			if (cell == nullptr)
				continue;
			if (!charge_local(MuxCostContext::snapshot_bytes(cell), MuxResources::Candidates))
				break;
			MuxCostContext::CellCostInfo info;
			info.type = cell->type;
			info.connections = joint_ports.count(name) ? joint_ports.at(name) : cell->connections();
			info.parameters = cell->parameters; info.attributes = cell->attributes; info.generation = generation;
			info.rank = context.cells.at(name).rank;
			if (dead.count(name)) {
				// 真实死亡：输出消失、输入释放，owners差量在prepared中完整结算。
				info.supported = false;
				info.removed = true;
				info.result = MuxResources::Kept;
				changed_output.insert(name);
			} else {
				const auto &old = context.cells.at(name);
				// 顺序单元、未知接口与保护对象没有组合Y输出，保持原有自由身份与外部观察。
				bool combinable = old.supported && info.connections.count(ID::Y) != 0 &&
					muxledger_port_output(context.types, cell, ID::Y);
				if (!combinable) {
					prepared[name] = old;
					continue;
				}
				std::vector<bool> old_live = liveness(old.connections.at(ID::Y), false);
				std::vector<bool> new_live = liveness(info.connections.at(ID::Y), true);
				std::vector<SigBit> old_alias = aliases(old.connections);
				std::vector<SigBit> new_alias = aliases(info.connections);
				bool alias_conflict = false;
				context.result_note = MuxResources::Kept;
				bool built = context.model(cell, info.connections, info.supported, info.outputs,
					&info.input_functions, &alias_conflict);
				info.result = alias_conflict ? MuxResources::AliasConflict :
					info.supported ? MuxResources::Kept : context.result_note;
				if (!built)
					result = info.result;
				valid &= built;
				Word active;
				if (built)
					for (int i = 0; i < GetSize(info.outputs); i++) {
						SigBit bit = context.sigmap(info.connections.at(ID::Y)[i]);
						if (context.output_bits.count(bit) || context.protected_bits.count(bit) ||
							context.use_count.at(bit, 0) + delta.at(bit, 0) > 0 || cell->has_keep_attr())
							active.push_back(info.outputs[i]);
						if (context.mutable_cell(cell)) {
							if (outputs.count(bit) && outputs.at(bit) != info.outputs[i]) {
								valid = false;
								result = MuxResources::AliasConflict;
							}
							outputs[bit] = info.outputs[i];
						}
					}
				info.dependencies = context.functions.dependencies(active, &info.input_functions);
				added_roots.insert(added_roots.end(), active.begin(), active.end());
				bool changed_outputs = !built || info.outputs != old.outputs;
				bool alias_changed = old_alias != new_alias;
				bool alive_changed = old_live != new_live;
				if (changed_outputs || alias_changed || alive_changed)
					changed_output.insert(name);
			}
			prepared[name] = std::move(info);
			if (!changed_output.count(name))
				continue;
			pool<IdString> successors;
			successors_of(cell, successors);
			for (IdString successor : successors)
				if (dirty.insert(successor).second)
					pending.push_back(successor);
			std::sort(pending.begin(), pending.end(), rank_order);
		}
		context.planned_outputs = nullptr;
		bool complete_joint = true;
		for (IdString name : dirty)
			if (!prepared.count(name))
				complete_joint = false;
		if (!complete_joint) {
			valid = false;
			if (result == MuxResources::Kept)
				result = MuxResources::WorkspaceLimit;
		}
		if (!valid) { settled = true; return false; }
		dict<Ref, int> owner_delta;
		pool<Ref> dead_refs;
		for (const auto &entry : prepared) {
			const auto &old = context.cells.at(entry.first);
			for (Ref ref : old.dependencies) {
				owner_delta[ref]--;
				if (entry.second.removed)
					dead_refs.insert(ref);
			}
			for (Ref ref : entry.second.dependencies)
				owner_delta[ref]++;
		}
		for (const auto &entry : owner_delta) {
			int before = context.owners.at(entry.first, 0), after = before + entry.second;
			log_assert(after >= 0);
			if (before > 0 && after == 0) {
				if (dead_refs.count(entry.first))
					dead_result++;
				else
					removed_gain++;
			}
			if (before == 0 && after > 0)
				added_cost++;
		}
		gain = removed_gain + dead_result - added_cost;
		valid &= !context.functions.exhausted;
		if (!valid && result == MuxResources::Kept)
			result = MuxResources::UnsupportedModel;
		settled = true;
		log("MUXJOINTCOST module=%s changed=%d affected=%d dead=%d removed=%lld dead_gain=%lld added=%lld gain=%lld live_bytes=%lld\n",
			log_id(context.module), GetSize(changed), GetSize(prepared), GetSize(dead),
			(long long)removed_gain, (long long)dead_result, (long long)added_cost,
			(long long)gain, (long long)context.resources.live_bytes);
		return valid;
	}

	// 提交直接安装prepared与真实端口索引，不重新进行全部TFO建图。
	void commit_joint()
	{
		log_assert(joint && joint_proof_complete && settled && valid && generation == context.generation &&
			context.resources.finish_work != nullptr);
		for (const auto &entry : joint_ports) {
			Cell *cell = context.module->cell(entry.first);
			log_assert(cell != nullptr);
			const auto &old = context.cells.at(entry.first);
			log_assert(cell->type == old.type && cell->connections() == old.connections &&
				cell->parameters == old.parameters && cell->attributes == old.attributes);
		}
		for (const auto &entry : joint_ports) {
			Cell *cell = context.module->cell(entry.first);
			for (const auto &port : context.cells.at(entry.first).connections)
				if (muxledger_port_input(context.types, cell, port.first))
					for (SigBit bit : context.sigmap(port.second)) {
						if (!bit.wire) continue;
						auto &users = context.users.at(bit);
						users.erase(std::remove_if(users.begin(), users.end(),
							[&](const MuxCostContext::PortBit &user) { return user.cell == entry.first; }), users.end());
						context.use_count[bit] = GetSize(users);
					}
			for (const auto &port : entry.second) {
				log_assert(cell->hasPort(port.first) && GetSize(cell->getPort(port.first)) == GetSize(port.second));
				cell->setPort(port.first, port.second);
				if (!muxledger_port_input(context.types, cell, port.first)) continue;
				SigSpec mapped = context.sigmap(port.second);
				for (int i = 0; i < GetSize(mapped); i++)
					if (mapped[i].wire) {
						context.users[mapped[i]].push_back({entry.first, port.first, i});
						context.use_count[mapped[i]]++;
					}
			}
			int64_t port_work = 32;
			for (const auto &port : context.cells.at(entry.first).connections) port_work += GetSize(port.second) * 8;
			for (const auto &port : entry.second) port_work += GetSize(port.second) * 8;
			log_assert(context.resources.charge(port_work, MuxResources::Commit));
		}
		for (IdString name : dead) {
			Cell *cell = context.module->cell(name);
			log_assert(cell != nullptr && context.module->selected(cell));
			for (const auto &port : cell->connections())
				for (SigBit bit : context.sigmap(port.second)) {
					if (!bit.wire) continue;
					if (muxledger_port_input(context.types, cell, port.first)) {
						auto &users = context.users.at(bit);
						users.erase(std::remove_if(users.begin(), users.end(),
							[&](const MuxCostContext::PortBit &user) { return user.cell == name; }), users.end());
						context.use_count[bit] = GetSize(users);
					}
					if (muxledger_port_output(context.types, cell, port.first)) {
						auto &drivers = context.drivers.at(bit);
						drivers.erase(std::remove_if(drivers.begin(), drivers.end(),
							[&](const MuxCostContext::PortBit &driver) { return driver.cell == name; }), drivers.end());
						context.output_functions.erase(bit);
					}
				}
			context.module->remove(cell);
			log_assert(context.resources.charge(32 + GetSize(context.cells.at(name).dependencies) * 8, MuxResources::Commit));
		}
		context.generation++;
		for (auto &entry : prepared) {
			log_assert(context.resources.charge(32 + (GetSize(context.cells.at(entry.first).dependencies) +
				GetSize(entry.second.dependencies)) * 8, MuxResources::Commit));
			for (Ref ref : context.cells.at(entry.first).dependencies) {
				log_assert(context.owners.at(ref, 0) > 0);
				context.owners.at(ref)--;
			}
			for (Ref ref : entry.second.dependencies)
				context.owners[ref]++;
			if (entry.second.removed) {
				// 死亡单元的drivers、users与output_functions已经在死亡循环中清理。
				context.cells.erase(entry.first);
				continue;
			}
			Cell *live_cell = context.module->cell(entry.first);
			bool mutable_cell = live_cell != nullptr && context.mutable_cell(live_cell);
			if (mutable_cell)
				for (const auto &old_port : context.cells.at(entry.first).connections)
					if (muxledger_port_output(context.types, live_cell, old_port.first))
						for (SigBit bit : context.sigmap(old_port.second))
							context.output_functions.erase(bit);
			if (entry.second.supported && mutable_cell)
				for (int i = 0; i < GetSize(entry.second.outputs); i++)
					context.output_functions[context.sigmap(entry.second.connections.at(ID::Y)[i])] = entry.second.outputs[i];
			entry.second.generation = context.generation;
			context.cells[entry.first] = std::move(entry.second);
		}
		// prepared装入Module并清理全部候选Ref之后才允许回收。
		prepared.clear();
		joint_ports.clear();
		// 小提交之间保留真实失效累计，与节点增长共同决定轻量回收。
		context.invalidated_cells += GetSize(changed) + GetSize(dead);
		context.committed_nodes = GetSize(context.functions.nodes);
		if (!context.reclaim_due()) return;
		Word retained = added_roots;
		context.collect_functions(&retained);
	}

	bool settle()
	{
		log_assert(generation == context.generation);
		if (settled)
			return valid;
		editable();
		if (joint)
			return prepare_joint();
		if (!valid || context.resources.exhausted) {
			valid = false;
			settled = true;
			return false;
		}
		std::vector<SigBit> todo(freed.begin(), freed.end());
		pool<SigBit> seen;
		while (!todo.empty()) {
			if (!charge_local(1, MuxResources::Candidates))
				break;
			SigBit bit = todo.back(); todo.pop_back();
			if (!seen.insert(bit).second)
				continue;
			auto driver_it = context.drivers.find(bit);
			if (driver_it == context.drivers.end())
				continue;
			for (const auto &driver : driver_it->second) {
				if (driver.cell.empty() || dropped.count(driver.cell) || changed.count(driver.cell) || dead.count(driver.cell))
					continue;
				Cell *cell = context.module->cell(driver.cell);
				log_assert(cell != nullptr);
				if (!cell_dead(cell))
					continue;
				dead.insert(driver.cell);
				for (const auto &port : cell->connections())
					if (muxledger_port_input(context.types, cell, port.first)) {
						adjust(port.second, -1);
						for (SigBit input : context.sigmap(port.second))
							if (input.wire) {
								seen.erase(input);
								todo.push_back(input);
							}
					}
			}
		}
		dict<Ref, int> changes;
		pool<Ref> explicit_refs, dead_refs;
		for (IdString name : dropped)
			for (Ref ref : context.cells.at(name).dependencies) {
				if (!workspace.reserve(256)) { valid = false; settled = true; return false; }
				changes[ref]--;
				explicit_refs.insert(ref);
			}
		for (IdString name : changed)
			for (Ref ref : context.cells.at(name).dependencies) {
				if (!workspace.reserve(256)) { valid = false; settled = true; return false; }
				changes[ref]--;
				explicit_refs.insert(ref);
			}
		for (IdString name : dead)
			for (Ref ref : context.cells.at(name).dependencies) {
				if (!workspace.reserve(256)) { valid = false; settled = true; return false; }
				changes[ref]--;
				dead_refs.insert(ref);
			}
		Word pending_roots = added_roots;
		pool<Ref> visited;
		while (!pending_roots.empty()) {
			if (!charge_local(1, MuxResources::Reclaim))
				break;
			Ref ref = pending_roots.back(); pending_roots.pop_back();
			if (mux_is_global_entry(ref) || ref < 4)
				continue;
			const auto &node = context.functions.nodes[ref];
			if (node.leaf || !visited.insert(ref).second || context.owners.at(ref, 0) + changes.at(ref, 0) > 0)
				continue;
			if (!workspace.reserve(256)) { valid = false; settled = true; return false; }
			changes[ref]++;
			for (int i = 0; i < node.arity; i++)
				pending_roots.push_back(node.inputs[i]);
		}
		for (const auto &entry : changes) {
			int before = context.owners.at(entry.first, 0), after = before + entry.second;
			log_assert(after >= 0);
			if (before > 0 && after == 0) {
				if (dead_refs.count(entry.first))
					dead_result++;
				else if (explicit_refs.count(entry.first))
					removed_gain++;
			}
			if (before == 0 && after > 0)
				added_cost++;
		}
		gain = removed_gain + dead_result - added_cost;
		valid &= !context.functions.exhausted;
		if (valid) {
			pool<IdString> dirty = dropped;
			for (IdString name : changed)
				dirty.insert(name);
			for (const auto &entry : delta) {
				if ((context.use_count.at(entry.first, 0) > 0) == (context.use_count.at(entry.first, 0) + entry.second > 0))
					continue;
				Cell *driver = context.unique_driver(entry.first);
				if (driver != nullptr)
					dirty.insert(driver->name);
			}
			std::vector<IdString> todo_cells(dirty.begin(), dirty.end());
			int64_t commit_work = 1024;
			for (int i = 0; i < GetSize(todo_cells); i++) {
				const auto &info = context.cells.at(todo_cells[i]);
				commit_work += 128;
				for (const auto &port : info.connections)
					commit_work += GetSize(port.second) * 16;
				if (info.connections.count(ID::Y))
					for (SigBit bit : context.sigmap(info.connections.at(ID::Y))) {
						auto users = context.users.find(bit);
						if (users != context.users.end())
							for (const auto &user : users->second)
								if (dirty.insert(user.cell).second)
									todo_cells.push_back(user.cell);
					}
			}
			int64_t added_users = 0;
			for (const auto &entry : delta)
				added_users += std::max(entry.second, 0);
			commit_work += added_users * std::max(GetSize(added_roots), 1) * 32;
			if (alias_commit)
				commit_work += context.index_work();
			valid &= context.resources.reserve_commit(commit_work);
		}
		settled = true;
		return valid;
	}
};

YOSYS_NAMESPACE_END
#endif
