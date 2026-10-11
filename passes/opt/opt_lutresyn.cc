#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "opt_lut4_mapping.h"
#include "opt_lut_ff_boundary.h"

#include <array>
#include <map>
#include <set>
#include <deque>
#include <tuple>
#include <cstdint>
#include <optional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct LutResynTable
{
	std::array<uint64_t, 16> words {};
	bool get(int i) const {
		log_assert(i >= 0 && i < 1024);
		return (words[i / 64] >> (i % 64)) & 1;
	}
	void set(int i, bool value) {
		log_assert(i >= 0 && i < 1024);
		if (value) words[i / 64] |= uint64_t(1) << (i % 64);
		else words[i / 64] &= ~(uint64_t(1) << (i % 64));
	}
	bool operator<(const LutResynTable &other) const { return words < other.words; }
	bool operator==(const LutResynTable &other) const { return words == other.words; }
};

static int lutresyn_count(unsigned mask)
{
	int result = 0;
	for (; mask; mask &= mask - 1) result++;
	return result;
}

static vector<int> lutresyn_positions(unsigned mask)
{
	vector<int> result;
	for (int i = 0; i < 10; i++)
		if (mask & (1u << i)) result.push_back(i);
	return result;
}

static unsigned lutresyn_deposit(unsigned value, const vector<int> &positions)
{
	unsigned result = 0;
	for (int i = 0; i < GetSize(positions); i++)
		result |= ((value >> i) & 1u) << positions[i];
	return result;
}

static unsigned lutresyn_project(unsigned value, const vector<int> &positions)
{
	unsigned result = 0;
	for (int i = 0; i < GetSize(positions); i++)
		result |= ((value >> positions[i]) & 1u) << i;
	return result;
}

// 真值表的输入使用排序后的独立信号，删除没有实际影响的 support。
template<typename T> static void lutresyn_reduce(vector<T> &inputs, LutResynTable &table)
{
	log_assert(GetSize(inputs) <= 10);
	vector<int> support;
	for (int i = 0; i < GetSize(inputs); i++) {
		bool relevant = false;
		for (int a = 0; a < (1 << GetSize(inputs)); a++)
			if (table.get(a) != table.get(a ^ (1 << i))) { relevant = true; break; }
		if (relevant) support.push_back(i);
	}
	vector<T> reduced_inputs;
	for (int i : support) reduced_inputs.push_back(inputs[i]);
	LutResynTable reduced_table;
	for (int a = 0; a < (1 << GetSize(support)); a++)
		reduced_table.set(a, table.get(lutresyn_deposit(a, support)));
	inputs = std::move(reduced_inputs);
	table = reduced_table;
}

struct LutResynFunction
{
	vector<SigBit> inputs;
	LutResynTable table;
	bool operator<(const LutResynFunction &other) const {
		return std::tie(inputs, table) < std::tie(other.inputs, other.table);
	}
};

struct LutResynOptions
{
	int max_cells = 32, max_cuts = 32, max_problems = 4096;
	int max_joint = 8, max_neighbors = 12, max_dependencies = 4096;
	int max_work = 16000000, max_memory = 64;
	int64_t memory_bytes = -1;
	bool dry_run = false;
};

struct LutResynResources
{
	int64_t work = 0, memory = 0, peak_memory = 0;
	int64_t work_limit, memory_limit;
	bool stopped = false;
	bool local_stopped = false;
	int64_t local_limit = -1;
	int64_t commit_credit = 0;
	explicit LutResynResources(const LutResynOptions &options) :
		work_limit(options.max_work), memory_limit(options.memory_bytes < 0 ? int64_t(options.max_memory) * 1024 * 1024 : options.memory_bytes) {}
	bool spend(int64_t amount) {
		log_assert(amount >= 0);
		if (stopped) return false;
		if (local_limit >= 0 && amount > local_limit - work - commit_credit) { local_stopped = true; return false; }
		if (amount > work_limit - work - commit_credit) { stopped = true; return false; }
		work += amount;
		return true;
	}
	bool reserve(int64_t amount) {
		log_assert(amount >= 0);
		if (stopped) return false;
		if (amount > memory_limit - memory) { stopped = true; return false; }
		memory += amount;
		peak_memory = std::max(peak_memory, memory);
		return true;
	}
	void release(int64_t amount) {
		log_assert(amount >= 0 && amount <= memory);
		memory -= amount;
	}
	bool hold_commit(int64_t amount) {
		log_assert(amount >= 0);
		if (amount > work_limit - work || (local_limit >= 0 && amount > local_limit - work)) return false;
		commit_credit = amount;
		return true;
	}
	void consume_commit() {
		log_assert(commit_credit <= work_limit - work);
		work += commit_credit; commit_credit = 0;
	}
};

struct LutResynReservation
{
	LutResynResources &resources;
	int64_t bytes = 0;
	explicit LutResynReservation(LutResynResources &resources) : resources(resources) {}
	bool reserve(int64_t amount) {
		if (!resources.reserve(amount)) return false;
		bytes += amount;
		return true;
	}
	~LutResynReservation() { resources.release(bytes); }
};

struct LutResynRegion
{
	std::set<IdString> nodes;
	vector<IdString> roots;
	vector<SigBit> boundary;
	vector<IdString> order;
};

struct LutResynRegionKey
{
	std::set<IdString> nodes;
	vector<IdString> roots;
	bool operator<(const LutResynRegionKey &other) const {
		return std::tie(nodes, roots) < std::tie(other.nodes, other.roots);
	}
};

struct LutResynPrepared
{
	bool valid = false;
	LutResynRegion region;
};

struct LutResynProof
{
	const LutResynRegion &region;
	std::set<IdString> independent, dependent;
	int examined = 0;
	explicit LutResynProof(const LutResynRegion &region) : region(region) {}
};

struct LutResynRef
{
	SigBit bit;
	int node = -1;
	LutResynRef() = default;
	explicit LutResynRef(SigBit bit) : bit(bit) {}
	explicit LutResynRef(int node) : node(node) {}
	bool operator<(const LutResynRef &other) const { return std::tie(node, bit) < std::tie(other.node, other.bit); }
	bool operator==(const LutResynRef &other) const { return node == other.node && bit == other.bit; }
};

struct LutResynPlannedFunction
{
	vector<LutResynRef> inputs;
	LutResynTable table;
	bool operator<(const LutResynPlannedFunction &other) const {
		return std::tie(inputs, table) < std::tie(other.inputs, other.table);
	}
};

struct LutResynPlan
{
	vector<LutResynPlannedFunction> nodes;
	vector<LutResynRef> outputs;
	std::map<LutResynPlannedFunction, LutResynRef> functions;
	std::set<int> needed;
	std::set<IdString> deleting, retained;
	vector<bool> preserve;
	bool proven = false;
	int gain = 0;
	void collect(LutResynRef ref) {
		if (ref.node < 0 || !needed.insert(ref.node).second) return;
		for (auto input : nodes.at(ref.node).inputs) collect(input);
	}
	int cost() {
		needed.clear();
		for (auto output : outputs) collect(output);
		return GetSize(needed);
	}
};

static SigBit lutresyn_canonical(const SigMap &sigmap, std::map<SigBit, SigBit> &redirects, SigBit bit)
{
	bit = sigmap(bit);
	SigBit original = bit;
	auto it = redirects.find(bit);
	while (it != redirects.end()) { bit = it->second; it = redirects.find(bit); }
	it = redirects.find(original);
	while (it != redirects.end() && it->second != bit) {
		SigBit next = it->second;
		it->second = bit;
		it = redirects.find(next);
	}
	return bit;
}

static Const lutresyn_logic_table(Cell *cell)
{
	return cell->type == ID($lut) ? cell->getParam(ID::LUT) : Const(1, 2);
}

// 两种重综合使用相同的四输入 LUT 与一位 NOT 接口。
static bool lutresyn_lut_shape(Cell *cell)
{
	if (!cell || !cell->type.in(ID($lut), ID($not), ID($_NOT_))) return false;
	bool inversion = cell->type != ID($lut);
	if (GetSize(cell->connections()) != 2 || !cell->hasPort(ID::A) || !cell->hasPort(ID::Y) ||
	    GetSize(cell->getPort(ID::Y)) != 1) return false;
	if (!inversion && (!cell->hasParam(ID::WIDTH) || !cell->hasParam(ID::LUT) ||
	    !cell->getParam(ID::WIDTH).is_fully_def())) return false;
	int width = inversion ? 1 : cell->getParam(ID::WIDTH).as_int();
	if (width < 0 || width > 4 || GetSize(cell->getPort(ID::A)) != width) return false;
	if (cell->type == ID($not) && (!cell->hasParam(ID::A_WIDTH) || !cell->hasParam(ID::Y_WIDTH) ||
	    !cell->getParam(ID::A_WIDTH).is_fully_def() || !cell->getParam(ID::Y_WIDTH).is_fully_def() ||
	    cell->getParam(ID::A_WIDTH).as_int() != 1 || cell->getParam(ID::Y_WIDTH).as_int() != 1)) return false;
	Const table = lutresyn_logic_table(cell);
	if (GetSize(table) != (1 << width)) return false;
	for (auto value : table)
		if (value != State::S0 && value != State::S1) return false;
	return true;
}

template<typename Worker> static void lutresyn_index_add(Worker &worker, Cell *cell)
{
	auto &inputs = worker.cell_inputs[cell->name], &outputs = worker.cell_outputs[cell->name];
	bool known = worker.types.cell_known(cell->type);
	for (auto &connection : cell->connections()) {
		bool input = !known || worker.types.cell_input(cell->type, connection.first);
		bool output = !known || worker.types.cell_output(cell->type, connection.first);
		for (auto bit : connection.second) {
			bit = worker.canonical(bit);
			if (!bit.wire) continue;
			if (input) {
				inputs.insert(bit); worker.users[bit].insert(cell->name);
			}
			if (output) {
				outputs.insert(bit); worker.drivers[bit].insert(cell->name);
				worker.driver_counts[bit]++; worker.cell_driver_counts[cell->name][bit]++;
			}
		}
	}
}

template<typename Worker> static void lutresyn_index_erase(Worker &worker, IdString name)
{
	for (auto bit : worker.cell_inputs.at(name)) {
		auto it = worker.users.find(bit);
		log_assert(it != worker.users.end());
		it->second.erase(name);
		if (it->second.empty()) worker.users.erase(it);
	}
	for (auto bit : worker.cell_outputs.at(name)) {
		auto it = worker.drivers.find(bit);
		log_assert(it != worker.drivers.end());
		it->second.erase(name);
		if (it->second.empty()) worker.drivers.erase(it);
	}
	auto counts = worker.cell_driver_counts.find(name);
	if (counts != worker.cell_driver_counts.end()) {
		for (auto entry : counts->second) {
			auto it = worker.driver_counts.find(entry.first);
			log_assert(it != worker.driver_counts.end() && it->second >= entry.second);
			it->second -= entry.second;
			if (it->second == 0) worker.driver_counts.erase(it);
		}
		worker.cell_driver_counts.erase(counts);
	}
	worker.cell_inputs.erase(name); worker.cell_outputs.erase(name);
}

struct LutResynWorker
{
	Module *module;
	SigMap sigmap;
	CellTypes types;
	bool native_dffeas;
	LutResynOptions options;
	LutResynResources resources;
	mutable std::map<SigBit, SigBit> redirects;
	std::map<SigBit, std::set<IdString>> drivers, users;
	std::map<IdString, std::set<SigBit>> cell_inputs, cell_outputs;
	std::map<SigBit, int> driver_counts, input_driver_counts;
	std::map<IdString, std::map<SigBit, int>> cell_driver_counts;
	std::set<SigBit> ports_in, ports_out, protected_bits;
	std::set<IdString> unsafe, pending;
	std::map<LutResynFunction, std::set<IdString>> function_cache;
	std::map<IdString, LutResynFunction> cached_cells;
	std::map<LutResynRegionKey, LutResynPrepared> region_cache;
	std::map<std::pair<vector<IdString>, int>, vector<LutResynRegion>> cut_cache;
	int64_t cycle_memory = 0;
	int64_t prepared_hits = 0, cut_hits = 0, problem_hits = 0, proof_hits = 0;
	int64_t analyzed = 0, accepted = 0, removed = 0;
	int64_t dictionary_functions = 0, complete_joint_plans = 0;
	int64_t enumeration_proofs = 0, external_outputs = 0, single_bridge_plans = 0, two_bridge_plans = 0;
	int64_t retained_cells = 0, new_cells_count = 0, care_regions = 0, native_ff_count = 0;
	int64_t dictionary_work = 0, address_work = 0, price_work = 0, proof_work = 0, environment_work = 0;
	int64_t problem_memory = 0;
	int64_t commit_work = 0, sorting_work = 0;
	int64_t eligible_original = 0, cycle_original = 0;

	SigBit canonical(SigBit bit) const {
		return lutresyn_canonical(sigmap, redirects, bit);
	}

	bool sequential(Cell *cell) const {
		return LutFfBoundary::sequential(cell, native_dffeas);
	}

	void index_add(Cell *cell) {
		lutresyn_index_add(*this, cell);
	}

	void cache_erase(IdString name) {
		auto it = cached_cells.find(name);
		if (it == cached_cells.end()) return;
		auto f = function_cache.find(it->second);
		log_assert(f != function_cache.end());
		f->second.erase(name);
		if (f->second.empty()) function_cache.erase(f);
		cached_cells.erase(it);
	}

	void index_erase(IdString name) {
		cache_erase(name);
		lutresyn_index_erase(*this, name);
	}

	Cell *unique_driver(SigBit bit) const {
		bit = canonical(bit);
		if (!bit.wire || ports_in.count(bit)) return nullptr;
		auto it = drivers.find(bit);
		if (it == drivers.end() || it->second.size() != 1 || driver_counts.at(bit) != 1) return nullptr;
		return module->cell(*it->second.begin());
	}

	bool valid_lut(Cell *cell, bool deleting) const {
		if (!cell || unsafe.count(cell->name)) return false;
		if (!lutresyn_lut_shape(cell)) return false;
		for (auto bit : cell->getPort(ID::A)) {
			bit = canonical(bit);
			if (!bit.wire && bit != State::S0 && bit != State::S1) return false;
			if (bit.wire) {
				auto it = driver_counts.find(bit), input_it = input_driver_counts.find(bit);
				int count = (it == driver_counts.end() ? 0 : it->second) +
				            (input_it == input_driver_counts.end() ? 0 : input_it->second);
				if (count > 1) return false;
			}
		}
		SigBit output = canonical(cell->getPort(ID::Y)[0]);
		if (unique_driver(output) != cell) return false;
		if (deleting && (!module->selected(cell) || cell->has_keep_attr() || cell->get_bool_attribute(ID::lut_keep) ||
		    cell->attributes.count(ID::init) || protected_bits.count(output)))
			return false;
		return true;
	}

	LutResynFunction cell_function(Cell *cell) const {
		LutResynFunction f;
		vector<SigBit> raw;
		for (auto bit : cell->getPort(ID::A)) {
			bit = canonical(bit); raw.push_back(bit);
			if (bit.wire) f.inputs.push_back(bit);
		}
		std::sort(f.inputs.begin(), f.inputs.end());
		f.inputs.erase(std::unique(f.inputs.begin(), f.inputs.end()), f.inputs.end());
		Const table = lutresyn_logic_table(cell);
		for (int a = 0; a < (1 << GetSize(f.inputs)); a++) {
			int address = 0;
			for (int i = 0; i < GetSize(raw); i++) {
				bool value = raw[i] == State::S1;
				if (raw[i].wire) value = (a >> (std::lower_bound(f.inputs.begin(), f.inputs.end(), raw[i]) - f.inputs.begin())) & 1;
				address |= int(value) << i;
			}
			f.table.set(a, table[address] == State::S1);
		}
		lutresyn_reduce(f.inputs, f.table);
		return f;
	}

	void cache_add(Cell *cell) {
		if (!valid_lut(cell, false)) return;
		auto f = cell_function(cell);
		function_cache[f].insert(cell->name);
		cached_cells.emplace(cell->name, std::move(f));
	}

	// Kahn 遍历把组合环及其后继排除，寄存器输出作为独立边界。
	void find_unsafe() {
		std::map<IdString, int> remaining;
		std::map<IdString, std::set<IdString>> successors;
		std::deque<IdString> queue;
		for (auto cell : module->cells()) {
			if (sequential(cell)) continue;
			std::set<IdString> predecessors;
			for (auto bit : cell_inputs.at(cell->name))
				for (auto name : drivers[bit]) {
					Cell *driver = module->cell(name);
					if (!sequential(driver)) predecessors.insert(name);
				}
			remaining[cell->name] = GetSize(predecessors);
			for (auto name : predecessors) successors[name].insert(cell->name);
			if (predecessors.empty()) queue.push_back(cell->name);
		}
		while (!queue.empty()) {
			IdString name = queue.front(); queue.pop_front();
			for (auto next : successors[name])
				if (--remaining.at(next) == 0) queue.push_back(next);
		}
		for (auto entry : remaining)
			if (entry.second) unsafe.insert(entry.first);
	}

	bool prepare_uncached(LutResynRegion &region) {
		if (GetSize(region.nodes) > options.max_cells) return false;
		if (!resources.spend(16 * GetSize(region.nodes) + GetSize(region.roots))) return false;
		std::set<IdString> roots(region.roots.begin(), region.roots.end());
		std::set<SigBit> leaves;
		std::map<IdString, int> indegree;
		std::map<IdString, std::set<IdString>> successors;
		for (auto name : region.nodes) {
			Cell *cell = module->cell(name);
			if (!valid_lut(cell, true)) return false;
			SigBit output = canonical(cell->getPort(ID::Y)[0]);
			if (!roots.count(name)) {
				bool observed = ports_out.count(output);
				auto it = users.find(output);
				if (it != users.end())
					for (auto user : it->second) {
						if (!resources.spend(1)) return false;
						if (!region.nodes.count(user)) observed = true;
					}
				if (observed) { roots.insert(name); region.roots.push_back(name); }
			}
			std::set<IdString> predecessors;
			for (auto bit : cell->getPort(ID::A)) {
				bit = canonical(bit);
				if (!bit.wire) continue;
				Cell *driver = unique_driver(bit);
				if (driver && region.nodes.count(driver->name)) predecessors.insert(driver->name);
				else leaves.insert(bit);
			}
			indegree[name] = GetSize(predecessors);
			for (auto predecessor : predecessors) successors[predecessor].insert(name);
		}
		for (auto root : roots)
			if (!region.nodes.count(root)) return false;
		region.boundary.assign(leaves.begin(), leaves.end());
		region.order.clear();
		std::set<IdString> ready;
		for (auto entry : indegree) if (entry.second == 0) ready.insert(entry.first);
		while (!ready.empty()) {
			IdString name = *ready.begin(); ready.erase(ready.begin());
			region.order.push_back(name);
			for (auto next : successors[name]) if (--indegree.at(next) == 0) ready.insert(next);
		}
		std::sort(region.roots.begin(), region.roots.end());
		return GetSize(region.order) == GetSize(region.nodes) && GetSize(region.roots) <= 8;
	}

	bool prepare(LutResynRegion &region, bool require_boundary = true) {
		if (!resources.spend(1 + GetSize(region.nodes))) return false;
		LutResynRegionKey key {region.nodes, region.roots};
		auto it = region_cache.find(key);
		if (it == region_cache.end()) {
			// 预留两个区域副本、容器节点及真值表，覆盖求值后的缓存大小。
			int64_t bytes = 4096 + 512 * GetSize(region.nodes);
			if (cycle_memory + bytes > 4 * 1048576) {
				int64_t eviction_work = 32 * (GetSize(region_cache) + GetSize(cut_cache));
				for (const auto &entry : region_cache) eviction_work += 8 * GetSize(entry.second.region.nodes);
				for (const auto &entry : cut_cache) for (const auto &cut : entry.second) eviction_work += 8 * GetSize(cut.nodes);
				if (!resources.spend(eviction_work)) return false;
				region_cache.clear(); cut_cache.clear();
				resources.release(cycle_memory); cycle_memory = 0;
			}
			if (!resources.reserve(bytes)) return false;
			cycle_memory += bytes;
			LutResynPrepared prepared;
			prepared.valid = prepare_uncached(region);
			prepared.region = region;
			it = region_cache.emplace(std::move(key), std::move(prepared)).first;
		} else {
			prepared_hits++;
			region = it->second.region;
		}
		return it->second.valid && (!require_boundary || GetSize(region.boundary) <= 10);
	}

	static bool region_priority(const LutResynRegion &a, const LutResynRegion &b) {
		if (a.nodes.size() != b.nodes.size()) return a.nodes.size() > b.nodes.size();
		if (a.boundary.size() != b.boundary.size()) return a.boundary.size() < b.boundary.size();
		return std::tie(a.roots, a.nodes) < std::tie(b.roots, b.nodes);
	}

	bool sort_regions(vector<LutResynRegion> &regions) {
		int levels = 1;
		for (size_t count = regions.size(); count > 1; count >>= 1) levels++;
		if (!resources.spend(int64_t(regions.size()) * levels * (options.max_cells + 4))) return false;
		std::sort(regions.begin(), regions.end(), region_priority);
		return true;
	}

	// 区域内部消耗的输出可以随区域删除，保留具有外部使用者的根。
	void reduce_roots(LutResynRegion &region) {
		region.roots.erase(std::remove_if(region.roots.begin(), region.roots.end(), [&](IdString name) {
			SigBit output = canonical(module->cell(name)->getPort(ID::Y)[0]);
			if (ports_out.count(output)) return false;
			auto it = users.find(output);
			if (it == users.end() || it->second.empty()) return false;
			for (auto user : it->second) {
				if (!resources.spend(1)) return false;
				if (!region.nodes.count(user)) return false;
			}
			return true;
		}), region.roots.end());
	}

	vector<LutResynRegion> enumerate(vector<IdString> roots, int budget) {
		if (!resources.spend(1 + GetSize(roots))) return {};
		std::sort(roots.begin(), roots.end());
		auto key = std::make_pair(roots, budget);
		auto cached = cut_cache.find(key);
		if (cached != cut_cache.end()) {
			int64_t work = 0;
			for (const auto &region : cached->second) work += 8 + 2 * GetSize(region.nodes) + GetSize(region.boundary);
			if (!resources.spend(work)) return {};
			cut_hits++;
			return cached->second;
		}
		LutResynRegion seed;
		seed.roots = roots;
		seed.nodes.insert(seed.roots.begin(), seed.roots.end());
		if (!prepare(seed, false)) return {};
		reduce_roots(seed);
		if (resources.stopped) return {};
		int leaf_limit = 10;
		vector<LutResynRegion> frontier {seed}, result;
		std::set<std::set<IdString>> visited {seed.nodes};
		int expanded = 0;
		while (!frontier.empty() && expanded < budget && !resources.stopped) {
			if (!sort_regions(frontier)) break;
			LutResynRegion region = frontier.front(); frontier.erase(frontier.begin());
			expanded++;
			if (GetSize(region.boundary) <= 10) result.push_back(region);
			if (GetSize(region.nodes) >= options.max_cells) continue;
			for (auto bit : region.boundary) {
				if (!resources.spend(8 + GetSize(region.nodes))) break;
				Cell *driver = unique_driver(bit);
				if (!valid_lut(driver, true)) continue;
				LutResynRegion next = region;
				next.nodes.insert(driver->name);
				reduce_roots(next);
				if (!visited.insert(next.nodes).second || !prepare(next, false) || GetSize(next.boundary) > leaf_limit) continue;
				frontier.push_back(std::move(next));
			}
			// 保留最高优先级的有限候选，避免展开过程随模块规模增长。
			if (!sort_regions(frontier)) break;
			if (GetSize(frontier) > budget - expanded) frontier.resize(budget - expanded);
		}
		if (!resources.stopped) {
			int64_t bytes = 128;
			for (const auto &region : result) bytes += 512 + 128 * GetSize(region.nodes);
			if (cycle_memory + bytes <= 4 * 1048576 && resources.reserve(bytes)) {
				cycle_memory += bytes;
				cut_cache.emplace(std::move(key), result);
			}
		}
		return result;
	}

	vector<IdString> neighbors(IdString root) {
		if (!resources.spend(64)) return {};
		std::set<SigBit> leaves;
		Cell *cell = module->cell(root);
		if (!valid_lut(cell, true)) return {};
		for (auto bit : cell->getPort(ID::A)) {
			bit = canonical(bit);
			if (!bit.wire) continue;
			leaves.insert(bit);
			Cell *driver = unique_driver(bit);
			if (valid_lut(driver, false))
				for (auto input : driver->getPort(ID::A)) {
					input = canonical(input);
					if (input.wire) leaves.insert(input);
				}
		}
		leaves.insert(canonical(cell->getPort(ID::Y)[0]));
		std::set<IdString> adjacent;
		for (auto bit : leaves) {
			auto it = users.find(bit);
			if (it == users.end()) continue;
			int examined = 0;
			for (auto name : it->second) {
				if (++examined > options.max_neighbors) break;
				if (!resources.spend(16)) return {};
				if (name != root && valid_lut(module->cell(name), true)) adjacent.insert(name);
			}
		}
		vector<IdString> result;
		for (auto name : adjacent) {
			result.push_back(name);
		}
		int levels = 1;
		for (size_t count = result.size(); count > 1; count >>= 1) levels++;
		if (!resources.spend(int64_t(result.size()) * levels * 8)) return {};
		std::sort(result.begin(), result.end(), [&](IdString a, IdString b) {
			bool a_port = ports_out.count(canonical(module->cell(a)->getPort(ID::Y)[0]));
			bool b_port = ports_out.count(canonical(module->cell(b)->getPort(ID::Y)[0]));
			if (a_port != b_port) return a_port > b_port;
			return a < b;
		});
		if (GetSize(result) > options.max_neighbors) result.resize(options.max_neighbors);
		return result;
	}

	vector<LutResynRegion> candidates(IdString root) {
		auto adjacent = neighbors(root);
		vector<vector<IdString>> groups;
		std::set<vector<IdString>> seen;
		for (int i = 0; i < GetSize(adjacent) && GetSize(groups) < options.max_joint; i++) {
			vector<IdString> group {root, adjacent[i]};
			for (int j = i; GetSize(group) <= 8 && GetSize(groups) < options.max_joint; j++) {
				if (!resources.spend(16)) return {};
				std::sort(group.begin(), group.end());
				if (seen.insert(group).second) groups.push_back(group);
				if (j + 1 == GetSize(adjacent)) break;
				group.push_back(adjacent[j + 1]);
			}
		}
		int joint_budget = groups.empty() ? 0 : options.max_cuts / 2;
		vector<LutResynRegion> result = enumerate({root}, options.max_cuts - joint_budget);
		int used = 0;
		for (int i = 0; i < GetSize(groups) && used < joint_budget && !resources.stopped; i++) {
			int budget = std::min(joint_budget - used, std::max(GetSize(groups[i]) + 1,
			                      (joint_budget - used) / (GetSize(groups) - i)));
			auto regions = enumerate(groups[i], budget);
			used += budget;
			if (!resources.spend(int64_t(regions.size()) * (2 * options.max_cells + 24))) break;
			result.insert(result.end(), regions.begin(), regions.end());
		}
		sort_regions(result);
		return result;
	}

	// 仅遍历待复用输出的组合前驱；完整证明可供当前区域的其它计划复用。
	bool independent(IdString source, LutResynProof &proof) {
		if (!resources.spend(1)) return false;
		if (proof.region.nodes.count(source)) return false;
		if (proof.independent.count(source)) { proof_hits++; return true; }
		if (proof.dependent.count(source)) { proof_hits++; return false; }
		std::set<IdString> visited;
		vector<IdString> queue;
		bool depends = false;
		auto visit = [&](IdString name) {
			if (!resources.spend(1)) return false;
			if (proof.region.nodes.count(name) || proof.dependent.count(name)) { depends = true; return false; }
			if (proof.independent.count(name) || visited.count(name)) return true;
			if (proof.examined >= options.max_dependencies) return false;
			proof.examined++;
			visited.insert(name); queue.push_back(name);
			return true;
		};
		auto reject = [&]() {
			if (depends) proof.dependent.insert(source);
			return false;
		};
		if (!visit(source)) return reject();
		while (!queue.empty()) {
			IdString name = queue.back(); queue.pop_back();
			if (sequential(module->cell(name))) continue;
			for (auto bit : cell_inputs.at(name)) {
				if (!resources.spend(1)) return false;
				auto it = drivers.find(bit);
				if (it == drivers.end()) continue;
				for (auto driver : it->second) if (!visit(driver)) return reject();
			}
		}
		proof.independent.insert(visited.begin(), visited.end());
		return true;
	}

	bool boundary_safe(LutResynProof &proof) {
		// 单根区域由无环组合图的前驱扩展生成，其边界均位于该根之前。
		if (GetSize(proof.region.roots) == 1) return true;
		for (auto bit : proof.region.boundary) {
			if (!resources.spend(1)) return false;
			auto it = drivers.find(bit);
			if (it != drivers.end())
				for (auto driver : it->second) if (!independent(driver, proof)) return false;
		}
		return true;
	}

	LutResynPlannedFunction normalize(vector<LutResynRef> raw, LutResynTable table) const {
		LutResynPlannedFunction f;
		for (auto &ref : raw) {
			if (ref.node < 0) ref.bit = canonical(ref.bit);
			if (ref.node >= 0 || ref.bit.wire) f.inputs.push_back(ref);
		}
		std::sort(f.inputs.begin(), f.inputs.end());
		f.inputs.erase(std::unique(f.inputs.begin(), f.inputs.end()), f.inputs.end());
		for (int a = 0; a < (1 << GetSize(f.inputs)); a++) {
			int address = 0;
			for (int i = 0; i < GetSize(raw); i++) {
				auto ref = raw[i];
				bool value = ref.node < 0 && ref.bit == State::S1;
				if (ref.node >= 0 || ref.bit.wire)
					value = (a >> (std::lower_bound(f.inputs.begin(), f.inputs.end(), ref) - f.inputs.begin())) & 1;
				address |= int(value) << i;
			}
			f.table.set(a, table.get(address));
		}
		lutresyn_reduce(f.inputs, f.table);
		return f;
	}

	vector<LutResynRef> cached_outputs(const LutResynPlannedFunction &f, LutResynProof &proof,
	                                  LutResynReservation &storage) {
		vector<LutResynRef> result;
		if (!resources.spend(1)) return result;
		LutResynFunction key;
		for (auto input : f.inputs) {
			if (input.node >= 0) return result;
			key.inputs.push_back(input.bit);
		}
		key.table = f.table;
		auto it = function_cache.find(key);
		if (it == function_cache.end()) return result;
		for (auto name : it->second) {
			if (!resources.spend(16)) break;
			Cell *cell = module->cell(name);
			if (!valid_lut(cell, false) || !independent(name, proof)) continue;
			if (!storage.reserve(128)) break;
			result.emplace_back(canonical(cell->getPort(ID::Y)[0]));
			break;
		}
		return result;
	}

	std::optional<LutResynRef> synthesize(LutResynPlan &plan, vector<LutResynRef> inputs, LutResynTable table,
	                                    LutResynProof &proof, LutResynReservation &storage) {
		if (!resources.spend(32 + (1 << GetSize(inputs)) * (2 * GetSize(inputs) + 2))) return std::nullopt;
		auto f = normalize(std::move(inputs), table);
		if (f.inputs.empty()) return LutResynRef(SigBit(f.table.get(0) ? State::S1 : State::S0));
		if (GetSize(f.inputs) == 1 && !f.table.get(0) && f.table.get(1)) return f.inputs[0];
		auto cached = cached_outputs(f, proof, storage);
		if (resources.stopped) return std::nullopt;
		if (!cached.empty()) return cached.front();
		auto it = plan.functions.find(f);
		if (it != plan.functions.end()) return it->second;
		log_assert(GetSize(f.inputs) <= 4);
		LutResynRef ref(GetSize(plan.nodes));
		plan.nodes.push_back(f); plan.functions.emplace(std::move(f), ref);
		return ref;
	}

#include "opt_lutresyn_dictionary.h"

	void commit(LutResynRegion region, LutResynPlan plan) {
		int64_t actual_commit_work = dictionary_commit_work(region, plan);
		log_assert(actual_commit_work <= resources.commit_credit);
		resources.commit_credit = actual_commit_work;
		commit_work += resources.commit_credit;
		resources.consume_commit();
		log_assert(GetSize(region.boundary) <= 10);
		int cost = plan.cost();
		log_assert(plan.proven && plan.gain > 0 && GetSize(plan.deleting) - cost == plan.gain);
		log_assert(GetSize(plan.preserve) == GetSize(region.roots));
		vector<SigBit> root_outputs;
		std::set<IdString> affected;
		for (auto root : region.roots) {
			SigBit bit = canonical(module->cell(root)->getPort(ID::Y)[0]);
			root_outputs.push_back(bit);
			auto it = users.find(bit);
			if (it != users.end()) affected.insert(it->second.begin(), it->second.end());
		}
		for (auto name : plan.deleting) affected.erase(name);
		for (auto name : affected) index_erase(name);
		// 缓存中的结构身份在移除单元之前释放，纯函数问题继续复用。
		region_cache.clear(); cut_cache.clear();
		resources.release(cycle_memory); cycle_memory = 0;
		for (auto name : plan.deleting) {
			index_erase(name); pending.erase(name); unsafe.erase(name);
			module->remove(module->cell(name));
		}
		vector<SigBit> created(plan.nodes.size());
		vector<Cell *> new_cells;
		auto materialize = [&](LutResynRef ref) {
			return ref.node < 0 ? canonical(ref.bit) : created.at(ref.node);
		};
		for (int i : plan.needed) {
			const auto &f = plan.nodes[i];
			SigSpec a;
			for (auto ref : f.inputs) a.append(materialize(ref));
			created[i] = SigBit(module->addWire(NEW_ID));
			Const table(State::S0, 1 << GetSize(f.inputs));
			for (int j = 0; j < GetSize(table); j++) table.set(j, f.table.get(j) ? State::S1 : State::S0);
			new_cells.push_back(module->addLut(NEW_ID, a, created[i], table));
		}
		for (int i = 0; i < GetSize(root_outputs); i++) {
			SigBit old_output = root_outputs[i], replacement = materialize(plan.outputs[i]);
			if (plan.preserve[i]) { log_assert(old_output == replacement); continue; }
			log_assert(old_output != replacement);
			module->connect(old_output, replacement);
			redirects[old_output] = replacement;
			if (ports_out.erase(old_output)) ports_out.insert(replacement);
			if (protected_bits.erase(old_output)) protected_bits.insert(replacement);
		}
		for (auto name : affected) index_add(module->cell(name));
		for (auto cell : new_cells) index_add(cell);
		for (auto name : affected) {
			Cell *cell = module->cell(name); cache_add(cell);
			if (valid_lut(cell, true)) pending.insert(name);
		}
		for (auto cell : new_cells) { cache_add(cell); pending.insert(cell->name); }
		for (auto bit : region.boundary) {
			Cell *driver = unique_driver(bit);
			if (valid_lut(driver, true)) pending.insert(driver->name);
			auto it = users.find(canonical(bit));
			if (it == users.end()) continue;
			int examined = 0;
			for (auto name : it->second) {
				if (++examined > options.max_neighbors) break;
				if (valid_lut(module->cell(name), true)) pending.insert(name);
			}
		}
		// 结构改变后结束当前分析周期，抽象真值表分解继续跨周期复用。
		accepted++;
		removed += plan.gain;
		retained_cells += GetSize(plan.retained); new_cells_count += cost;
		log("  Dictionary commit: outputs=%d retained=%d deleted=%d new=%d gain=%d.\n",
		    GetSize(region.roots), GetSize(plan.retained), GetSize(plan.deleting), cost, plan.gain);
		log_debug("  Replaced %d $lut cells at %d outputs with %d new cells in %s.\n",
		          GetSize(plan.deleting), GetSize(region.roots), cost, log_id(module));
	}

	LutResynWorker(Module *module, Design *design, LutResynOptions options) :
		module(module), sigmap(module), types(design), native_dffeas(LutFfBoundary::native_dffeas_declared(design, types)),
		options(options), resources(options)
	{
		for (auto wire : module->wires())
			for (auto bit : SigSpec(wire)) {
				bit = canonical(bit);
				if (wire->port_input) { ports_in.insert(bit); input_driver_counts[bit]++; }
				if (wire->port_output) ports_out.insert(bit);
				if (wire->get_bool_attribute(ID::keep) || wire->get_bool_attribute(ID::lut_keep) || wire->attributes.count(ID::init)) protected_bits.insert(bit);
			}
		for (auto cell : module->cells()) { index_add(cell); if (cell->type == ID(dffeas) && sequential(cell)) native_ff_count++; }
		find_unsafe();
		for (auto cell : module->cells()) {
			if (cell->type.in(ID($lut), ID($not), ID($_NOT_)) && unsafe.count(cell->name)) cycle_original++;
			bool eligible = valid_lut(cell, true);
			if (eligible) eligible_original++;
			cache_add(cell);
			if (eligible) pending.insert(cell->name);
		}
		// 搜索临时容器按允许的结构规模预留空间，模块连接索引按实际连接维护。
		LutResynReservation scratch(resources);
		scratch.reserve(131072 + int64_t(options.max_cuts) * 20 * (512 + 128 * options.max_cells) +
		                int64_t(options.max_dependencies) * 256 + int64_t(options.max_joint) * 256 +
		                int64_t(options.max_neighbors) * 21 * 128);
		Lut4Mapping::PostTimer search_timer(Lut4Mapping::timed_post_design(design), Lut4Mapping::PostPhase::ResynSearch);
		std::deque<IdString> root_queue = dictionary_root_queue();
		while ((!pending.empty() || !root_queue.empty()) && !resources.stopped) {
			resources.local_stopped = false;
			root_complete_plans = 0;
			root_work_end = std::min<int64_t>(resources.work_limit, resources.work + 250000);
			resources.local_limit = root_work_end;
			if (!resources.spend(16)) break;
			while (!root_queue.empty() && !pending.count(root_queue.front())) root_queue.pop_front();
			if (root_queue.empty() && pending.empty()) break;
			IdString root = root_queue.empty() ? *pending.begin() : root_queue.front();
			if (!root_queue.empty()) root_queue.pop_front();
			pending.erase(root);
			if (!valid_lut(module->cell(root), true)) continue;
			LutResynRegion best_region;
			LutResynPlan best_plan;
			int best_gain = 0, best_cost = 0;
			int64_t best_commit_memory = 0;
			for (auto region : candidates(root)) {
				if (resources.stopped || resources.local_stopped) break;
				analyzed++;
				if (!prepare(region)) continue;
				LutResynProof proof(region);
				if (!boundary_safe(proof)) continue;
				LutResynPlan plan;
				if (!choose_dictionary_plan(region, proof, plan)) continue;
				int cost = plan.cost(), gain = plan.gain;
				if (gain > best_gain || (gain == best_gain && cost < best_cost)) {
					int64_t prior_credit = resources.commit_credit;
					if (!resources.hold_commit(dictionary_commit_work(region, plan) + 16384)) continue;
					int64_t commit_memory = 256 * (GetSize(region.roots) + GetSize(plan.needed));
					if (commit_memory > best_commit_memory && !resources.reserve(commit_memory - best_commit_memory)) {
						resources.commit_credit = prior_credit; continue;
					}
					if (commit_memory < best_commit_memory) resources.release(best_commit_memory - commit_memory);
					best_commit_memory = commit_memory;
					best_gain = gain; best_cost = cost;
					best_region = std::move(region); best_plan = std::move(plan);
				}
			}
			if (best_gain > 0 && !options.dry_run) commit(std::move(best_region), std::move(best_plan));
			else resources.release(best_commit_memory);
			resources.commit_credit = 0;
			resources.local_limit = -1;
			resources.local_stopped = false;
		}
		log("  %s: analyzed %lld candidates, accepted %lld regions, removed %lld $lut cells.\n",
		    log_id(module), (long long)analyzed, (long long)accepted, (long long)removed);
		log("  Search work %lld/%lld, accounted peak memory %lld/%lld bytes, budget %s.\n",
		    (long long)resources.work, (long long)resources.work_limit,
		    (long long)resources.peak_memory, (long long)resources.memory_limit,
		    resources.stopped ? "exhausted" : "available");
		log("  Cache hits: prepared %lld, cuts %lld, problems %lld, dependency proofs %lld.\n",
		    (long long)prepared_hits, (long long)cut_hits, (long long)problem_hits, (long long)proof_hits);
		log("  Dictionary: native_ff_boundary=%lld eligible_luts=%lld cycle_luts=%lld external_outputs=%lld functions=%lld single_bridge_plans=%lld two_bridge_plans=%lld complete_joint_plans=%lld enumeration_proofs=%lld care_regions=%lld generation=%lld retained=%lld new=%lld gain=%lld.\n",
		    (long long)native_ff_count, (long long)eligible_original, (long long)cycle_original, (long long)external_outputs,
		    (long long)dictionary_functions, (long long)single_bridge_plans, (long long)two_bridge_plans,
		    (long long)complete_joint_plans, (long long)enumeration_proofs, (long long)care_regions, (long long)accepted,
		    (long long)retained_cells, (long long)new_cells_count, (long long)removed);
		log("  Dictionary work: functions=%lld address=%lld price=%lld proof=%lld environment=%lld ordering=%lld commit=%lld SAT=0.\n",
		    (long long)dictionary_work, (long long)address_work, (long long)price_work, (long long)proof_work, (long long)environment_work,
		    (long long)sorting_work, (long long)commit_work);
	}
};

struct OptLutResynPass : Pass
{
	OptLutResynPass() : Pass("opt_lutresyn", "exact area resynthesis of small LUT4 regions") {}
	void help() override {
		log("\n    opt_lutresyn [options] [selection]\n\n");
		log("Resynthesize selected LUT/NOT regions with up to ten independent inputs\n");
		log("and eight externally observed outputs using a shared function dictionary.\n");
		log("Enumerate one/two-bridge partitions on supports of up to seven inputs,\n");
		log("reuse existing functions, and prove complete bounded environment care.\n");
		log("Select each output's own shared subset and accept replacements\n");
		log("only when actual deletions exceed actual new LUT cells. Preserve output\n");
		log("wires, ports, keep and init attributes, and all sequential cells.\n");
		log("Run after abc9 and before technology-specific LUT cell mapping.\n\n");
		log("    -dry-run            prove and price plans without modifying the module\n");
		log("    -max-cells N        region cell limit (1..32, default 32)\n");
		log("    -max-cuts N         candidates per root (1..1024, default 32)\n");
		log("    -max-problems N     cached decomposition problems (1..65536, default 4096)\n");
		log("    -max-joint N        adjacent root groups (0..256, default 8)\n");
		log("    -max-neighbors N    neighboring roots (1..256, default 12)\n");
		log("    -max-dependencies N visited proof cells per region (1..1048576, default 4096)\n");
		log("    -max-work N         total search work per module (1..16000000, default 16000000)\n");
		log("    -max-memory N       accounted search memory in MiB (1..64, default 64)\n\n");
		log("Work covers cuts, preparation, table evaluation, dependency edges,\n");
		log("decomposition and plan comparisons, and persists across accepted changes.\n");
		log("Memory includes conservative container charges and reserved search scratch;\n");
		log("module connection/function indexes and commit maintenance scale with the netlist.\n");
		log("At a search budget limit, stop new candidates and commit the best proven gain.\n");
		log("At the problem limit, reuse cached proofs and stop searching new problems.\n");
		log("Reject candidates with undefined tables or inputs, multiple drivers,\n");
		log("combinational cycles, or incomplete dependency proofs.\n\n");
	}
	void execute(vector<std::string> args, Design *design) override {
		log_header(design, "Executing OPT_LUTRESYN pass (exact LUT4 region resynthesis).\n");
		LutResynOptions options;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			int *target = nullptr, minimum = 1, maximum = 0;
			const std::string &arg = args[argidx];
			if (arg == "-dry-run") { options.dry_run = true; continue; }
			if (arg == "-max-cells") { target = &options.max_cells; maximum = 32; }
			if (arg == "-max-cuts") { target = &options.max_cuts; maximum = 1024; }
			if (arg == "-max-problems") { target = &options.max_problems; maximum = 65536; }
			if (arg == "-max-joint") { target = &options.max_joint; minimum = 0; maximum = 256; }
			if (arg == "-max-neighbors") { target = &options.max_neighbors; maximum = 256; }
			if (arg == "-max-dependencies") { target = &options.max_dependencies; maximum = 1048576; }
			if (arg == "-max-work") { target = &options.max_work; maximum = 16000000; }
			if (arg == "-max-memory") { target = &options.max_memory; maximum = 64; }
			if (!target) break;
			if (++argidx == args.size() || args[argidx].empty()) log_cmd_error("Expected an integer after %s.\n", arg.c_str());
			int value = 0;
			for (char ch : args[argidx]) {
				if (ch < '0' || ch > '9' || value > (maximum - (ch - '0')) / 10)
					log_cmd_error("%s requires an integer in %d..%d.\n", arg.c_str(), minimum, maximum);
				value = value * 10 + ch - '0';
			}
			if (value < minimum || value > maximum) log_cmd_error("%s requires an integer in %d..%d.\n", arg.c_str(), minimum, maximum);
			*target = value;
		}
		extra_args(args, argidx, design);
		if (!Lut4Mapping::shared_post(design)) Lut4Mapping::reset_post_report(design, "resyn");
		for (auto module : design->selected_modules()) {
			if (module->has_processes()) log_cmd_error("opt_lutresyn requires lowered processes in %s.\n", log_id(module));
			auto module_options = options;
			int64_t setup_work = 0;
			if (Lut4Mapping::shared_post(design)) {
				module_options.max_work = std::min<int64_t>(options.max_work, std::stoll(design->scratchpad_get_string(Lut4Mapping::post_key("resyn", "remaining"))));
				int64_t minimum = 64 + 16 * int64_t(module->cells_size()) + 8 * int64_t(module->wires_size());
				if (module_options.max_work < minimum + 16) {
					log("opt_lutresyn: shared work remaining=%d below minimum index/candidate work=%lld before workspace construction in %s.\n", module_options.max_work, (long long)(minimum + 16), log_id(module));
					continue;
				}
				int64_t inspection = 0;
				setup_work = Lut4Mapping::post_setup_work(module, module_options.max_work, inspection);
				Lut4Mapping::report_post(design, "resyn", inspection, 0, 0);
				module_options.max_work -= inspection;
				if (setup_work < 0) {
					log("opt_lutresyn: shared work exhausted during index size inspection before workspace construction in %s.\n", log_id(module));
					continue;
				}
				if (module_options.max_work < setup_work + 16) {
					log("opt_lutresyn: shared work below complete index/candidate work=%lld before workspace construction in %s.\n", (long long)(setup_work + 16), log_id(module));
					continue;
				}
			}
			int64_t index_bytes = Lut4Mapping::post_index_bytes(module, true) + 1024 * int64_t(module->cells_size());
			// 函数索引包含 1024 行容器与有据排序队列，费用在构造前完整预付。
			setup_work += 256 * int64_t(module->cells_size());
			if (module_options.max_work < setup_work + 16) {
				log("opt_lutresyn: work below complete dictionary index construction in %s.\n", log_id(module));
				continue;
			}
			if (!Lut4Mapping::shared_post(design)) {
				int64_t inspection = 0;
				int64_t index_work = Lut4Mapping::post_setup_work(module, module_options.max_work - setup_work, inspection);
				Lut4Mapping::report_post(design, "resyn", inspection, 0, 0);
				module_options.max_work -= inspection;
				if (index_work < 0) continue;
				setup_work += index_work;
				if (module_options.max_work < setup_work + 16) continue;
				module_options.memory_bytes = std::max<int64_t>(0, int64_t(options.max_memory) * 1048576 - index_bytes);
			}
			if (Lut4Mapping::shared_post(design)) {
				int64_t memory = std::stoll(design->scratchpad_get_string("opt_lut4_post.memory_remaining"));
				memory = std::max<int64_t>(0, memory - index_bytes);
				module_options.memory_bytes = std::max<int64_t>(0, std::min<int64_t>(int64_t(options.max_memory) * 1048576 - index_bytes, memory));
				if (!module_options.max_work || !module_options.memory_bytes) {
					log("opt_lutresyn: shared budget exhausted before workspace construction in %s.\n", log_id(module));
					continue;
				}
			}
			if (!module_options.memory_bytes) continue;
			Lut4Mapping::report_post(design, "resyn", setup_work, 0, index_bytes);
			log("opt_lutresyn: workspace construction work=%lld, search allowance=%lld, index reservation=%lld bytes in %s.\n", (long long)setup_work, (long long)(module_options.max_work - setup_work), (long long)index_bytes, log_id(module));
			module_options.max_work -= setup_work;
			LutResynWorker worker(module, design, module_options);
			Lut4Mapping::report_post(design, "resyn", worker.resources.work, 0, worker.resources.peak_memory + index_bytes);
		}
	}
} OptLutResynPass;

// ===== 原生 FF 观察域 LUT4 拟合 =====
//
// 只处理 prn=1 且 aload/asdata/sclr/sload=0 的原 FF_MAP 形式 dffeas。FF 仅在
// ENA 有效时观察 D，因此 D 在 ENA 关闭域可以改变。每个数据根枚举根与有限直接
// 前驱子集组成的区域，按当前真实消费者计算删除闭包并按闭包去重；区域内部排序
// 与数据/ENA 有界展开负责结束没有有效依赖顺序的候选。数据与全部实际 ENA 在同
// 一组合前沿完整枚举，冲突拟合为四输入以内的一份逻辑；严格观察者、恒 1 ENA 与
// 共同域恒被观察的根立即结束。常量与直通零新增，普通新增 LUT/NOT 计一，只提交
// 已完整证明的最大正收益。

struct NativeFfLut4Observer
{
	SigBit ena;
	IdString ff;
};

struct NativeFfLut4Fit
{
	std::vector<SigBit> support;
	LutResynTable table;
	int cost = 0;
};

// 边界信号按名称排序，候选枚举次序与平局处理保持稳定。
struct NativeFfLut4BitLess
{
	bool operator()(SigBit a, SigBit b) const {
		if (a.wire == b.wire) {
			if (!a.wire) return int(a.data) < int(b.data);
			return a.offset < b.offset;
		}
		if (!a.wire || !b.wire) return a.wire == nullptr;
		return a.wire->name.str() < b.wire->name.str();
	}
};

struct NativeFfLut4Worker
{
	Module *module;
	SigMap sigmap;
	CellTypes types;
	bool native_dffeas;
	LutResynResources resources;

	mutable std::map<SigBit, SigBit> redirects;
	std::map<SigBit, std::set<IdString>> drivers, users;
	std::map<IdString, std::set<SigBit>> cell_inputs, cell_outputs;
	std::map<SigBit, int> driver_counts, input_driver_counts;
	std::map<IdString, std::map<SigBit, int>> cell_driver_counts;
	std::set<SigBit> ports_in, ports_out, protected_bits;
	std::set<IdString> pending, attempted;
	std::vector<IdString> qualified_ffs;
	std::vector<SigBit> frontier;
	std::map<SigBit, int> frontier_index;
	int64_t analyzed = 0, accepted = 0, removed = 0, added = 0;
	int64_t ff_observers = 0, strict_observers = 0;

	SigBit canonical(SigBit bit) const {
		return lutresyn_canonical(sigmap, redirects, bit);
	}

	bool sequential(Cell *cell) const {
		return LutFfBoundary::sequential(cell, native_dffeas);
	}

	int driver_count(SigBit bit) const {
		auto it = driver_counts.find(bit), input_it = input_driver_counts.find(bit);
		return (it == driver_counts.end() ? 0 : it->second) + (input_it == input_driver_counts.end() ? 0 : input_it->second);
	}

	void index_add(Cell *cell) {
		lutresyn_index_add(*this, cell);
	}

	void index_erase(IdString name) {
		lutresyn_index_erase(*this, name);
	}

	Cell *unique_driver(SigBit bit) const {
		bit = canonical(bit);
		if (!bit.wire || ports_in.count(bit)) return nullptr;
		auto it = drivers.find(bit);
		auto count = driver_counts.find(bit);
		if (it == drivers.end() || it->second.size() != 1) return nullptr;
		if (count == driver_counts.end() || count->second != 1) return nullptr;
		return module->cell(*it->second.begin());
	}

	// 仅普通 $lut 与一位 NOT 进入数据区域，资格与原保护条件保持一致。
	bool valid_lut(Cell *cell, bool deleting) const {
		if (!lutresyn_lut_shape(cell)) return false;
		for (auto bit : cell->getPort(ID::A)) {
			bit = canonical(bit);
			if (!bit.wire && bit != State::S0 && bit != State::S1) return false;
			if (bit.wire && driver_count(bit) > 1) return false;
		}
		SigBit output = canonical(cell->getPort(ID::Y)[0]);
		if (unique_driver(output) != cell) return false;
		if (deleting && (!module->selected(cell) || cell->has_keep_attr() || cell->get_bool_attribute(ID::lut_keep) ||
		    cell->attributes.count(ID::init) || protected_bits.count(output))) return false;
		return true;
	}

	// 只接受完整原生接口且 prn=1、aload/asdata/sclr/sload=0 的原 FF_MAP 形式。
	bool qualified_ff(Cell *cell) const {
		if (!native_dffeas || cell->type != ID(dffeas) || !sequential(cell)) return false;
		if (canonical(cell->getPort(ID(prn))[0]) != State::S1) return false;
		for (auto port : {ID(aload), ID(asdata), ID(sclr), ID(sload)})
			if (canonical(cell->getPort(port)[0]) != State::S0) return false;
		return true;
	}

	// 根输出的真实观察者：只把输入端口算作使用者，Y 驱动端口不进入观察。
	// 出现模块输出、保护、其它端口或普通组合使用者（严格观察者）时立即结束该根。
	bool collect_observers(SigBit output, const std::set<IdString> &deleting, std::vector<NativeFfLut4Observer> &observers) {
		if (!resources.spend(8)) return false;
		if (ports_out.count(output)) { strict_observers++; return false; }
		auto it = users.find(output);
		if (it == users.end()) return true;
		for (auto name : it->second) {
			if (!resources.spend(8)) return false;
			if (deleting.count(name)) continue;
			Cell *user = module->cell(name);
			bool ff = qualified_ff(user);
			bool known = types.cell_known(user->type);
			for (auto &connection : user->connections()) {
				if (known && !types.cell_input(user->type, connection.first)) continue;
				for (auto bit : connection.second) {
					if (!resources.spend(1)) return false;
					if (canonical(bit) != output) continue;
					if (!ff || connection.first != ID(d)) { strict_observers++; return false; }
					observers.push_back({canonical(user->getPort(ID(ena))[0]), user->name});
					ff_observers++;
				}
			}
		}
		return true;
	}

	// 在观察域地址上做冲突拟合：同一地址出现不同原值即拒绝该 support。
	bool fit_subset(uint32_t mask, int nb, const std::vector<std::pair<uint32_t, bool>> &items, NativeFfLut4Fit &fit) {
		std::vector<int> positions;
		for (int i = 0; i < nb; i++) if (mask & (uint32_t(1) << i)) positions.push_back(i);
		int size = GetSize(positions);
		std::vector<int8_t> table(1 << size, -1);
		for (auto &item : items) {
			if (!resources.spend(1 + size)) return false;
			int address = 0;
			for (int i = 0; i < size; i++) address |= int((item.first >> positions[i]) & 1) << i;
			int8_t value = item.second ? 1 : 0;
			if (table[address] < 0) table[address] = value;
			else if (table[address] != value) return false;
		}
		if (!resources.spend(int64_t(1 << size) * (2 + size))) return false;
		std::vector<SigBit> support;
		LutResynTable lut;
		for (int i = 0; i < size; i++) support.push_back(frontier[positions[i]]);
		for (int address = 0; address < (1 << size); address++) lut.set(address, table[address] == 1);
		// 未观察地址已经取确定常量，无关输入由现有规范化删除。
		lutresyn_reduce(support, lut);
		fit.support = std::move(support);
		fit.table = lut;
		fit.cost = GetSize(fit.support) == 0 ? 0 : (GetSize(fit.support) == 1 && fit.table.get(1)) ? 0 : 1;
		return true;
	}

	// 拟合后完整检查：全部观察行上新函数等于原 D。
	bool verify_fit(const NativeFfLut4Fit &fit, int rows, const std::vector<uint8_t> &care, const std::vector<uint8_t> &old_value) {
		std::vector<int> positions;
		for (auto bit : fit.support) positions.push_back(frontier_index.at(bit));
		for (int row = 0; row < rows; row++) {
			if (!care[row]) continue;
			if (!resources.spend(1 + GetSize(positions))) return false;
			int address = 0;
			for (int i = 0; i < GetSize(positions); i++) address |= int((row >> positions[i]) & 1) << i;
			if (fit.table.get(address) != bool(old_value[row])) return false;
		}
		return true;
	}

	// 数据函数与全部实际 ENA 在同一组合前沿求值，FF.q 作为独立输入。
	bool analyze(SigBit output, const std::set<IdString> &deleting,
	             const std::vector<NativeFfLut4Observer> &observers, NativeFfLut4Fit &fit) {
		std::vector<SigBit> boundary;
		for (auto name : deleting) {
			for (auto bit : module->cell(name)->getPort(ID::A)) {
				if (!resources.spend(2)) return false;
				bit = canonical(bit);
				if (!bit.wire) continue;
				if (driver_count(bit) > 1) return false;
				Cell *driver = unique_driver(bit);
				if (driver && deleting.count(driver->name)) continue;
				boundary.push_back(bit);
			}
		}
		std::sort(boundary.begin(), boundary.end(), NativeFfLut4BitLess());
		boundary.erase(std::unique(boundary.begin(), boundary.end()), boundary.end());
		if (GetSize(boundary) > 10) return false;
		frontier = boundary;
		frontier_index.clear();
		for (int i = 0; i < GetSize(frontier); i++) frontier_index[frontier[i]] = i;
		// 数据区域按唯一内部前驱排序，评估次序保证依赖在前；重复 A 仍按实际真值
		// 求值，无法形成有效依赖顺序的候选在此正常结束。
		std::vector<Cell*> order;
		std::map<SigBit, int> result_index;
		{
			std::map<IdString, int> indegree;
			std::map<IdString, std::set<IdString>> successors;
			for (auto name : deleting) {
				std::set<IdString> predecessors;
				for (auto bit : module->cell(name)->getPort(ID::A)) {
					if (!resources.spend(1)) return false;
					Cell *driver = unique_driver(canonical(bit));
					if (driver && deleting.count(driver->name)) predecessors.insert(driver->name);
				}
				indegree[name] = GetSize(predecessors);
				for (auto predecessor : predecessors) successors[predecessor].insert(name);
			}
			std::set<IdString> ready;
			for (auto &entry : indegree) if (!entry.second) ready.insert(entry.first);
			while (!ready.empty()) {
				IdString name = *ready.begin(); ready.erase(ready.begin());
				order.push_back(module->cell(name));
				auto it = successors.find(name);
				if (it == successors.end()) continue;
				for (auto next : it->second) if (--indegree.at(next) == 0) ready.insert(next);
			}
			if (GetSize(order) != GetSize(deleting)) return false;
			for (int i = 0; i < GetSize(order); i++) result_index[canonical(order[i]->getPort(ID::Y)[0])] = i;
		}
		// ENA 沿真实普通 LUT/一位 NOT 完整展开，只允许停在既有 data frontier、真实
		// module input、真实顺序输出边界或真正无驱动位；常量仅接受 S0/S1。
		int cone_limit = 64;
		std::function<bool(SigBit, int)> expand = [&](SigBit bit, int depth) -> bool {
			bit = canonical(bit);
			if (!bit.wire) return bit == State::S0 || bit == State::S1;
			// 每个真实 wire 入口先核实唯一驱动，多驱动立即结束整个候选。
			if (driver_count(bit) > 1) return false;
			if (frontier_index.count(bit) || result_index.count(bit)) return true;
			if (depth > 32 || GetSize(order) >= cone_limit) return false;
			if (!resources.spend(8)) return false;
			Cell *driver = unique_driver(bit);
			if (!driver) {
				// 只有真实 module input 与真正无驱动位可以作为独立输入。
				if (!ports_in.count(bit) && driver_count(bit) != 0) return false;
				if (GetSize(frontier) >= 10) return false;
				frontier_index[bit] = GetSize(frontier);
				frontier.push_back(bit);
				return true;
			}
			if (sequential(driver)) {
				if (GetSize(frontier) >= 10) return false;
				frontier_index[bit] = GetSize(frontier);
				frontier.push_back(bit);
				return true;
			}
			// 无效或未知组合驱动与无效 LUT 表不能直接当作独立 bit。
			if (!valid_lut(driver, false)) return false;
			for (auto input : driver->getPort(ID::A)) if (!expand(input, depth + 1)) return false;
			// 前驱递归加入的单元同样计入上限，保证每个候选实际单元不超过 64。
			if (GetSize(order) >= cone_limit) return false;
			result_index[bit] = GetSize(order);
			order.push_back(driver);
			return true;
		};
		for (auto &observer : observers)
			if (!expand(observer.ena, 0)) return false;
		int nb = GetSize(boundary), n = GetSize(frontier);
		if (n > 10) return false;
		int rows = 1 << n;
		int64_t row_work = 1 + GetSize(observers);
		for (auto cell : order) row_work += 1 + GetSize(cell->getPort(ID::A));
		if (!resources.spend(int64_t(rows) * row_work)) return false;
		// 原图在本次求值期间保持不变，提前取得真值表与 canonical 输入。
		struct EvaluatedCell { Const table; std::vector<SigBit> inputs; };
		std::vector<EvaluatedCell> functions;
		for (auto cell : order) {
			EvaluatedCell function {lutresyn_logic_table(cell), {}};
			for (auto bit : cell->getPort(ID::A)) function.inputs.push_back(canonical(bit));
			functions.push_back(std::move(function));
		}
		std::vector<uint8_t> values(n), results(order.size()), care(rows), old_value(rows);
		std::map<uint32_t, bool> constraints;
		auto value_of = [&](SigBit bit) -> bool {
			if (!bit.wire) return bit == State::S1;
			auto f = frontier_index.find(bit);
			if (f != frontier_index.end()) return values[f->second];
			auto r = result_index.find(bit);
			log_assert(r != result_index.end());
			return results[r->second];
		};
		uint32_t boundary_mask = nb == 0 ? 0 : (uint32_t(1) << nb) - 1;
		for (int row = 0; row < rows; row++) {
			for (int i = 0; i < n; i++) values[i] = (row >> i) & 1;
			for (int index = 0; index < GetSize(order); index++) {
				const auto &function = functions[index];
				int address = 0;
				for (int i = 0; i < GetSize(function.inputs); i++) address |= int(value_of(function.inputs[i])) << i;
				results[index] = function.table[address] == State::S1;
			}
			bool observed = false;
			for (auto &observer : observers)
				if (value_of(observer.ena)) { observed = true; break; }
			old_value[row] = results[result_index.at(output)];
			care[row] = observed;
			if (observed) {
				auto entry = constraints.emplace(uint32_t(row) & boundary_mask, old_value[row]);
				log_assert(entry.second || entry.first->second == old_value[row]);
			}
		}
		// 每一种数据 boundary 赋值都被观察时该根没有观察自由度，结束该候选并
		// 留给后续原 opt_lutresyn 处理普通无条件重综合。
		if (GetSize(constraints) == (1 << nb)) return false;
		std::vector<std::pair<uint32_t, bool>> items(constraints.begin(), constraints.end());
		// support 按规模递增枚举，同规模取增益最好、support 最少、次序稳定的一份。
		NativeFfLut4Fit best;
		bool found = false;
		for (int size = 0; size <= std::min(4, nb) && !found; size++) {
			NativeFfLut4Fit size_best;
			bool have = false;
			for (uint32_t mask = 0; mask < (uint32_t(1) << nb); mask++) {
				int count = 0;
				for (int i = 0; i < nb; i++) count += (mask >> i) & 1;
				if (count != size) continue;
				if (!resources.spend(4)) return false;
				NativeFfLut4Fit candidate;
				if (!fit_subset(mask, nb, items, candidate)) continue;
				if (!have || candidate.cost < size_best.cost ||
				    (candidate.cost == size_best.cost && GetSize(candidate.support) < GetSize(size_best.support))) {
					size_best = candidate; have = true;
				}
			}
			if (have) { best = size_best; found = true; }
		}
		if (!found || !verify_fit(best, rows, care, old_value)) return false;
		fit = best;
		return true;
	}

	// 初始化只建立一次数据根集合。
	void collect_initial_roots() {
		for (auto name : qualified_ffs) {
			if (!resources.spend(4)) return;
			Cell *ff = module->cell(name);
			if (!ff) continue;
			Cell *driver = unique_driver(canonical(ff->getPort(ID(d))[0]));
			if (!driver || !valid_lut(driver, true)) continue;
			pending.insert(driver->name);
		}
	}

	// 实际替换：删除闭包单元，按拟合函数继续驱动原 D 信号。
	// 提交之前 work 与 memory 已经完整取得，此处不再进行可能耗尽的分配。
	void commit(SigBit output, const std::set<IdString> &deleting, const NativeFfLut4Fit &fit,
	            const std::vector<NativeFfLut4Observer> &observers) {
		std::set<IdString> affected;
		auto it = users.find(output);
		if (it != users.end())
			for (auto name : it->second) if (!deleting.count(name)) affected.insert(name);
		// 别名建立之前按现有索引移除，别名建立之后再按当前连接重建。
		for (auto name : deleting) index_erase(name);
		for (auto name : affected) index_erase(name);
		for (auto name : deleting) { pending.erase(name); module->remove(module->cell(name)); }
		Cell *created = nullptr;
		if (GetSize(fit.support) == 0) {
			SigBit value = fit.table.get(0) ? State::S1 : State::S0;
			module->connect(output, value);
			redirects[output] = value;
		} else if (GetSize(fit.support) == 1 && fit.table.get(1)) {
			module->connect(output, fit.support[0]);
			redirects[output] = fit.support[0];
			if (ports_out.erase(output)) ports_out.insert(fit.support[0]);
		} else {
			Const table(State::S0, 1 << GetSize(fit.support));
			for (int i = 0; i < GetSize(table); i++) table.set(i, fit.table.get(i) ? State::S1 : State::S0);
			created = module->addLut(NEW_ID, SigSpec(fit.support), SigSpec(output), table);
		}
		for (auto name : affected) index_add(module->cell(name));
		if (created) index_add(created);
		removed += GetSize(deleting);
		added += created ? 1 : 0;
		// 候选更新只依据本次实际受影响的观察者重新定根。
		for (auto &observer : observers) {
			Cell *ff = module->cell(observer.ff);
			if (!ff) continue;
			Cell *driver = unique_driver(canonical(ff->getPort(ID(d))[0]));
			if (driver && !attempted.count(driver->name) && valid_lut(driver, true)) pending.insert(driver->name);
		}
	}

	// 删除闭包：非根节点的全部消费者必须留在闭包内部，按当前真实连接计算。
	bool deletion_closure(const std::set<IdString> &nodes, IdString root_name, std::set<IdString> &deleting) {
		deleting = nodes;
		bool changed = true;
		while (changed) {
			changed = false;
			for (auto name : nodes) {
				if (name == root_name || !deleting.count(name)) continue;
				if (!resources.spend(4)) return false;
				SigBit bit = canonical(module->cell(name)->getPort(ID::Y)[0]);
				bool external = ports_out.count(bit);
				auto it = users.find(bit);
				if (!external && it != users.end())
					for (auto user : it->second) if (!deleting.count(user)) { external = true; break; }
				if (external) { deleting.erase(name); changed = true; }
			}
		}
		return true;
	}

	void process(IdString root_name) {
		Cell *root = module->cell(root_name);
		if (!root || !valid_lut(root, true)) return;
		SigBit output = canonical(root->getPort(ID::Y)[0]);
		// 根的直接前驱按当前真实连接与资格收集，固定次序，不向更深层次扩展。
		std::vector<IdString> predecessors;
		for (auto bit : root->getPort(ID::A)) {
			if (!resources.spend(4)) return;
			Cell *driver = unique_driver(canonical(bit));
			if (!driver || driver->name == root->name || !valid_lut(driver, true)) continue;
			if (std::find(predecessors.begin(), predecessors.end(), driver->name) == predecessors.end())
				predecessors.push_back(driver->name);
		}
		// 先完成根资格与全部真实输入端口观察者检查；严格观察者与恒 1 ENA 结束该根。
		std::vector<NativeFfLut4Observer> required;
		{
			std::set<IdString> alone {root->name};
			if (!collect_observers(output, alone, required)) return;
		}
		if (required.empty()) return;
		for (auto &observer : required)
			if (observer.ena == State::S1) return;
		analyzed++;
		int64_t consumers = users.count(output) ? int64_t(GetSize(users.at(output))) : 0;
		// 根加直接前驱的有限子集（根最多四个输入，最多 16 种），按删除闭包去重后
		// 逐个完成完整前沿与观察域证明，只比较已证明计划的真实删除数减新增数。
		std::set<std::set<IdString>> seen;
		std::set<IdString> best_deleting;
		std::vector<NativeFfLut4Observer> best_observers;
		NativeFfLut4Fit best_fit;
		int64_t best_gain = 0, best_support = 0, best_index = 0;
		for (uint32_t mask = 0; mask < (uint32_t(1) << GetSize(predecessors)); mask++) {
			if (resources.stopped || resources.local_stopped) break;
			if (!resources.spend(8)) break;
			std::set<IdString> nodes {root->name};
			for (int i = 0; i < GetSize(predecessors); i++)
				if (mask & (uint32_t(1) << i)) nodes.insert(predecessors[i]);
			std::set<IdString> deleting;
			if (!deletion_closure(nodes, root->name, deleting)) break;
			if (!seen.insert(deleting).second) continue;
			// 逐候选容器按实际消费者数量与算法有限上限在分配之前完整预留。
			LutResynReservation candidate_storage(resources);
			if (!candidate_storage.reserve(262144 + 1024 * consumers)) break;
			std::vector<NativeFfLut4Observer> observers;
			if (!collect_observers(output, deleting, observers)) break;
			if (observers.empty()) continue;
			NativeFfLut4Fit fit;
			if (!analyze(output, deleting, observers, fit)) continue;
			int64_t gain = int64_t(GetSize(deleting)) - fit.cost;
			int64_t support = GetSize(fit.support);
			if (gain <= 0) continue;
			if (gain > best_gain || (gain == best_gain && (support < best_support ||
			    (support == best_support && mask < best_index)))) {
				best_gain = gain; best_support = support; best_index = mask;
				best_deleting = std::move(deleting);
				best_observers = std::move(observers);
				best_fit = fit;
			}
		}
		if (!best_gain) return;
		// 提交所需 work 与 memory 完整取得之后才执行全部实际修改。
		int64_t commit_work = 128 + 32 * int64_t(GetSize(best_deleting) + GetSize(best_observers));
		int64_t commit_memory = 256 * int64_t(GetSize(best_deleting) + GetSize(best_observers) + 4);
		if (!resources.reserve(commit_memory)) return;
		if (!resources.hold_commit(commit_work)) { resources.release(commit_memory); return; }
		resources.consume_commit();
		commit(output, best_deleting, best_fit, best_observers);
		resources.release(commit_memory);
		accepted++;
	}

	NativeFfLut4Worker(Module *module, Design *design, LutResynOptions options) :
		module(module), sigmap(module), types(design),
		native_dffeas(LutFfBoundary::native_dffeas_declared(design, types)), resources(options)
	{
		// 索引与候选容器按实际模块规模在分配之前完整预留。
		LutResynReservation index_storage(resources);
		int64_t index_bytes = 512 + 1024 * int64_t(module->cells_size()) + 256 * int64_t(module->wires_size());
		for (auto wire : module->wires()) index_bytes += 128 * int64_t(wire->width);
		if (!index_storage.reserve(index_bytes)) return;
		for (auto wire : module->wires())
			for (auto bit : SigSpec(wire)) {
				if (!resources.spend(1)) return;
				bit = canonical(bit);
				if (wire->port_input) { ports_in.insert(bit); input_driver_counts[bit]++; }
				if (wire->port_output) ports_out.insert(bit);
				if (wire->get_bool_attribute(ID::keep) || wire->get_bool_attribute(ID::lut_keep) || wire->attributes.count(ID::init)) protected_bits.insert(bit);
			}
		for (auto cell : module->cells()) {
			if (!resources.spend(8)) return;
			index_add(cell);
		}
		for (auto cell : module->cells()) {
			if (!resources.spend(4)) return;
			if (qualified_ff(cell)) qualified_ffs.push_back(cell->name);
		}
		collect_initial_roots();
		{
			// ResynSearch 只包实际搜索，setup 由外层 Resyn 总时间减该差值计入。
			Lut4Mapping::PostTimer search_timer(Lut4Mapping::timed_post_design(design), Lut4Mapping::PostPhase::ResynSearch);
			while (!pending.empty() && !resources.stopped) {
				resources.local_stopped = false;
				resources.local_limit = std::min<int64_t>(resources.work_limit, resources.work + 250000);
				if (!resources.spend(16)) break;
				IdString root = *pending.begin();
				pending.erase(pending.begin());
				attempted.insert(root);
				process(root);
				resources.commit_credit = 0;
				resources.local_limit = -1;
				resources.local_stopped = false;
			}
		}
		log("  opt_native_ff_lut4: %s: %lld candidates, %lld accepted, %lld FF and %lld strict observations, %lld deleted, %lld added, gain %lld.\n",
		    log_id(module), (long long)analyzed, (long long)accepted, (long long)ff_observers, (long long)strict_observers,
		    (long long)removed, (long long)added, (long long)(removed - added));
		log("  opt_native_ff_lut4: search work %lld/%lld, accounted peak memory %lld/%lld bytes, budget %s.\n",
		    (long long)resources.work, (long long)resources.work_limit, (long long)resources.peak_memory,
		    (long long)resources.memory_limit, resources.stopped ? "exhausted" : "available");
	}
};

struct OptNativeFfLut4Pass : Pass
{
	OptNativeFfLut4Pass() : Pass("opt_native_ff_lut4", "fit native FF data observation domains into four-input LUTs") {}
	void help() override {
		log("\n    opt_native_ff_lut4 [options] [selection]\n\n");
		log("Fit the data input of native dffeas registers in FF_MAP form (prn=1 and\n");
		log("aload/asdata/sclr/sload=0) into one LUT with at most four inputs, using the\n");
		log("actual enable observation domain of the data signal. Every root considers the\n");
		log("finite subsets of its real ordinary LUT/one-bit NOT direct predecessors, with\n");
		log("each subset plus the root reduced by the actual deletion closure, and compares\n");
		log("only fully proven plans by true deletions minus new cells. Enables are\n");
		log("expanded through real LUT/NOT logic only; multiple or invalid combinational\n");
		log("drivers and unknown constants end the root, and the bounded local ordering\n");
		log("ends candidates without a valid dependency order. Roots with a strict\n");
		log("observer, with a constant-one enable, or with every data-boundary assignment\n");
		log("observed are left to the following exact resynthesis. Constants and direct\n");
		log("wires cost nothing; ordinary new LUT/NOT cells cost one, and only positive\n");
		log("actual gain is committed. Registers, ports, parameters, attributes,\n");
		log("initialization and the original data signal are preserved.\n\n");
		log("    -max-work N         total search work per module (1..16000000, default 16000000)\n");
		log("    -max-memory N       accounted search memory in MiB (1..64, default 64)\n\n");
		log("The pass shares the existing resyn work and memory account when it runs in\n");
		log("the shared post-mapping coordinator and uses local limits otherwise.\n\n");
	}
	void execute(vector<std::string> args, Design *design) override {
		log_header(design, "Executing OPT_NATIVE_FF_LUT4 pass (native FF observation-domain LUT4 fitting).\n");
		LutResynOptions options;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			int *target = nullptr, minimum = 1, maximum = 0;
			const std::string &arg = args[argidx];
			if (arg == "-max-work") { target = &options.max_work; maximum = 16000000; }
			if (arg == "-max-memory") { target = &options.max_memory; maximum = 64; }
			if (!target) break;
			if (++argidx == args.size() || args[argidx].empty()) log_cmd_error("Expected an integer after %s.\n", arg.c_str());
			int value = 0;
			for (char ch : args[argidx]) {
				if (ch < '0' || ch > '9' || value > (maximum - (ch - '0')) / 10)
					log_cmd_error("%s requires an integer in %d..%d.\n", arg.c_str(), minimum, maximum);
				value = value * 10 + ch - '0';
			}
			if (value < minimum || value > maximum) log_cmd_error("%s requires an integer in %d..%d.\n", arg.c_str(), minimum, maximum);
			*target = value;
		}
		extra_args(args, argidx, design);
		bool shared = Lut4Mapping::shared_post(design);
		if (!shared) Lut4Mapping::reset_post_report(design, "resyn");
		for (auto module : design->selected_modules()) {
			if (module->has_processes()) log_cmd_error("opt_native_ff_lut4 requires lowered processes in %s.\n", log_id(module));
			auto module_options = options;
			if (shared) {
				int64_t remaining = std::stoll(design->scratchpad_get_string(Lut4Mapping::post_key("resyn", "remaining")));
				module_options.max_work = std::min<int64_t>(options.max_work, remaining);
				int64_t minimum = 64 + 16 * int64_t(module->cells_size()) + 8 * int64_t(module->wires_size());
				if (module_options.max_work < minimum + 16) {
					log("opt_native_ff_lut4: shared work allowance=%d from remaining=%lld below minimum index/candidate work=%lld before workspace construction in %s.\n", module_options.max_work, (long long)remaining, (long long)(minimum + 16), log_id(module));
					continue;
				}
			}
			int64_t inspection = 0;
			int64_t setup_work = Lut4Mapping::post_setup_work(module, module_options.max_work, inspection);
			Lut4Mapping::report_post(design, "resyn", inspection, 0, 0);
			module_options.max_work -= inspection;
			if (setup_work < 0) {
				log("opt_native_ff_lut4: work exhausted during index inspection in %s.\n", log_id(module));
				continue;
			}
			setup_work += 16 * int64_t(module->cells_size());
			if (module_options.max_work < setup_work + 16) {
				log("opt_native_ff_lut4: work below complete index/candidate work=%lld before workspace construction in %s.\n", (long long)(setup_work + 16), log_id(module));
				continue;
			}
			int64_t memory_limit = int64_t(options.max_memory) * 1048576;
			if (shared)
				memory_limit = std::min<int64_t>(memory_limit, std::max<int64_t>(0, std::stoll(design->scratchpad_get_string("opt_lut4_post.memory_remaining"))));
			module_options.memory_bytes = std::max<int64_t>(0, memory_limit);
			if (!module_options.max_work || !module_options.memory_bytes) {
				log("opt_native_ff_lut4: budget exhausted before workspace construction in %s.\n", log_id(module));
				continue;
			}
			Lut4Mapping::report_post(design, "resyn", setup_work, 0, 0);
			module_options.max_work -= setup_work;
			log("opt_native_ff_lut4: workspace construction work=%lld, search allowance=%lld in %s.\n",
			    (long long)setup_work, (long long)module_options.max_work, log_id(module));
			NativeFfLut4Worker worker(module, design, module_options);
			Lut4Mapping::report_post(design, "resyn", worker.resources.work, 0, worker.resources.peak_memory);
		}
	}
} OptNativeFfLut4Pass;

PRIVATE_NAMESPACE_END
