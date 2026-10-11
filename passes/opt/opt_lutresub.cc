#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "kernel/qcsat.h"
#include "opt_lut4_mapping.h"
#include "opt_lut_ff_boundary.h"

#include <array>
#include <deque>
#include <map>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ResubOptions
{
	int max_cells = 32, max_divisors = 32, max_plans = 32;
	int max_inputs = 10, max_cone = 128, max_work = Lut4Mapping::post_resub_work_limit;
	int max_memory = Lut4Mapping::post_resub_workspace / 1048576, sat_effort = Lut4Mapping::post_sat_limit, sat_query = 100000;
	int total_plans = 4096;
	int64_t memory_bytes = -1;
	bool dry_run = false;
};

struct ResubBudget
{
	int64_t work = 0, peak = 0, bytes = 0, plans = 0;
	ResubOptions opt;
	SatEffortBudget sat;
	bool stopped = false;
	int64_t slice_left = -1;
	bool slice_limited = false;
	explicit ResubBudget(ResubOptions opt) : opt(opt), sat(std::max(1, opt.sat_effort)) { sat.remaining = opt.sat_effort; }
	int64_t memory_limit() const { return opt.memory_bytes < 0 ? int64_t(opt.max_memory) * 1048576 : opt.memory_bytes; }
	bool spend(int64_t n) {
		log_assert(n >= 0);
		if (stopped) return false;
		if (n > opt.max_work - work) { stopped = true; return false; }
		if (slice_left >= 0 && n > slice_left) { slice_limited = true; return false; }
		if (slice_limited) return false;
		if (slice_left >= 0) slice_left -= n;
		work += n;
		return true;
	}
	bool reserve(int64_t n) {
		log_assert(n >= 0);
		if (stopped) return false;
		if (n > memory_limit() - bytes) { slice_limited = true; return false; }
		bytes += n; peak = std::max(peak, bytes);
		return true;
	}
	bool plan() {
		if (plans == opt.total_plans) { stopped = true; return false; }
		if (!spend(64)) return false;
		plans++;
		return true;
	}
};

struct ResubSlice
{
	ResubBudget &budget;
	explicit ResubSlice(ResubBudget &budget, int64_t limit) : budget(budget) {
		log_assert(budget.slice_left < 0);
		budget.slice_left = limit; budget.slice_limited = false;
	}
	~ResubSlice() { budget.slice_left = -1; budget.slice_limited = false; }
};

struct ResubStorage
{
	ResubBudget &budget;
	int64_t bytes = 0;
	explicit ResubStorage(ResubBudget &budget) : budget(budget) {}
	bool reserve(int64_t n) {
		if (!budget.reserve(n)) return false;
		bytes += n;
		return true;
	}
	~ResubStorage() { log_assert(bytes <= budget.bytes); budget.bytes -= bytes; }
	void clear() { log_assert(bytes <= budget.bytes); budget.bytes -= bytes; bytes = 0; }
	void release(int64_t n) { log_assert(n >= 0 && n <= bytes); bytes -= n; budget.bytes -= n; }
};

struct ResubRef
{
	SigBit bit = State::S0;
	int node = -1;
	bool phase = false;
	ResubRef() = default;
	explicit ResubRef(SigBit bit, bool phase = false) : bit(bit), phase(phase) {}
	explicit ResubRef(int node) : node(node) {}
	bool operator<(const ResubRef &rhs) const { return std::tie(node, bit, phase) < std::tie(rhs.node, rhs.bit, rhs.phase); }
	bool operator==(const ResubRef &rhs) const { return node == rhs.node && bit == rhs.bit && phase == rhs.phase; }
};

struct ResubNode { vector<ResubRef> inputs; uint16_t table = 0; };
struct ResubPlan
{
	vector<ResubNode> nodes;
	ResubRef output;
	std::set<int> needed;
	std::set<Cell *> deleting;
	int kind = 0, cost = 0, gain = 0;
	bool proven = false;
	void collect(ResubRef ref) {
		if (ref.node < 0 || !needed.insert(ref.node).second) return;
		log_assert(ref.node < GetSize(nodes));
		for (auto input : nodes[ref.node].inputs) {
			log_assert(input.node < ref.node);
			collect(input);
		}
	}
};

struct ResubRow { uint32_t divisors = 0; bool target = false; };
struct ResubRegion
{
	Cell *root = nullptr;
	SigBit output;
	std::set<Cell *> nodes;
	vector<SigBit> divisors, leaves;
	vector<bool> private_divisors;
	vector<uint32_t> retained_divisors;
	uint32_t retained_external = 0;
	vector<std::array<uint64_t, 2>> supports;
	vector<Cell *> cone;
	vector<ResubRow> rows;
	vector<vector<uint64_t>> divisor_values;
	vector<uint64_t> target_values;
	mutable std::map<vector<int>, int64_t> conflict_cache;
	uint64_t last_mask = ~uint64_t(0);
	bool exhaustive = false;
};

struct ResubLayout { int kind = 1; vector<int> bound, top; };

struct ResubFunction
{
	IdString type;
	vector<SigBit> a, b, s, y;
	bool signed_a = false, signed_b = false;
	uint16_t table = 0;
};

struct ResubEnvironment
{
	uint64_t generation;
	bool exhaustive;
	vector<SigBit> leaves;
	bool operator<(const ResubEnvironment &rhs) const {
		return std::tie(generation, exhaustive, leaves) < std::tie(rhs.generation, rhs.exhaustive, rhs.leaves);
	}
};

struct LutResubWorker
{
	Module *module;
	ModWalker walker;
	bool native_dffeas;
	ResubBudget budget;
	ResubStorage index_storage, cache_storage;
	std::map<Cell *, ResubFunction> functions;
	std::map<ResubEnvironment, std::map<SigBit, vector<uint64_t>>> value_cache;
	uint64_t generation = 0;
	int64_t cache_hits = 0, slice_limits = 0, coverage_regions = 0, continuation_regions = 0;
	std::set<SigBit> protected_bits;
	std::map<SigBit, int> input_counts;
	std::set<Cell *> unsafe;
	int64_t regions = 0, accepted = 0, deleted = 0, added = 0;
	int64_t exhaustive_proofs = 0, sat_proofs = 0, sat_limits = 0, counterexamples = 0;
	std::array<int64_t, 4> attempts {{0, 0, 0, 0}};

	SigBit canonical(SigBit bit) { return walker.sigmap(bit); }
	bool ff(Cell *cell) { return LutFfBoundary::sequential(cell, native_dffeas); }
	bool binary(const Const &value) {
		for (auto bit : value) if (bit != State::S0 && bit != State::S1) return false;
		return true;
	}
	bool bit_safe(SigBit bit) {
		bit = canonical(bit);
		if (!bit.wire) return bit == State::S0 || bit == State::S1;
		auto it = walker.signal_drivers.find(bit);
		int n = it == walker.signal_drivers.end() ? 0 : GetSize(it->second);
		auto pi = input_counts.find(bit);
		if (pi != input_counts.end()) n += pi->second;
		return n == 1;
	}
	Cell *driver(SigBit bit) {
		bit = canonical(bit);
		if (!bit.wire || input_counts.count(bit)) return nullptr;
		auto it = walker.signal_drivers.find(bit);
		if (it == walker.signal_drivers.end() || GetSize(it->second) != 1) return nullptr;
		return it->second.begin()->cell;
	}
	bool shape(Cell *cell) {
		if (!cell || unsafe.count(cell)) return false;
		if (!cell->type.in(ID($lut), ID($not), ID($_NOT_))) return false;
		for (auto &param : cell->parameters) if (GetSize(param.second) > 64) return false;
		if (!cell->hasPort(ID::A) || !cell->hasPort(ID::Y))
			log_error("opt_lutresub: invalid scalar cell %s.\n", log_id(cell));
		if (GetSize(cell->getPort(ID::Y)) != 1) {
			if (cell->type == ID($lut)) log_error("opt_lutresub: invalid scalar cell %s.\n", log_id(cell));
			return false;
		}
		if (cell->type == ID($lut)) {
			if (!cell->hasParam(ID::WIDTH) || !cell->hasParam(ID::LUT))
				log_error("opt_lutresub: missing LUT parameters in %s.\n", log_id(cell));
			if (!binary(cell->getParam(ID::WIDTH)) || !binary(cell->getParam(ID::LUT))) return false;
			int n = cell->getParam(ID::WIDTH).as_int();
			if (n < 0 || n > 4) return false;
			if (GetSize(cell->getPort(ID::A)) != n || GetSize(cell->getParam(ID::LUT)) != (1 << n))
				log_error("opt_lutresub: inconsistent LUT width in %s.\n", log_id(cell));
		} else if (GetSize(cell->getPort(ID::A)) != 1) return false;
		for (auto &param : cell->parameters) if (!binary(param.second)) return false;
		for (auto bit : cell->getPort(ID::A)) if (!bit_safe(bit)) return false;
		return driver(cell->getPort(ID::Y)[0]) == cell;
	}
	bool removable(Cell *cell) {
		return shape(cell) && module->selected(cell) && !cell->has_keep_attr() &&
		       !cell->get_bool_attribute(ID::lut_keep) && !protected_bits.count(canonical(cell->getPort(ID::Y)[0]));
	}

	// 模块连接索引仅建立一次；提交后更新实际受影响的连接。
	void add_index(Cell *cell) {
		walker.cell_inputs[cell]; walker.cell_outputs[cell];
		walker.add_cell(cell);
	}
	void erase_index(Cell *cell) {
		bool known = walker.ct.cell_known(cell->type);
		for (auto &conn : cell->connections()) {
			bool in = !known || walker.ct.cell_input(cell->type, conn.first);
			bool out = !known || walker.ct.cell_output(cell->type, conn.first);
			for (int i = 0; i < GetSize(conn.second); i++) {
				SigBit bit = canonical(conn.second[i]);
				if (!bit.wire) continue;
				ModWalker::PortBit port(cell, conn.first, i);
				if (in) {
					log_assert(walker.signal_consumers.count(bit) && walker.signal_consumers.at(bit).count(port));
					walker.signal_consumers.at(bit).erase(port);
					if (walker.signal_consumers.at(bit).empty()) walker.signal_consumers.erase(bit);
				}
				if (out) {
					log_assert(walker.signal_drivers.count(bit) && walker.signal_drivers.at(bit).count(port));
					walker.signal_drivers.at(bit).erase(port);
					if (walker.signal_drivers.at(bit).empty()) walker.signal_drivers.erase(bit);
				}
			}
		}
		walker.cell_inputs.erase(cell); walker.cell_outputs.erase(cell);
	}
	void find_cycles() {
		std::map<Cell *, int> degree;
		std::map<Cell *, std::set<Cell *>> next;
		std::deque<Cell *> ready;
		for (auto cell : module->cells()) {
			if (ff(cell)) continue;
			std::set<Cell *> prev;
			for (auto bit : walker.cell_inputs[cell]) {
				auto it = walker.signal_drivers.find(bit);
				if (it != walker.signal_drivers.end())
					for (auto port : it->second) if (!ff(port.cell)) prev.insert(port.cell);
			}
			degree[cell] = GetSize(prev);
			for (auto p : prev) next[p].insert(cell);
			if (prev.empty()) ready.push_back(cell);
		}
		while (!ready.empty()) {
			Cell *cell = ready.front(); ready.pop_front();
			for (auto n : next[cell]) { log_assert(degree.at(n) > 0); if (--degree.at(n) == 0) ready.push_back(n); }
		}
		for (auto entry : degree) if (entry.second) unsafe.insert(entry.first);
	}

	// 未完成的依赖遍历拒绝该 divisor，FF 输出结束组合依赖遍历。
	bool independent(SigBit bit, Cell *root) {
		std::set<Cell *> seen;
		vector<SigBit> pending {canonical(bit)};
		while (!pending.empty()) {
			if (!budget.spend(1)) return false;
			SigBit current = pending.back(); pending.pop_back();
			if (!bit_safe(current)) return false;
			Cell *cell = driver(current);
			if (!cell || ff(cell)) continue;
			if (cell == root || unsafe.count(cell) || !walker.ct.cell_known(cell->type)) return false;
			if (!seen.insert(cell).second) continue;
			if (GetSize(seen) > budget.opt.max_cone) return false;
			const auto &inputs = walker.cell_inputs.at(cell);
			if (GetSize(inputs) > 64 || GetSize(pending) + GetSize(inputs) > 8192 || !budget.spend(GetSize(inputs))) return false;
			for (auto input : inputs) pending.push_back(input);
		}
		return true;
	}

	bool make_region(Cell *root, ResubRegion &region) {
		if (!removable(root)) return false;
		region.root = root; region.output = canonical(root->getPort(ID::Y)[0]);
		std::deque<Cell *> pending {root};
		region.nodes.insert(root);
		while (!pending.empty()) {
			Cell *cell = pending.front(); pending.pop_front();
			for (auto bit : cell->getPort(ID::A)) {
				if (!budget.spend(4)) return false;
				Cell *prev = driver(bit);
				if (shape(prev) && !region.nodes.count(prev) && GetSize(region.nodes) < budget.opt.max_cells) {
					region.nodes.insert(prev); pending.push_back(prev);
				}
			}
		}
		std::set<SigBit> boundary, shared, internal;
		for (auto cell : region.nodes) {
			SigBit out = canonical(cell->getPort(ID::Y)[0]);
			if (cell != root) {
				bool external = !removable(cell) || walker.signal_outputs.count(out);
				auto it = walker.signal_consumers.find(out);
				if (it != walker.signal_consumers.end()) for (auto port : it->second) {
					if (!budget.spend(1)) return false;
					external |= !region.nodes.count(port.cell);
				}
				(external ? shared : internal).insert(out);
			}
			for (auto bit : cell->getPort(ID::A)) {
				bit = canonical(bit);
				if (bit.wire && !region.nodes.count(driver(bit))) boundary.insert(bit);
			}
		}
		// 共同输入附近的既有函数参与搜索，全部候选使用真实信号。
		std::set<SigBit> neighbors;
		int visits = 0;
		for (auto bit : boundary) {
			auto it = walker.signal_consumers.find(bit);
			if (it == walker.signal_consumers.end()) continue;
			for (auto port : it->second) {
				if (++visits > 128) break;
				if (!budget.spend(4)) return false;
				if (port.cell != root && shape(port.cell)) neighbors.insert(canonical(port.cell->getPort(ID::Y)[0]));
			}
			if (visits > 128) break;
		}
		std::set<SigBit> seen;
		for (const auto *group : {&shared, &neighbors, &boundary, &internal})
			for (auto bit : *group) {
				if (GetSize(region.divisors) == budget.opt.max_divisors) break;
				if (seen.insert(bit).second && independent(bit, root)) {
					region.divisors.push_back(bit); region.private_divisors.push_back(internal.count(bit));
				}
			}
		std::map<Cell *, int> positions;
		for (auto cell : region.nodes) positions.emplace(cell, GetSize(positions));
		auto retention = [&](const vector<SigBit> &signals, uint32_t &mask) {
			std::set<Cell *> visited;
			vector<SigBit> pending = signals;
			while (!pending.empty()) {
				if (!budget.spend(4)) return false;
				Cell *cell = driver(pending.back()); pending.pop_back();
				if (!cell || ff(cell) || !visited.insert(cell).second) continue;
				if (GetSize(visited) > budget.opt.max_cone) return false;
				auto position = positions.find(cell);
				if (position != positions.end()) mask |= uint32_t(1) << position->second;
				for (auto input : walker.cell_inputs.at(cell)) {
					if (!budget.spend(1)) return false;
					pending.push_back(input);
				}
			}
			return true;
		};
		vector<SigBit> externally_used(shared.begin(), shared.end());
		if (!retention(externally_used, region.retained_external)) return false;
		for (auto bit : region.divisors) {
			uint32_t mask = 0;
			if (!retention({bit}, mask)) return false;
			region.retained_divisors.push_back(mask);
		}
		return !budget.stopped;
	}

	bool evaluable(Cell *cell) {
		if (!cell || unsafe.count(cell) || ff(cell)) return false;
		if (!cell->type.in(ID($lut), ID($not), ID($_NOT_), ID($and), ID($or), ID($xor), ID($xnor),
			ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
			ID($logic_not), ID($logic_and), ID($logic_or), ID($eq), ID($ne), ID($mux),
			ID($_AND_), ID($_OR_), ID($_XOR_), ID($_XNOR_), ID($_MUX_), ID($pos), ID($buf), ID($_BUF_))) return false;
		if (!cell->hasPort(ID::Y)) log_error("opt_lutresub: missing output in %s.\n", log_id(cell));
		int bits = 0;
		for (auto &conn : cell->connections()) bits += GetSize(conn.second);
		if (bits > 64 || GetSize(cell->getPort(ID::Y)) == 0) return false;
		for (auto &param : cell->parameters) if (GetSize(param.second) > 64 || !binary(param.second)) return false;
		if (cell->type == ID($lut) && !shape(cell)) return false;
		for (auto bit : walker.cell_inputs.at(cell)) if (!bit_safe(bit)) return false;
		for (auto bit : cell->getPort(ID::Y)) if (driver(bit) != cell) return false;
		return true;
	}

	bool cone_visit(SigBit bit, ResubRegion &region, std::map<Cell *, int> &state, std::set<SigBit> &leaves) {
		if (!budget.spend(4)) return false;
		bit = canonical(bit);
		if (!bit_safe(bit)) return false;
		if (!bit.wire) return true;
		Cell *cell = driver(bit);
		if (!cell || ff(cell)) { leaves.insert(bit); return GetSize(leaves) <= 128; }
		if (unsafe.count(cell) || !walker.ct.cell_known(cell->type)) return false;
		if (!evaluable(cell)) {
			// 静态未定义参数始终拒绝；确定的技术单元输出保留为独立边界。
			for (auto &param : cell->parameters) {
				if (!budget.spend(GetSize(param.second)) || !binary(param.second)) return false;
			}
			for (auto &conn : cell->connections()) {
				if (!budget.spend(GetSize(conn.second))) return false;
				for (auto input : conn.second) if (!input.wire && input != State::S0 && input != State::S1) return false;
			}
			leaves.insert(bit); return GetSize(leaves) <= 128;
		}
		auto it = state.find(cell);
		if (it != state.end()) return it->second == 2;
		if (GetSize(state) == budget.opt.max_cone) return false;
		state[cell] = 1;
		for (auto input : walker.cell_inputs.at(cell)) if (!cone_visit(input, region, state, leaves)) return false;
		state[cell] = 2; region.cone.push_back(cell);
		return true;
	}

	const ResubFunction &function(Cell *cell) {
		auto it = functions.find(cell);
		if (it != functions.end()) return it->second;
		ResubFunction f;
		f.type = cell->type;
		auto copy = [&](IdString port, vector<SigBit> &bits) {
			if (cell->hasPort(port)) for (auto bit : cell->getPort(port)) bits.push_back(canonical(bit));
		};
		copy(ID::A, f.a); copy(ID::B, f.b); copy(ID::S, f.s); copy(ID::Y, f.y);
		f.signed_a = cell->hasParam(ID::A_SIGNED) && cell->getParam(ID::A_SIGNED).as_bool();
		f.signed_b = cell->hasParam(ID::B_SIGNED) && cell->getParam(ID::B_SIGNED).as_bool();
		if (cell->type == ID($lut)) f.table = cell->getParam(ID::LUT).as_int();
		return functions.emplace(cell, std::move(f)).first->second;
	}

	bool lut_words(uint16_t table, const vector<uint64_t> &inputs, uint64_t mask, uint64_t &result) {
		log_assert(GetSize(inputs) <= 4);
		if (!budget.spend((1 << GetSize(inputs)) + 4 * ((1 << GetSize(inputs)) - 1))) return false;
		std::array<uint64_t, 16> values {};
		int size = 1 << GetSize(inputs);
		for (int i = 0; i < size; i++) values[i] = ((table >> i) & 1) ? mask : 0;
		for (auto input : inputs) {
			for (int i = 0; i < size; i += 2) values[i / 2] = (~input & values[i]) | (input & values[i + 1]);
			size /= 2;
		}
		result = values[0] & mask;
		return true;
	}

	bool evaluate(const ResubFunction &f, int word, uint64_t mask, std::map<SigBit, vector<uint64_t>> &values) {
		// 每个块预留端口访问、扩展、归约与输出运算的完整费用。
		if (!budget.spend(16 + 8 * (GetSize(f.a) + GetSize(f.b) + GetSize(f.s) + GetSize(f.y)))) return false;
		auto get = [&](SigBit bit) { return bit.wire ? values.at(bit).at(word) : bit == State::S1 ? mask : uint64_t(0); };
		vector<uint64_t> a, b, s;
		for (auto bit : f.a) a.push_back(get(bit));
		for (auto bit : f.b) b.push_back(get(bit));
		for (auto bit : f.s) s.push_back(get(bit));
		auto extended = [&](const vector<uint64_t> &v, int i, bool sign) {
			return i < GetSize(v) ? v[i] : sign && !v.empty() ? v.back() : uint64_t(0);
		};
		auto reduce = [&](const vector<uint64_t> &v, int operation) {
			uint64_t result = operation == 0 ? mask : 0;
			for (auto bit : v) result = operation == 0 ? result & bit : operation == 1 ? result | bit : result ^ bit;
			return result;
		};
		vector<uint64_t> result(f.y.size(), 0);
		if (f.type == ID($lut)) {
			log_assert(GetSize(result) == 1);
			if (!lut_words(f.table, a, mask, result[0])) return false;
		} else if (f.type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor),
		                    ID($logic_not), ID($logic_and), ID($logic_or), ID($eq), ID($ne))) {
			uint64_t r = 0;
			if (f.type.in(ID($eq), ID($ne))) {
				r = mask;
				bool sign = f.signed_a && f.signed_b;
				for (int i = 0; i < std::max(GetSize(a), GetSize(b)); i++) r &= ~(extended(a, i, sign) ^ extended(b, i, sign));
				if (f.type == ID($ne)) r = ~r;
			} else if (f.type.in(ID($logic_and), ID($logic_or))) {
				uint64_t x = reduce(a, 1), y = reduce(b, 1);
				r = f.type == ID($logic_and) ? x & y : x | y;
			} else {
				int operation = f.type == ID($reduce_and) ? 0 : f.type.in(ID($reduce_xor), ID($reduce_xnor)) ? 2 : 1;
				r = reduce(a, operation);
				if (f.type.in(ID($reduce_xnor), ID($logic_not))) r = ~r;
			}
			result[0] = r & mask;
		} else {
			bool unary = f.type.in(ID($pos), ID($buf), ID($_BUF_), ID($not), ID($_NOT_));
			bool sign = unary ? f.signed_a : f.signed_a && f.signed_b;
			for (int i = 0; i < GetSize(result); i++) {
				uint64_t x = extended(a, i, sign), y = extended(b, i, sign), r;
				if (f.type.in(ID($pos), ID($buf), ID($_BUF_))) r = x;
				else if (f.type.in(ID($not), ID($_NOT_))) r = ~x;
				else if (f.type.in(ID($and), ID($_AND_))) r = x & y;
				else if (f.type.in(ID($or), ID($_OR_))) r = x | y;
				else if (f.type.in(ID($xor), ID($_XOR_))) r = x ^ y;
				else if (f.type.in(ID($xnor), ID($_XNOR_))) r = ~(x ^ y);
				else {
					log_assert(f.type.in(ID($mux), ID($_MUX_)) && GetSize(s) == 1);
					r = (~s[0] & x) | (s[0] & y);
				}
				result[i] = r & mask;
			}
		}
		for (int i = 0; i < GetSize(f.y); i++) values.at(f.y[i])[word] = result[i];
		return true;
	}

	bool prepare(ResubRegion &region, ResubStorage &storage) {
		std::map<Cell *, int> state;
		std::set<SigBit> leaves;
		if (!cone_visit(region.output, region, state, leaves)) return false;
		for (auto bit : region.divisors) if (!cone_visit(bit, region, state, leaves)) return false;
		region.leaves.assign(leaves.begin(), leaves.end());
		int64_t connection_bits = 0;
		for (auto cell : region.cone) for (auto &conn : cell->connections()) connection_bits += GetSize(conn.second);
		// 包含样本、计划副本、连接容器和受限 SAT 的保守空间预留。
		if (!storage.reserve(1048576 + connection_bits * 4096)) return false;
		std::map<SigBit, std::array<uint64_t, 2>> supports;
		supports[State::S0] = {}; supports[State::S1] = {};
		for (int i = 0; i < GetSize(region.leaves); i++) supports[region.leaves[i]][i / 64] = uint64_t(1) << (i % 64);
		for (auto cell : region.cone) {
			std::array<uint64_t, 2> support {};
			for (auto input : walker.cell_inputs.at(cell)) {
				if (!budget.spend(4)) return false;
				const auto &prev = supports.at(input);
				for (int i = 0; i < 2; i++) support[i] |= prev[i];
			}
			for (auto bit : cell->getPort(ID::Y)) supports.emplace(canonical(bit), support);
		}
		for (auto bit : region.divisors) region.supports.push_back(supports.at(bit));
		region.exhaustive = GetSize(region.leaves) <= budget.opt.max_inputs;
		int rows = region.exhaustive ? (1 << GetSize(region.leaves)) : 1024;
		int words = (rows + 63) / 64;
		region.last_mask = rows % 64 ? (uint64_t(1) << (rows % 64)) - 1 : ~uint64_t(0);
		ResubEnvironment environment {generation, region.exhaustive, region.leaves};
		std::map<SigBit, vector<uint64_t>> values;
		auto cached = value_cache.find(environment);
		auto load = [&](SigBit bit) {
			if (values.count(bit)) return true;
			if (cached == value_cache.end()) return false;
			auto it = cached->second.find(bit);
			if (it == cached->second.end()) return false;
			if (!budget.spend(words)) return false;
			values.emplace(bit, it->second); cache_hits++;
			return true;
		};
		for (int i = 0; i < GetSize(region.leaves); i++) {
			SigBit bit = region.leaves[i];
			if (load(bit)) continue;
			if (!budget.spend(int64_t(rows) * (region.exhaustive ? 4 : 16))) return false;
			vector<uint64_t> pattern(words, 0);
			for (int row = 0; row < rows; row++) {
				uint64_t hash = uint64_t(row + 1) * 0x9e3779b97f4a7c15ull + uint64_t(i + 1) * 0xbf58476d1ce4e5b9ull;
				hash = (hash ^ (hash >> 30)) * 0xbf58476d1ce4e5b9ull;
				hash = (hash ^ (hash >> 27)) * 0x94d049bb133111ebull;
				bool value = region.exhaustive ? ((row >> i) & 1) : row == 0 ? false : row == 1 ? true : ((hash ^ (hash >> 31)) & 1);
				if (value) pattern[row / 64] |= uint64_t(1) << (row % 64);
			}
			values.emplace(bit, std::move(pattern));
		}
		for (auto cell : region.cone) {
			const auto &f = function(cell);
			bool ready = true;
			for (auto bit : f.y) ready &= load(bit);
			if (ready) continue;
			for (auto bit : f.y) values[bit] = vector<uint64_t>(words, 0);
			for (int word = 0; word < words; word++)
				if (!evaluate(f, word, word + 1 == words ? region.last_mask : ~uint64_t(0), values)) return false;
		}
		int64_t cache_bytes = 256 + GetSize(region.leaves) * 32 + GetSize(values) * (128 + 8 * words);
		if (cache_bytes <= 4194304) {
			int64_t additional = cached == value_cache.end() ? cache_bytes : 0;
			if (cached != value_cache.end()) for (const auto &entry : values)
				if (!cached->second.count(entry.first)) additional += 128 + 8 * words;
			if (cache_storage.bytes + additional > 4194304) {
				value_cache.clear(); cache_storage.clear(); cached = value_cache.end(); additional = cache_bytes;
			}
			if (!cache_storage.reserve(additional)) return false;
			if (!budget.spend(int64_t(values.size()) * words)) return false;
			auto &destination = value_cache[environment];
			for (auto &entry : values) destination.emplace(entry.first, entry.second);
		}
		region.target_values = values.at(region.output);
		for (auto bit : region.divisors) region.divisor_values.push_back(values.at(bit));
		if (!budget.spend(int64_t(rows) * (GetSize(region.divisors) + 1))) return false;
		region.rows.resize(rows);
		for (int row = 0; row < rows; row++) {
			region.rows[row].target = (region.target_values[row / 64] >> (row % 64)) & 1;
			for (int d = 0; d < GetSize(region.divisors); d++)
				if ((region.divisor_values[d][row / 64] >> (row % 64)) & 1) region.rows[row].divisors |= uint32_t(1) << d;
		}
		return true;
	}

	int code(const ResubRow &row, const vector<int> &inputs) {
		int result = 0;
		for (int i = 0; i < GetSize(inputs); i++) result |= ((row.divisors >> inputs[i]) & 1) << i;
		return result;
	}
	int64_t conflicts(const ResubRegion &region, const vector<int> &inputs) {
		log_assert(GetSize(inputs) <= 7);
		vector<int> key = inputs;
		std::sort(key.begin(), key.end());
		if (!budget.spend(16 + GetSize(key) * GetSize(key))) return -1;
		auto cached = region.conflict_cache.find(key);
		if (cached != region.conflict_cache.end()) return cached->second;
		vector<vector<uint64_t>> groups;
		if (!cover_groups(region, key, groups)) return -1;
		int64_t total = 0;
		for (const auto &group : groups) {
			int64_t zero = 0, one = 0;
			for (int word = 0; word < GetSize(group); word++) {
				if (!budget.spend(7)) return -1;
				one += __builtin_popcountll(group[word] & region.target_values[word]);
				zero += __builtin_popcountll(group[word] & ~region.target_values[word]);
			}
			total += zero * one;
		}
		if (GetSize(region.conflict_cache) < 256) region.conflict_cache.emplace(std::move(key), total);
		return total;
	}
	bool cover_groups(const ResubRegion &region, const vector<int> &inputs, vector<vector<uint64_t>> &groups) {
		groups.emplace_back(region.target_values.size(), ~uint64_t(0));
		groups[0].back() = region.last_mask;
		for (int d : inputs) {
			vector<vector<uint64_t>> next;
			for (const auto &group : groups) {
				vector<uint64_t> zero(group.size()), one(group.size());
				uint64_t any_zero = 0, any_one = 0;
				for (int word = 0; word < GetSize(group); word++) {
					if (!budget.spend(6)) return false;
					one[word] = group[word] & region.divisor_values[d][word];
					zero[word] = group[word] & ~region.divisor_values[d][word];
					any_zero |= zero[word]; any_one |= one[word];
				}
				if (any_zero) next.push_back(std::move(zero));
				if (any_one) next.push_back(std::move(one));
			}
			groups = std::move(next);
		}
		return true;
	}
	int64_t split_conflicts(const ResubRegion &region, const vector<vector<uint64_t>> &groups, int divisor) {
		int64_t total = 0;
		for (const auto &group : groups) {
			std::array<int64_t, 4> count {};
			for (int word = 0; word < GetSize(group); word++) {
				if (!budget.spend(14)) return -1;
				uint64_t one = group[word] & region.divisor_values[divisor][word];
				uint64_t zero = group[word] & ~region.divisor_values[divisor][word];
				count[0] += __builtin_popcountll(zero & ~region.target_values[word]);
				count[1] += __builtin_popcountll(zero & region.target_values[word]);
				count[2] += __builtin_popcountll(one & ~region.target_values[word]);
				count[3] += __builtin_popcountll(one & region.target_values[word]);
			}
			total += count[0] * count[1] + count[2] * count[3];
		}
		return total;
	}
	int retained_inputs(const ResubRegion &region, const vector<int> &inputs) {
		if (!budget.spend(2 + GetSize(inputs))) return -1;
		uint32_t retained = region.retained_external;
		for (int d : inputs) retained |= region.retained_divisors.at(d);
		return __builtin_popcount(retained);
	}
	bool greedy(const ResubRegion &region, vector<int> &inputs, int limit, int seed, bool include_private) {
		if (seed >= 0 && seed < GetSize(region.divisors) && (include_private || !region.private_divisors[seed])) inputs.push_back(seed);
		while (GetSize(inputs) < limit) {
			int64_t best = conflicts(region, inputs);
			if (best < 0) return false;
			if (!best) break;
			vector<vector<uint64_t>> groups;
			if (!cover_groups(region, inputs, groups)) return false;
			int selected = -1;
			std::array<uint64_t, 2> covered {};
			for (int d : inputs) for (int i = 0; i < 2; i++) covered[i] |= region.supports[d][i];
			int best_overlap = 129, best_fresh = -1, best_retained = 33;
			for (int i = 0; i < GetSize(region.divisors); i++) {
				if (!include_private && region.private_divisors[i]) continue;
				if (std::find(inputs.begin(), inputs.end(), i) != inputs.end()) continue;
				vector<int> key = inputs; key.push_back(i); std::sort(key.begin(), key.end());
				int retained = retained_inputs(region, key);
				if (retained < 0) return false;
				auto cached = region.conflict_cache.find(key);
				int64_t remaining = cached == region.conflict_cache.end() ? split_conflicts(region, groups, i) : cached->second;
				if (remaining < 0) return false;
				if (GetSize(region.conflict_cache) < 256) region.conflict_cache.emplace(std::move(key), remaining);
				if (!budget.spend(16 + GetSize(inputs) * GetSize(inputs))) return false;
				int overlap = 0, fresh = 0;
				for (int word = 0; word < 2; word++) {
					uint64_t common = covered[word] & region.supports[i][word], added = ~covered[word] & region.supports[i][word];
					overlap += __builtin_popcountll(common);
					fresh += __builtin_popcountll(added);
				}
				if (selected < 0 || remaining < best || (remaining == best &&
				    (retained < best_retained || (retained == best_retained &&
				     (overlap < best_overlap || (overlap == best_overlap && fresh > best_fresh)))))) {
					best = remaining; selected = i; best_overlap = overlap; best_fresh = fresh; best_retained = retained;
				}
			}
			if (selected < 0) break;
			inputs.push_back(selected);
		}
		return true;
	}
	bool structural_cover(const ResubRegion &region, vector<int> &best) {
		std::map<SigBit, int> divisors;
		for (int i = 0; i < GetSize(region.divisors); i++) divisors.emplace(region.divisors[i], i);
		vector<int> initial;
		for (auto bit : region.root->getPort(ID::A)) {
			bit = canonical(bit);
			if (!bit.wire) continue;
			auto it = divisors.find(bit);
			if (it == divisors.end()) return false;
			initial.push_back(it->second);
		}
		std::sort(initial.begin(), initial.end());
		initial.erase(std::unique(initial.begin(), initial.end()), initial.end());
		vector<vector<int>> frontier {initial};
		std::set<vector<int>> seen {initial};
		int best_retained = retained_inputs(region, best);
		if (best_retained < 0) return false;
		int64_t remaining = conflicts(region, best);
		if (remaining < 0) return false;
		if (remaining) best_retained = 33;
		for (int depth = 0; depth <= GetSize(region.nodes) && !frontier.empty(); depth++) {
			vector<std::pair<int, vector<int>>> next;
			for (const auto &cut : frontier) {
				int retained = retained_inputs(region, cut);
				if (retained < 0) return false;
				if (retained < best_retained || (retained == best_retained && cut.size() < best.size())) {
					best = cut; best_retained = retained;
				}
				for (int d : cut) {
					Cell *cell = driver(region.divisors[d]);
					if (!cell || !region.nodes.count(cell) || !shape(cell)) continue;
					if (!budget.spend(16 + GetSize(cut) + GetSize(cell->getPort(ID::A)))) return false;
					vector<int> expanded;
					for (int input : cut) if (input != d) expanded.push_back(input);
					bool available = true;
					for (auto bit : cell->getPort(ID::A)) {
						bit = canonical(bit);
						if (!bit.wire) continue;
						auto it = divisors.find(bit);
						if (it == divisors.end()) { available = false; break; }
						expanded.push_back(it->second);
					}
					std::sort(expanded.begin(), expanded.end());
					expanded.erase(std::unique(expanded.begin(), expanded.end()), expanded.end());
					if (!available || GetSize(expanded) > 4 || !seen.insert(expanded).second) continue;
					retained = retained_inputs(region, expanded);
					if (retained < 0) return false;
					next.emplace_back(retained, std::move(expanded));
				}
			}
			if (!budget.spend(16 * GetSize(next) * GetSize(next))) return false;
			std::sort(next.begin(), next.end());
			frontier.clear();
			for (int i = 0; i < std::min(8, GetSize(next)); i++) frontier.push_back(std::move(next[i].second));
		}
		return true;
	}
	ResubLayout layout(const ResubRegion &region, int iteration) {
		ResubLayout result;
		result.kind = iteration % 3 + 1;
		int variant = iteration / 3;
		if (result.kind == 1 && variant >= 1 && variant <= 3) {
			std::set<SigBit> cut;
			for (auto bit : region.root->getPort(ID::A)) if (canonical(bit).wire) cut.insert(canonical(bit));
			for (int step = 1; step < variant; step++) {
				bool expanded = false;
				for (auto bit : cut) {
					if (!budget.spend(128)) return result;
					Cell *cell = driver(bit);
					if (!cell || !region.nodes.count(cell) || !shape(cell)) continue;
					auto next = cut; next.erase(bit);
					for (auto input : cell->getPort(ID::A)) if (canonical(input).wire) next.insert(canonical(input));
					if (GetSize(next) > 4) continue;
					bool available = true;
					for (auto input : next) available &= std::find(region.divisors.begin(), region.divisors.end(), input) != region.divisors.end();
					if (!available) continue;
					cut = std::move(next); expanded = true; break;
				}
				if (!expanded) break;
			}
			for (auto bit : cut) {
				auto it = std::find(region.divisors.begin(), region.divisors.end(), bit);
				if (it == region.divisors.end()) { result.bound.clear(); return result; }
				result.bound.push_back(it - region.divisors.begin());
			}
			return result;
		}
		int seed = variant == 0 ? -1 : (variant - 1) % std::max(1, GetSize(region.divisors));
		bool include_private = variant % 3 != 0;
		if (result.kind == 1) {
			if (!greedy(region, result.bound, 4, seed, include_private)) return result;
			if (variant == 0) structural_cover(region, result.bound);
			return result;
		}
		greedy(region, result.top, result.kind == 2 ? 3 : 2, seed, include_private);
		vector<int> combined = result.top;
		greedy(region, combined, GetSize(result.top) + 4, -1, include_private);
		for (int i : combined) if (std::find(result.top.begin(), result.top.end(), i) == result.top.end()) result.bound.push_back(i);
		// 结构候选允许 B/T 交叠，用共同变量编码具有相关性的余因子。
		if (variant % 3 == 2 && !result.top.empty()) {
			result.bound.insert(result.bound.begin(), result.top.front());
			if (GetSize(result.bound) > 4) result.bound.resize(4);
		}
		return result;
	}

	bool color_four(const std::array<uint16_t, 16> &edges, std::array<int, 16> &colors, int used) {
		if (!budget.spend(352)) return false;
		int vertex = -1, best_saturation = -1, best_degree = -1;
		for (int i = 0; i < 16; i++) {
			if (colors[i] >= 0) continue;
			unsigned mask = 0; int degree = 0;
			for (int j = 0; j < 16; j++) if ((edges[i] >> j) & 1) {
				degree++; if (colors[j] >= 0) mask |= 1u << colors[j];
			}
			int saturation = 0;
			for (; mask; mask &= mask - 1) saturation++;
			if (saturation > best_saturation || (saturation == best_saturation && degree > best_degree)) {
				vertex = i; best_saturation = saturation; best_degree = degree;
			}
		}
		if (vertex < 0) return true;
		for (int color = 0; color < std::min(4, used + 1); color++) {
			bool valid = true;
			for (int j = 0; j < 16; j++) if (((edges[vertex] >> j) & 1) && colors[j] == color) valid = false;
			if (!valid) continue;
			colors[vertex] = color;
			if (color_four(edges, colors, std::max(used, color + 1))) return true;
			colors[vertex] = -1;
			if (budget.stopped) return false;
		}
		return false;
	}
	bool decompose(const ResubRegion &region, const ResubLayout &layout, std::array<uint16_t, 3> &tables) {
		log_assert(GetSize(layout.bound) <= 4 && GetSize(layout.top) <= (layout.kind == 2 ? 3 : 2));
		if (!budget.spend(int64_t(region.rows.size()) * 16 + 4096)) return false;
		if (layout.kind == 1) {
			std::array<int, 16> truth; truth.fill(-1);
			for (const auto &row : region.rows) {
				int a = code(row, layout.bound);
				if (truth[a] >= 0 && truth[a] != int(row.target)) return false;
				truth[a] = row.target;
			}
			for (int i = 0; i < 16; i++) if (truth[i] == 1) tables[2] |= uint16_t(1) << i;
			return true;
		}
		std::array<std::array<unsigned, 8>, 16> values {};
		for (const auto &row : region.rows) values[code(row, layout.bound)][code(row, layout.top)] |= 1u << row.target;
		std::array<uint16_t, 16> edges {};
		for (int i = 0; i < 16; i++) for (int j = i; j < 16; j++) {
			bool conflict = false;
			for (int t = 0; t < 8; t++) conflict |= ((values[i][t] & 1) && (values[j][t] & 2)) || ((values[i][t] & 2) && (values[j][t] & 1));
			if (conflict && i == j) return false;
			if (conflict) { edges[i] |= uint16_t(1) << j; edges[j] |= uint16_t(1) << i; }
		}
		std::array<int, 16> colors; colors.fill(-1);
		if (layout.kind == 2) {
			for (int i = 0; i < 16; i++) {
				if (colors[i] >= 0) continue;
				colors[i] = 0; vector<int> pending {i};
				while (!pending.empty()) {
					if (!budget.spend(17)) return false;
					int v = pending.back(); pending.pop_back();
					for (int j = 0; j < 16; j++) if ((edges[v] >> j) & 1) {
						if (colors[j] == colors[v]) return false;
						if (colors[j] < 0) { colors[j] = colors[v] ^ 1; pending.push_back(j); }
					}
				}
			}
		} else if (!color_four(edges, colors, 0)) return false;
		for (int i = 0; i < 16; i++) {
			if (colors[i] & 1) tables[0] |= uint16_t(1) << i;
			if (colors[i] & 2) tables[1] |= uint16_t(1) << i;
		}
		std::array<int, 16> h; h.fill(-1);
		for (const auto &row : region.rows) {
			int a = colors[code(row, layout.bound)] | (code(row, layout.top) << (layout.kind - 1));
			log_assert(a >= 0 && a < 16 && (h[a] < 0 || h[a] == int(row.target)));
			h[a] = row.target;
		}
		for (int i = 0; i < 16; i++) if (h[i] == 1) tables[2] |= uint16_t(1) << i;
		return true;
	}

	bool plan_words(const ResubRegion &region, const ResubPlan &plan, ResubRef output, vector<uint64_t> &signature) {
		int words = GetSize(region.target_values);
		signature.resize(words);
		for (int word = 0; word < words; word++) {
			uint64_t mask = word + 1 == words ? region.last_mask : ~uint64_t(0);
			vector<uint64_t> nodes(plan.nodes.size(), 0);
			auto value = [&](ResubRef ref) {
				uint64_t result;
				if (ref.node >= 0) result = nodes.at(ref.node);
				else if (!ref.bit.wire) result = ref.bit == State::S1 ? mask : 0;
				else {
					auto it = std::find(region.divisors.begin(), region.divisors.end(), ref.bit);
					log_assert(it != region.divisors.end());
					result = region.divisor_values.at(it - region.divisors.begin())[word];
				}
				return ref.phase ? result ^ mask : result;
			};
			for (int i = 0; i < GetSize(plan.nodes); i++) {
				const auto &node = plan.nodes[i];
				if (!budget.spend(GetSize(node.inputs) * (GetSize(region.divisors) + 2))) return false;
				vector<uint64_t> inputs;
				for (auto ref : node.inputs) inputs.push_back(value(ref));
				if (!lut_words(node.table, inputs, mask, nodes[i])) return false;
			}
			if (!budget.spend(GetSize(region.divisors) + 2)) return false;
			signature[word] = value(output);
		}
		return true;
	}
	int retained_cost(const ResubRegion &region, const ResubPlan &plan, ResubRef output) {
		uint32_t retained = region.retained_external;
		std::set<int> needed;
		vector<ResubRef> pending {output};
		while (!pending.empty()) {
			if (!budget.spend(4 + GetSize(region.divisors))) return -1;
			ResubRef ref = pending.back(); pending.pop_back();
			if (ref.node >= 0) {
				if (needed.insert(ref.node).second)
					for (auto input : plan.nodes.at(ref.node).inputs) pending.push_back(input);
			} else if (ref.bit.wire) {
				auto it = std::find(region.divisors.begin(), region.divisors.end(), ref.bit);
				log_assert(it != region.divisors.end());
				retained |= region.retained_divisors.at(it - region.divisors.begin());
			}
		}
		return __builtin_popcount(retained) + GetSize(needed) + int(output.node < 0 && output.phase && output.bit.wire);
	}
	bool synthesize(const ResubRegion &region, ResubPlan &plan, vector<ResubRef> raw, uint16_t truth, ResubRef &output) {
		if (!budget.spend(2048)) return false;
		log_assert(GetSize(raw) <= 4);
		ResubNode f;
		for (auto ref : raw) {
			ref.phase = false;
			if (ref.node >= 0 || ref.bit.wire) f.inputs.push_back(ref);
		}
		std::sort(f.inputs.begin(), f.inputs.end());
		f.inputs.erase(std::unique(f.inputs.begin(), f.inputs.end()), f.inputs.end());
		for (int a = 0; a < (1 << GetSize(f.inputs)); a++) {
			int address = 0;
			for (int i = 0; i < GetSize(raw); i++) {
				auto ref = raw[i]; bool phase = ref.phase; ref.phase = false;
				bool v = ref.bit == State::S1 && ref.node < 0;
				if (ref.node >= 0 || ref.bit.wire) v = (a >> (std::lower_bound(f.inputs.begin(), f.inputs.end(), ref) - f.inputs.begin())) & 1;
				address |= int(v ^ phase) << i;
			}
			if ((truth >> address) & 1) f.table |= uint16_t(1) << a;
		}
		for (int i = GetSize(f.inputs) - 1; i >= 0; i--) {
			bool relevant = false;
			for (int a = 0; a < (1 << GetSize(f.inputs)); a++) relevant |= ((f.table >> a) & 1) != ((f.table >> (a ^ (1 << i))) & 1);
			if (relevant) continue;
			uint16_t next = 0;
			for (int a = 0; a < (1 << (GetSize(f.inputs) - 1)); a++) {
				int full = (a & ((1 << i) - 1)) | ((a >> i) << (i + 1));
				if ((f.table >> full) & 1) next |= uint16_t(1) << a;
			}
			f.inputs.erase(f.inputs.begin() + i); f.table = next;
		}
		if (f.inputs.empty()) { output = ResubRef(SigBit((f.table & 1) ? State::S1 : State::S0)); return true; }
		if (GetSize(f.inputs) == 1 && (f.table == 2 || f.table == 1)) {
			output = f.inputs[0]; output.phase = f.table == 1; return true;
		}
		int index = GetSize(plan.nodes); log_assert(index < 3);
		plan.nodes.push_back(f);
		// 全部枚举行证明复用；抽样环境的复用随最终候选共同接受 SAT 验证。
		vector<uint64_t> signature;
		if (!plan_words(region, plan, ResubRef(index), signature)) { plan.nodes.pop_back(); return false; }
		output = ResubRef(index);
		int best_cost = retained_cost(region, plan, output);
		if (best_cost < 0) { plan.nodes.pop_back(); return false; }
		for (int d = 0; d < GetSize(region.divisors); d++) {
			if (!budget.spend(int64_t(signature.size()) * 6)) { plan.nodes.pop_back(); return false; }
			bool equal = true, complement = true;
			for (int word = 0; word < GetSize(signature); word++) {
				uint64_t difference = signature[word] ^ region.divisor_values[d][word];
				uint64_t mask = word + 1 == GetSize(signature) ? region.last_mask : ~uint64_t(0);
				equal &= difference == 0; complement &= difference == mask;
			}
			if (equal || complement) {
				ResubRef replacement(region.divisors[d], complement);
				int cost = retained_cost(region, plan, replacement);
				if (cost < 0) { plan.nodes.pop_back(); return false; }
				if (cost < best_cost) { best_cost = cost; output = replacement; }
			}
		}
		if (output.node < 0) plan.nodes.pop_back();
		return true;
	}
	bool make_plan(const ResubRegion &region, const ResubLayout &layout, const std::array<uint16_t, 3> &tables, ResubPlan &plan) {
		plan.kind = layout.kind;
		vector<ResubRef> bound, top;
		for (int d : layout.bound) bound.emplace_back(region.divisors.at(d));
		if (layout.kind == 1) return synthesize(region, plan, bound, tables[2], plan.output);
		for (int i = 0; i < layout.kind - 1; i++) {
			ResubRef bridge;
			if (!synthesize(region, plan, bound, tables[i], bridge)) return false;
			top.push_back(bridge);
		}
		for (int d : layout.top) top.emplace_back(region.divisors.at(d));
		return synthesize(region, plan, top, tables[2], plan.output);
	}

	bool price(const ResubRegion &region, ResubPlan &plan) {
		plan.collect(plan.output);
		std::set<Cell *> kept, visited;
		vector<Cell *> pending;
		auto keep = [&](Cell *cell) {
			if (!cell || ff(cell)) return;
			if (region.nodes.count(cell)) kept.insert(cell);
			if (visited.insert(cell).second) pending.push_back(cell);
		};
		for (auto cell : region.nodes) {
			if (!budget.spend(4)) return false;
			if (cell == region.root) continue;
			SigBit out = canonical(cell->getPort(ID::Y)[0]);
			if (!removable(cell) || walker.signal_outputs.count(out)) keep(cell);
			auto it = walker.signal_consumers.find(out);
			if (it != walker.signal_consumers.end()) for (auto port : it->second) {
				if (!budget.spend(1)) return false;
				if (!region.nodes.count(port.cell)) keep(cell);
			}
		}
		if (plan.output.node < 0) keep(driver(plan.output.bit));
		for (int i : plan.needed) for (auto ref : plan.nodes[i].inputs) if (ref.node < 0) keep(driver(ref.bit));
		// 既有 divisor 可以经过区域外的组合单元依赖区域内部信号。
		while (!pending.empty()) {
			Cell *cell = pending.back(); pending.pop_back();
			for (auto bit : walker.cell_inputs.at(cell)) { if (!budget.spend(4)) return false; keep(driver(bit)); }
		}
		log_assert(!kept.count(region.root));
		for (auto cell : region.nodes) if (!kept.count(cell)) {
			log_assert(removable(cell)); plan.deleting.insert(cell);
		}
		for (auto cell : plan.deleting) {
			if (cell == region.root) continue;
			SigBit out = canonical(cell->getPort(ID::Y)[0]);
			log_assert(!walker.signal_outputs.count(out));
			auto it = walker.signal_consumers.find(out);
			if (it != walker.signal_consumers.end()) for (auto port : it->second) {
				if (!budget.spend(1)) return false;
				log_assert(plan.deleting.count(port.cell));
			}
		}
		plan.cost = GetSize(plan.needed) + int(plan.output.node < 0 && plan.output.phase && plan.output.bit.wire);
		plan.gain = GetSize(plan.deleting) - plan.cost;
		return plan.gain > 0;
	}

	int sat_lut(ezSAT *ez, uint16_t table, const vector<int> &inputs) {
		vector<int> values;
		for (int i = 0; i < (1 << GetSize(inputs)); i++) values.push_back(ez->value((table >> i) & 1));
		for (int input : inputs) {
			vector<int> next;
			for (int i = 0; i < GetSize(values); i += 2) next.push_back(ez->ITE(input, values[i + 1], values[i]));
			values = std::move(next);
		}
		log_assert(GetSize(values) == 1);
		return values[0];
	}
	bool prove(const ResubRegion &region, ResubPlan &plan) {
		vector<uint64_t> signature;
		if (!plan_words(region, plan, plan.output, signature) || !budget.spend(2 * GetSize(signature))) return false;
		for (int word = 0; word < GetSize(signature); word++) log_assert(signature[word] == region.target_values[word]);
		if (region.exhaustive) { plan.proven = true; exhaustive_proofs++; return true; }
		if (budget.sat.spent()) { sat_limits++; return false; }
		if (int64_t(region.cone.size()) * SatEffortBudget::import_cell_cost > budget.sat.remaining) { sat_limits++; return false; }
		if (!budget.spend(64 + 64 * GetSize(region.cone))) return false;
		QuickConeSat query(walker);
		// 显式导入已检查的真实组合单元，避免添加属性产生的赋值约束。
		for (auto cell : region.cone) {
			log_assert(evaluable(cell) && GetSize(query.imported_cells) < budget.opt.max_cone);
			if (!query.satgen.importCell(cell)) log_error("opt_lutresub: SAT import rejected %s.\n", log_id(cell));
			query.imported_cells.insert(cell);
		}
		budget.sat.charge_import(query, 0);
		vector<int> nodes(plan.nodes.size(), 0);
		auto ref = [&](ResubRef r) {
			int value = r.node < 0 ? query.satgen.importSigBit(r.bit) : nodes.at(r.node);
			log_assert(value != 0);
			return r.phase ? query.ez->NOT(value) : value;
		};
		for (int i : plan.needed) {
			vector<int> inputs;
			for (auto r : plan.nodes[i].inputs) inputs.push_back(ref(r));
			nodes[i] = sat_lut(query.ez.get(), plan.nodes[i].table, inputs);
		}
		int mismatch = query.ez->XOR(query.satgen.importSigBit(region.output), ref(plan.output));
		query.ez->bind(mismatch);
		// Minisat 在无冲突传播后检查限额；连续冲突逐次降低决策层级。
		int64_t variables = query.ez->numCnfVariables() + 4;
		int64_t headroom = variables * variables;
		if (budget.sat.remaining <= headroom) { sat_limits++; return false; }
		int64_t cap = std::min<int64_t>(budget.opt.sat_query, budget.sat.remaining - headroom);
		int64_t work_available = budget.opt.max_work - budget.work;
		if (budget.slice_left >= 0) work_available = std::min(work_available, budget.slice_left);
		if (work_available <= headroom) { budget.slice_limited = true; return false; }
		cap = std::min(cap, work_available - headroom);
		// 初始 CNF 已包含在连接空间预留中；每次冲突最多新增一个学习子句。
		// 限额检查前最多连续发生 variables 次冲突，每个子句最多包含 variables 个文字。
		int64_t per_propagation = 256 + 32 * variables;
		int64_t available = budget.memory_limit() - budget.bytes;
		if (available / per_propagation <= variables) { sat_limits++; return false; }
		cap = std::min(cap, available / per_propagation - variables);
		ResubStorage proof_storage(budget);
		if (!proof_storage.reserve((cap + variables) * per_propagation)) return false;
		int64_t sat_before = budget.sat.remaining;
		auto result = budget.sat.solve(query, cap, {mismatch});
		log_assert(budget.spend(sat_before - budget.sat.remaining));
		log_assert(budget.sat.remaining >= 0);
		if (result == SatEffortBudget::Result::LimitReached) { sat_limits++; return false; }
		if (result == SatEffortBudget::Result::Sat) { counterexamples++; return false; }
		log_assert(result == SatEffortBudget::Result::Unsat);
		plan.proven = true; sat_proofs++;
		return true;
	}

	std::pair<int, int> counts() {
		int area = 0, flops = 0;
		for (auto cell : module->cells()) {
			area += cell->type.in(ID($lut), ID($not), ID($_NOT_));
			flops += ff(cell);
		}
		return {area, flops};
	}

	struct RootSearch {
		IdString name;
		int deleting = 0, boundary = 0, retained = 0, sharing = 0, estimate = 1, next = 0;
		std::set<std::tuple<int, vector<int>, vector<int>>> seen;
	};

	bool rank_root(Cell *root, RootSearch &rank) {
		rank.name = root->name;
		std::set<Cell *> nodes {root}, kept;
		vector<Cell *> pending {root};
		std::set<SigBit> boundary;
		while (!pending.empty()) {
			Cell *cell = pending.back(); pending.pop_back();
			for (auto bit : cell->getPort(ID::A)) {
				if (!budget.spend(8)) return false;
				Cell *prev = driver(bit);
				if (shape(prev) && !nodes.count(prev) && GetSize(nodes) < budget.opt.max_cells) {
					nodes.insert(prev); pending.push_back(prev);
				}
			}
		}
		for (auto cell : nodes) {
			SigBit out = canonical(cell->getPort(ID::Y)[0]);
			bool external = cell != root && (!removable(cell) || walker.signal_outputs.count(out));
			auto it = walker.signal_consumers.find(out);
			if (it != walker.signal_consumers.end()) for (auto port : it->second) {
				if (!budget.spend(4)) return false;
				if (!nodes.count(port.cell)) { rank.sharing++; if (cell != root) external = true; }
			}
			if (external && kept.insert(cell).second) pending.push_back(cell);
			for (auto bit : cell->getPort(ID::A)) {
				if (!budget.spend(4)) return false;
				bit = canonical(bit);
				if (bit.wire && !nodes.count(driver(bit))) boundary.insert(bit);
			}
		}
		while (!pending.empty()) {
			Cell *cell = pending.back(); pending.pop_back();
			for (auto bit : cell->getPort(ID::A)) {
				if (!budget.spend(4)) return false;
				Cell *prev = driver(bit);
				if (nodes.count(prev) && kept.insert(prev).second) pending.push_back(prev);
			}
		}
		rank.deleting = GetSize(nodes) - GetSize(kept);
		rank.retained = GetSize(kept); rank.boundary = GetSize(boundary);
		rank.estimate = 16 + rank.boundary * 8 + GetSize(nodes) * 4 + rank.retained * 16;
		return true;
	}

	void search_root(RootSearch &entry, int end, int64_t allowance, ResubStorage &queue_storage) {
		ResubSlice slice(budget, allowance);
		Cell *root = module->cell(entry.name);
		if (!root || !removable(root)) { entry.next = budget.opt.max_plans; return; }
		ResubStorage storage(budget);
		if (!storage.reserve(262144)) { slice_limits++; return; }
		ResubRegion region;
		if (!make_region(root, region) || !prepare(region, storage)) {
			if (budget.slice_limited) slice_limits++;
			else entry.next = budget.opt.max_plans;
			return;
		}
		regions++;
		ResubPlan best;
		while (entry.next < end && !budget.stopped && !budget.slice_limited) {
			auto candidate = layout(region, entry.next);
			if (budget.stopped || budget.slice_limited) break;
			auto key = std::make_tuple(candidate.kind, candidate.bound, candidate.top);
			if (entry.seen.count(key)) { entry.next++; continue; }
			// 记账沿用 SigBit 尺寸，保持既有内存额度数值不变。
			int64_t queue_bytes = 256 + (GetSize(candidate.bound) + GetSize(candidate.top)) * sizeof(SigBit);
			if (!queue_storage.reserve(queue_bytes)) break;
			if (!budget.plan()) break;
			entry.seen.insert(key); entry.next++;
			attempts[candidate.kind]++;
			auto rollback = [&]() {
				entry.seen.erase(key); entry.next--;
				queue_storage.release(queue_bytes);
			};
			std::array<uint16_t, 3> tables {};
			if (!decompose(region, candidate, tables)) {
				if (budget.slice_limited) rollback();
				continue;
			}
			ResubPlan plan;
			if (make_plan(region, candidate, tables, plan) && price(region, plan) && plan.gain > best.gain)
				if (prove(region, plan)) best = std::move(plan);
			if (budget.slice_limited) rollback();
		}
		if (budget.slice_limited) slice_limits++;
		if (best.gain > 0) commit(region, best);
	}
	void commit(const ResubRegion &region, const ResubPlan &plan) {
		log_assert(plan.proven && plan.gain > 0 && plan.deleting.count(region.root));
		log("  %s.%s: kind=%d, delete=%d, add=%d, gain=%d, proof=%s%s.\n", log_id(module), log_id(region.root),
		    plan.kind, GetSize(plan.deleting), plan.cost, plan.gain, region.exhaustive ? "enumeration" : "UNSAT", budget.opt.dry_run ? ", dry-run" : "");
		if (budget.opt.dry_run) return;
		generation++;
		value_cache.clear(); cache_storage.clear(); functions.clear();
		vector<SigBit> created(plan.nodes.size(), State::Sx);
		vector<Cell *> new_cells;
		// 使用完整的原始索引检查删除集合，随后统一移除索引。
		for (auto cell : plan.deleting) log_assert(removable(cell));
		for (auto cell : plan.deleting) { erase_index(cell); unsafe.erase(cell); }
		for (auto cell : plan.deleting) module->remove(cell);
		auto materialize = [&](ResubRef ref) {
			log_assert(!ref.phase);
			SigBit bit = ref.node < 0 ? canonical(ref.bit) : created.at(ref.node);
			log_assert(bit.wire || bit == State::S0 || bit == State::S1);
			return bit;
		};
		for (int i : plan.needed) {
			const auto &f = plan.nodes[i];
			SigSpec inputs;
			for (auto ref : f.inputs) inputs.append(materialize(ref));
			created[i] = plan.output.node == i ? region.output : SigBit(module->addWire(NEW_ID));
			Const truth(State::S0, 1 << GetSize(f.inputs));
			for (int a = 0; a < GetSize(truth); a++) truth.set(a, (((f.table >> a) & 1) ^ (plan.output.node == i && plan.output.phase)) ? State::S1 : State::S0);
			new_cells.push_back(module->addLut(NEW_ID, inputs, created[i], truth));
		}
		if (plan.output.node < 0) {
			SigBit replacement = canonical(plan.output.bit);
			log_assert(replacement != region.output);
			if (plan.output.phase && replacement.wire) new_cells.push_back(module->addNot(NEW_ID, replacement, region.output));
			else {
				if (plan.output.phase) replacement = replacement == State::S1 ? State::S0 : State::S1;
				std::set<Cell *> affected;
				auto it = walker.signal_consumers.find(region.output);
				if (it != walker.signal_consumers.end()) for (auto port : it->second) affected.insert(port.cell);
				for (auto cell : affected) erase_index(cell);
				module->connect(region.output, replacement);
				walker.sigmap.add(region.output, replacement);
				// 保持既有 replacement 的代表信号及全部关联索引。
				walker.sigmap.add(replacement);
				log_assert(canonical(region.output) == replacement);
				if (walker.signal_outputs.erase(region.output) && replacement.wire) walker.signal_outputs.insert(replacement);
				for (auto cell : affected) add_index(cell);
			}
		}
		for (auto cell : new_cells) add_index(cell);
		log_assert(GetSize(new_cells) == plan.cost);
		accepted++; deleted += GetSize(plan.deleting); added += plan.cost;
	}

	LutResubWorker(Design *design, Module *module, ResubOptions options) : module(module), walker(design, module),
		native_dffeas(LutFfBoundary::native_dffeas_declared(design, walker.ct)), budget(options),
		index_storage(budget), cache_storage(budget) {
		for (auto cell : module->cells()) { walker.cell_inputs[cell]; walker.cell_outputs[cell]; }
		for (auto wire : module->wires()) for (auto bit : SigSpec(wire)) {
			bit = canonical(bit);
			if (wire->port_input && bit.wire) input_counts[bit]++;
			if (wire->get_bool_attribute(ID::keep) || wire->attributes.count(ID::init)) protected_bits.insert(bit);
		}
		find_cycles();
		auto before = counts();
		int64_t connections = 0;
		for (auto cell : module->cells()) for (auto &conn : cell->connections()) connections += GetSize(conn.second);
		int64_t index_bytes = 512 * GetSize(module->cells()) + 192 * connections + 128 * GetSize(protected_bits);
		ResubStorage queue_storage(budget);
		vector<RootSearch> roots;
		Lut4Mapping::PostTimer search_timer(Lut4Mapping::timed_post_design(design), Lut4Mapping::PostPhase::ResubSearch);
		if (index_storage.reserve(index_bytes) && budget.spend(64 * GetSize(module->cells()) + 8 * connections)) {
			int64_t metadata_end = budget.work + (options.max_work - budget.work) / 10;
			for (auto cell : module->cells()) {
				if (budget.work >= metadata_end || budget.stopped) break;
				if (!budget.spend(16)) break;
				if (!removable(cell)) continue;
				ResubSlice slice(budget, std::min<int64_t>(50000, metadata_end - budget.work));
				RootSearch rank;
				if (rank_root(cell, rank) && queue_storage.reserve(256)) roots.push_back(std::move(rank));
			}
		}
		auto order = [](const RootSearch &a, const RootSearch &b) {
			int64_t lhs = int64_t(a.deleting) * b.estimate, rhs = int64_t(b.deleting) * a.estimate;
			if (lhs != rhs) return lhs > rhs;
			if (a.sharing != b.sharing) return a.sharing > b.sharing;
			if (a.boundary != b.boundary) return a.boundary < b.boundary;
			if (a.retained != b.retained) return a.retained < b.retained;
			return a.name < b.name;
		};
		auto sort_roots = [&]() {
			int levels = 1;
			for (int size = GetSize(roots); size > 1; size = (size + 1) / 2) levels++;
			if (!budget.spend(int64_t(roots.size()) * levels * 16)) return false;
			std::stable_sort(roots.begin(), roots.end(), order);
			return true;
		};
		if (sort_roots()) {
			// ranked_generation只在sort_roots成功之后登记；coverage中的真实提交改变generation，continuation据此重算。
			uint64_t ranked_generation = generation;
			bool ranked_complete = true;
			int64_t coverage_end = budget.work + (options.max_work - budget.work) * 3 / 5;
			for (int i = 0; i < GetSize(roots) && !budget.stopped; i++) {
				int64_t allowance = std::min<int64_t>(500000, std::max<int64_t>(0, coverage_end - budget.work) / (GetSize(roots) - i));
				coverage_regions++;
				search_root(roots[i], std::min(8, options.max_plans), allowance, queue_storage);
			}
			for (int round = 0; round < options.max_plans && !budget.stopped; round++) {
				if (ranked_generation != generation || !ranked_complete) {
					ranked_complete = true;
					for (auto &entry : roots) {
						if (entry.next >= options.max_plans) continue;
						Cell *cell = module->cell(entry.name);
						if (!cell || !removable(cell)) { entry.next = options.max_plans; continue; }
						// 局部额度失败只把这一轮评分标为未完成，其余entry与当前搜索继续。
						ResubSlice slice(budget, std::min<int64_t>(50000, options.max_work - budget.work));
						RootSearch rank;
						if (!rank_root(cell, rank)) { ranked_complete = false; continue; }
						entry.deleting = rank.deleting; entry.boundary = rank.boundary;
						entry.retained = rank.retained; entry.sharing = rank.sharing; entry.estimate = rank.estimate;
					}
					// 重评分结束后照常按实际已有评分排序，部分rank_root失败也用当前评分。
					if (!sort_roots()) break;
					if (ranked_complete) ranked_generation = generation;
				}
				// 本轮搜索中直接记录是否还有待搜索entry，无待搜索entry时结束外层round。
				bool pending = true;
				for (auto &entry : roots) {
					if (budget.stopped) break;
					if (entry.next >= options.max_plans) continue;
					pending = false;
					continuation_regions++;
					search_root(entry, entry.next + 1, std::min<int64_t>(500000, options.max_work - budget.work), queue_storage);
				}
				if (pending) break;
			}
		}
		auto after = counts();
		log_assert(before.second == after.second && before.first - after.first == deleted - added);
		log("  %s: area %d -> %d, FF %d -> %d, regions=%lld, accepted=%lld, deleted=%lld, added=%lld.\n", log_id(module),
		    before.first, after.first, before.second, after.second, (long long)regions, (long long)accepted, (long long)deleted, (long long)added);
		log("  Search work %lld/%d, workspace peak %lld/%lld bytes, plans %lld/%d, SAT effort %lld/%d, budget %s.\n",
		    (long long)budget.work, options.max_work, (long long)budget.peak, (long long)budget.memory_limit(),
		    (long long)budget.plans, options.total_plans, (long long)(options.sat_effort - budget.sat.remaining), options.sat_effort, budget.stopped ? "exhausted" : "available");
		log("  Attempts 1/2/3=%lld/%lld/%lld, enumeration=%lld, UNSAT=%lld, counterexamples=%lld, SAT limits=%lld.\n",
		    (long long)attempts[1], (long long)attempts[2], (long long)attempts[3], (long long)exhaustive_proofs,
		    (long long)sat_proofs, (long long)counterexamples, (long long)sat_limits);
		log("  Coverage regions=%lld, continuation regions=%lld, local limits=%lld, value cache hits=%lld.\n",
		    (long long)coverage_regions, (long long)continuation_regions, (long long)slice_limits, (long long)cache_hits);
	}
};

struct OptLutResubPass : Pass
{
	OptLutResubPass() : Pass("opt_lutresub", "area resubstitution with one to three LUT4s and existing divisors") {}
	void help() override {
		log("\n    opt_lutresub [options] [selection]\n\n");
		log("Search H(D), H(G(B),T), and H(G0(B),G1(B),T) using actual divisors.\n");
		log("Enumerate common independent inputs up to ten; larger environments require\n");
		log("a propagation-limited joint UNSAT proof on the real combinational network.\n");
		log("Keep shared/protected logic; count actual LUT and inverter deletions/additions.\n");
		log("Run after abc9 and before technology-specific map_cells.\n\n");
		log("    -max-cells N       region cells (1..32, default 32)\n");
		log("    -max-divisors N    actual signals (1..32, default 32)\n");
		log("    -max-plans N       candidate layouts per root (1..32, default 32)\n");
		log("    -total-plans N     layouts per module (1..1000000, default 4096)\n");
		log("    -max-inputs N      exhaustive input limit (1..10, default 10)\n");
		log("    -max-cone N        proof/dependency cells (1..128, default 128)\n");
		log("    -max-work N        module work units (1..1000000000, default 100000000)\n");
		log("    -max-memory N      search workspace MiB (1..1024, default 32)\n");
		log("    -sat-effort N      module propagation/import budget (1..1000000000, default 4000000)\n");
		log("    -sat-query N       propagation cap per proof (1..1000000000, default 100000)\n");
		log("    -dry-run           search and prove candidates without changing the module\n\n");
		log("Work includes evaluation, divisor ranking, graph coloring, reuse and proofs.\n");
		log("Workspace uses conservative container/SAT reservations; connection and cycle\n");
		log("indexes scale with the actual module. Regional tables/plans are released.\n");
		log("Undefined, cyclic and multiply-driven structures remain unchanged. Resource\n");
		log("limits stop unproved work; completed positive-gain proofs may be committed.\n\n");
	}
	void execute(vector<std::string> args, Design *design) override {
		log_header(design, "Executing OPT_LUTRESUB pass (multi-LUT area resubstitution).\n");
		ResubOptions opt;
		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			const std::string &arg = args[argidx];
			if (arg == "-dry-run") { opt.dry_run = true; continue; }
			int *target = nullptr, maximum = 0;
			if (arg == "-max-cells") { target = &opt.max_cells; maximum = 32; }
			if (arg == "-max-divisors") { target = &opt.max_divisors; maximum = 32; }
			if (arg == "-max-plans") { target = &opt.max_plans; maximum = 32; }
			if (arg == "-total-plans") { target = &opt.total_plans; maximum = 1000000; }
			if (arg == "-max-inputs") { target = &opt.max_inputs; maximum = 10; }
			if (arg == "-max-cone") { target = &opt.max_cone; maximum = 128; }
			if (arg == "-max-work") { target = &opt.max_work; maximum = 1000000000; }
			if (arg == "-max-memory") { target = &opt.max_memory; maximum = 1024; }
			if (arg == "-sat-effort") { target = &opt.sat_effort; maximum = 1000000000; }
			if (arg == "-sat-query") { target = &opt.sat_query; maximum = 1000000000; }
			if (!target) break;
			if (++argidx == args.size() || args[argidx].empty()) log_cmd_error("Expected integer after %s.\n", arg.c_str());
			int value = 0;
			for (char ch : args[argidx]) {
				if (ch < '0' || ch > '9' || value > (maximum - (ch - '0')) / 10)
					log_cmd_error("%s requires an integer in 1..%d.\n", arg.c_str(), maximum);
				value = value * 10 + ch - '0';
			}
			if (value < 1 || value > maximum) log_cmd_error("%s requires an integer in 1..%d.\n", arg.c_str(), maximum);
			*target = value;
		}
		extra_args(args, argidx, design);
		Lut4Mapping::reset_post_report(design, "resub");
		for (auto module : design->selected_modules()) {
			if (module->has_processes()) log_cmd_error("opt_lutresub requires lowered processes in %s.\n", log_id(module));
			auto module_options = opt;
			int64_t setup_work = 0;
			if (Lut4Mapping::shared_post(design)) {
				module_options.max_work = std::min<int64_t>(opt.max_work, std::stoll(design->scratchpad_get_string(Lut4Mapping::post_key("resub", "remaining"))));
				module_options.sat_effort = std::min<int64_t>(opt.sat_effort, std::stoll(design->scratchpad_get_string(Lut4Mapping::post_key("resub", "sat_remaining"))));
				int64_t minimum = 64 + 80 * int64_t(module->cells_size()) + 8 * int64_t(module->wires_size());
				if (module_options.max_work < minimum + 16) {
					log("opt_lutresub: shared work remaining=%d below minimum index/candidate work=%lld before workspace construction in %s.\n", module_options.max_work, (long long)(minimum + 16), log_id(module));
					continue;
				}
				int64_t inspection = 0, index_work = 0;
				setup_work = Lut4Mapping::post_setup_work(module, module_options.max_work, inspection, &index_work);
				Lut4Mapping::report_post(design, "resub", inspection, 0, 0);
				module_options.max_work -= inspection;
				if (setup_work < 0) {
					log("opt_lutresub: shared work exhausted during index size inspection before workspace construction in %s.\n", log_id(module));
					continue;
				}
				if (module_options.max_work < setup_work + index_work + 16) {
					log("opt_lutresub: shared work below complete index/candidate work=%lld before workspace construction in %s.\n", (long long)(setup_work + index_work + 16), log_id(module));
					continue;
				}
			}
			int64_t index_bytes = Lut4Mapping::post_index_bytes(module, false);
			if (Lut4Mapping::shared_post(design)) {
				int64_t memory = std::stoll(design->scratchpad_get_string("opt_lut4_post.memory_remaining"));
				if (!design->scratchpad_get_bool("opt_lut4_post.baseline")) memory = std::max<int64_t>(0, memory - index_bytes);
				module_options.memory_bytes = std::min<int64_t>(int64_t(opt.max_memory) * 1048576, memory);
				if (!module_options.max_work || !module_options.memory_bytes) {
					log("opt_lutresub: shared budget exhausted before workspace construction in %s.\n", log_id(module));
					continue;
				}
				Lut4Mapping::report_post(design, "resub", setup_work, 0, index_bytes);
				log("opt_lutresub: workspace construction work=%lld, search allowance=%lld, index reservation=%lld bytes in %s.\n", (long long)setup_work, (long long)(module_options.max_work - setup_work), (long long)index_bytes, log_id(module));
				module_options.max_work -= setup_work;
			}
			LutResubWorker worker(design, module, module_options);
			Lut4Mapping::report_post(design, "resub", worker.budget.work, module_options.sat_effort - worker.budget.sat.remaining, worker.budget.peak + index_bytes);
		}
	}
} OptLutResubPass;

PRIVATE_NAMESPACE_END
