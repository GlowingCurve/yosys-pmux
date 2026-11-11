#ifndef PMUX_LUT_COST_H
#define PMUX_LUT_COST_H

#include "kernel/yosys.h"
#include <functional>
#include <memory>

YOSYS_NAMESPACE_BEGIN
class PmuxNetlist;

namespace PmuxLutCost {

struct Cut {
private:
	std::array<uint16_t, 4> inputs = {};
	uint8_t length = 0;

public:
	Cut() = default;
	template<typename Iterator> Cut(Iterator first, Iterator last)
	{
		auto count = std::distance(first, last);
		log_assert(count >= 0 && count <= 4);
		for (auto it = first; it != last; ++it) log_assert(*it >= 0 && *it < 4096);
		length = uint8_t(count);
		std::copy(first, last, inputs.begin());
	}
	Cut(std::initializer_list<int> values) : Cut(values.begin(), values.end()) {}

	int size() const { return length; }
	bool empty() const { return length == 0; }
	void clear() { length = 0; }
	const uint16_t *begin() const { return inputs.data(); }
	const uint16_t *end() const { return inputs.data()+length; }
	int operator[](int index) const { return inputs[index]; }
	bool operator==(const Cut &other) const
	{
		return length == other.length && std::equal(begin(), end(), other.begin());
	}
	bool operator<(const Cut &other) const
	{
		return std::lexicographical_compare(begin(), end(), other.begin(), other.end());
	}
	[[nodiscard]] Hasher hash_into(Hasher h) const
	{
		h.eat((uint32_t)length);
		for (int input : *this) h.eat(input);
		return h;
	}
};

struct LutCostGraph {
	struct Primary {
		Cut inputs;
		uint16_t table;
		bool leaf = false;
		Primary(uint16_t table, const std::vector<int> &inputs, bool leaf = false) :
			inputs(inputs.begin(), inputs.end()), table(table), leaf(leaf) {}
	};
	struct MapState {
		std::vector<Cut> cuts;
		int cost = -1;
		unsigned generation = 0;
		const Cut &best_cut() const
		{
			static constexpr Cut empty;
			return cost > 0 ? cuts.front() : empty;
		}
	};
	struct Node : Primary, MapState {
		Node(uint16_t table, const std::vector<int> &inputs, bool leaf = false) : Primary(table, inputs, leaf) {}
	};
	struct ReadOnlyGraph {
		std::vector<Primary> nodes;
		dict<SigBit, int> leaves;
		dict<std::pair<uint16_t, std::vector<int>>, int> functions;
	};
	struct CertificateTruth {
		std::vector<int> inputs;
		std::array<uint64_t, 2> values;
		int traversal_work, evaluation_work;
		bool partial;
	};
	using CertificateCache = dict<std::pair<int, int>, CertificateTruth>;

private:
	const ReadOnlyGraph *original = nullptr;
	const pool<SigBit> *original_fixed = nullptr;
	CertificateCache *original_certificates = nullptr;
	std::vector<MapState> original_mapping;
	unsigned mapping_generation = 0;

public:
	std::vector<Node> nodes = {{0, {}}, {1, {}}};
	dict<SigBit, int> leaves;
	dict<std::pair<uint16_t, std::vector<int>>, int> functions;
	dict<int, pool<Cut>> certificates;
	pool<std::pair<int, int>> checked_certificates;
	pool<SigBit> fixed_bits;
	pool<int> required;
	int certificate_widths[8] = {}, partial_functions = 0;
	int &work;
	bool valid = true;

	LutCostGraph(int &work) : work(work) {}

	void use_snapshot(const ReadOnlyGraph &snapshot, const pool<SigBit> &fixed, CertificateCache *cache = nullptr)
	{
		log_assert(valid && !original && GetSize(nodes) == 2 && leaves.empty() && functions.empty() && fixed_bits.empty());
		log_assert(certificates.empty() && checked_certificates.empty() && required.empty() && original_mapping.empty());
		log_assert(GetSize(snapshot.nodes) >= 2 && GetSize(snapshot.nodes) <= 4096);
		original = &snapshot;
		original_fixed = &fixed;
		original_certificates = cache;
		nodes.clear();
		original_mapping.resize(GetSize(snapshot.nodes));
	}

	int node_count() const
	{
		return GetSize(nodes) + (original ? GetSize(original->nodes) : 0);
	}

	const Primary &primary(int id) const
	{
		int prefix = original ? GetSize(original->nodes) : 0;
		return id < prefix ? original->nodes[id] : nodes[id-prefix];
	}

	MapState &mapping(int id)
	{
		int prefix = original ? GetSize(original->nodes) : 0;
		auto &state = id < prefix ? original_mapping[id] : nodes[id-prefix];
		if ((state.generation & ~3u) != mapping_generation) {
			state.cost = -1;
			state.cuts.clear();
			state.generation = mapping_generation;
		}
		return state;
	}

	void add_fixed(SigBit bit)
	{
		if (!original_fixed || !original_fixed->count(bit)) fixed_bits.insert(bit);
	}

	int fixed_count() const
	{
		return GetSize(fixed_bits) + (original_fixed ? GetSize(*original_fixed) : 0);
	}

	bool spend(int amount = 1)
	{
		if (!valid) return false;
		if (work < amount) { work = -1; valid = false; }
		else work -= amount;
		return valid;
	}

	int append(Node node)
	{
		if (!spend() || node_count() >= 4096) {
			valid = false;
			return 0;
		}
		int id = node_count();
		nodes.push_back(std::move(node));
		return id;
	}

	int leaf(SigBit bit)
	{
		if (bit == State::S0 || bit == State::S1) return bit == State::S1 ? 1 : 0;
		if (original) {
			auto found = original->leaves.find(bit);
			if (found != original->leaves.end()) return found->second;
		}
		auto found = leaves.find(bit);
		if (found != leaves.end()) return found->second;
		int id = append({0, {}, true});
		leaves[bit] = id;
		return id;
	}

	int gate(uint16_t table, const std::vector<int> &args)
	{
		log_assert(GetSize(args) <= 4);
		std::vector<int> inputs;
		for (int id : args) if (id > 1) inputs.push_back(id);
		std::sort(inputs.begin(), inputs.end());
		inputs.erase(std::unique(inputs.begin(), inputs.end()), inputs.end());
		uint16_t normalized = 0;
		for (int assignment = 0; assignment < (1 << GetSize(inputs)); assignment++) {
			if (!spend()) return 0;
			int original = 0;
			for (int i = 0; i < GetSize(args); i++) {
				int value = args[i] <= 1 ? args[i] : (assignment >> (std::lower_bound(inputs.begin(), inputs.end(), args[i])-inputs.begin())) & 1;
				original |= value << i;
			}
			normalized |= ((table >> original) & 1) << assignment;
		}
		for (int i = GetSize(inputs)-1; i >= 0; i--) {
			bool relevant = false;
			for (int assignment = 0; assignment < (1 << GetSize(inputs)); assignment++) {
				if (!spend()) return 0;
				if (!(assignment & (1 << i)) && ((normalized >> assignment) & 1) != ((normalized >> (assignment | (1 << i))) & 1)) relevant = true;
			}
			if (relevant) continue;
			uint16_t reduced = 0;
			for (int assignment = 0; assignment < (1 << (GetSize(inputs)-1)); assignment++) {
				if (!spend()) return 0;
				int original = (assignment & ((1 << i)-1)) | ((assignment >> i) << (i+1));
				reduced |= ((normalized >> original) & 1) << assignment;
			}
			normalized = reduced;
			inputs.erase(inputs.begin()+i);
		}
		if (inputs.empty()) return normalized & 1;
		if (GetSize(inputs) == 1 && normalized == 2) return inputs[0];
		auto key = std::make_pair(normalized, inputs);
		if (original) {
			auto found = original->functions.find(key);
			if (found != original->functions.end()) return found->second;
		}
		auto found = functions.find(key);
		if (found != functions.end()) return found->second;
		int id = append({normalized, inputs});
		functions[key] = id;
		return id;
	}

	int reduce(uint16_t table, std::vector<int> inputs, int identity)
	{
		if (inputs.empty()) return identity;
		while (GetSize(inputs) > 1) {
			std::vector<int> next;
			for (int i = 0; i < GetSize(inputs); i += 2)
				next.push_back(i+1 < GetSize(inputs) ? gate(table, {inputs[i], inputs[i+1]}) : inputs[i]);
			inputs.swap(next);
		}
		return inputs[0];
	}

	void prepare_certificate(int root, int care)
	{
		if (!checked_certificates.insert({root, care}).second || root <= 1 || primary(root).leaf) return;
		CertificateTruth calculated;
		const CertificateTruth *truth = nullptr;
		bool share = original_certificates && root < GetSize(original->nodes) && care < GetSize(original->nodes);
		if (share) {
			auto found = original_certificates->find({root, care});
			if (found != original_certificates->end()) {
				truth = &found->second;
				if (!spend(truth->traversal_work) || !spend(truth->evaluation_work)) return;
			}
		}
		if (!truth) {
			int initial_work = work;
			std::array<uint64_t, 64> visited = {};
			std::vector<int> pending = {root, care}, inputs, order;
			order.reserve(64);
			inputs.reserve(7);
			for (int i = 0; i < GetSize(pending); i++) {
				int id = pending[i];
				if (!spend()) return;
				if (id <= 1 || (visited[id/64] & (uint64_t(1) << (id%64)))) continue;
				visited[id/64] |= uint64_t(1) << (id%64);
				order.push_back(id);
				if (GetSize(order) > 64) return;
				if (primary(id).leaf) {
					inputs.push_back(id);
					if (GetSize(inputs) > 7) return;
				} else for (int input : primary(id).inputs) pending.push_back(input);
			}
			int width = GetSize(inputs);
			if (width <= 4) return;
			std::sort(inputs.begin(), inputs.end());
			std::sort(order.begin(), order.end());
			calculated.traversal_work = initial_work-work;
			std::array<std::array<uint64_t, 2>, 66> values = {};
			values[1] = {~uint64_t(0), ~uint64_t(0)};
			auto local = [&](int id) {
				return id <= 1 ? id : 2+int(std::lower_bound(order.begin(), order.end(), id)-order.begin());
			};
			static constexpr uint64_t patterns[] = {
				0xaaaaaaaaaaaaaaaaULL, 0xccccccccccccccccULL, 0xf0f0f0f0f0f0f0f0ULL,
				0xff00ff00ff00ff00ULL, 0xffff0000ffff0000ULL, 0xffffffff00000000ULL,
			};
			for (int i = 0; i < GetSize(order); i++) {
				const auto &node = primary(order[i]);
				if (node.leaf) {
					int input = std::lower_bound(inputs.begin(), inputs.end(), order[i])-inputs.begin();
					values[i+2] = input == 6 ? std::array<uint64_t, 2>{0, ~uint64_t(0)} :
						std::array<uint64_t, 2>{patterns[input], patterns[input]};
					continue;
				}
				std::array<int, 4> args = {};
				for (int j = 0; j < node.inputs.size(); j++) args[j] = local(node.inputs[j]);
				for (int lane = 0; lane < (width == 7 ? 2 : 1); lane++) {
					std::array<uint64_t, 16> rows;
					int count = 1 << node.inputs.size();
					for (int row = 0; row < count; row++) rows[row] = uint64_t(0)-((node.table >> row) & 1);
					for (int j = 0; j < node.inputs.size(); j++) {
						uint64_t select = values[args[j]][lane];
						count /= 2;
						for (int row = 0; row < count; row++) rows[row] = (select & rows[2*row+1]) | (~select & rows[2*row]);
					}
					values[i+2][lane] = rows[0];
				}
			}
			int assignments = 1 << width;
			uint64_t mask = width == 5 ? 0xffffffffULL : ~uint64_t(0);
			const auto &defined = values[local(care)];
			if ((defined[0] & mask) != mask) assignments = __builtin_ctzll(~defined[0] & mask)+1;
			else if (width == 7 && defined[1] != ~uint64_t(0)) assignments = 65+__builtin_ctzll(~defined[1]);
			calculated.evaluation_work = GetSize(order)*assignments;
			if (!spend(calculated.evaluation_work)) return;
			calculated.inputs = std::move(inputs);
			calculated.values = values[local(root)];
			calculated.partial = assignments < (1 << width) ||
				(width == 7 ? defined[1] != ~uint64_t(0) : (defined[0] & mask) != mask);
			truth = share ? &((*original_certificates)[{root, care}] = std::move(calculated)) : &calculated;
		}
		if (truth->partial) { partial_functions++; return; }
		const auto &inputs = truth->inputs;
		int width = GetSize(inputs);
		int partitions = 0;
		for (int mask = 0; mask < (1 << width); mask++) {
			int bound_width = __builtin_popcount(unsigned(mask));
			if (bound_width < 2 || bound_width > 4 || width-bound_width > 3) continue;
			log_assert(++partitions <= 35);
			std::vector<int> bound, free;
			for (int i = 0; i < width; i++) (mask & (1 << i) ? bound : free).push_back(i);
			std::vector<int> patterns;
			uint16_t inner = 0;
			for (int b = 0; b < (1 << bound_width); b++) {
				int column = 0;
				for (int a = 0; a < (1 << GetSize(free)); a++) {
					if (!spend()) return;
					int assignment = 0;
					for (int i = 0; i < bound_width; i++) assignment |= ((b >> i) & 1) << bound[i];
					for (int i = 0; i < GetSize(free); i++) assignment |= ((a >> i) & 1) << free[i];
					column |= ((truth->values[assignment/64] >> (assignment%64)) & 1) << a;
				}
				auto found = std::find(patterns.begin(), patterns.end(), column);
				if (found == patterns.end()) {
					patterns.push_back(column);
					if (GetSize(patterns) > 2) break;
					found = patterns.end()-1;
				}
				inner |= int(found-patterns.begin()) << b;
			}
			if (GetSize(patterns) > 2) continue;
			std::vector<int> inner_inputs, cut;
			for (int i : bound) inner_inputs.push_back(inputs[i]);
			for (int i : free) cut.push_back(inputs[i]);
			int intermediate = gate(inner, inner_inputs);
			if (!valid) return;
			if (intermediate == root) continue;
			if (intermediate > 1) cut.push_back(intermediate);
			std::sort(cut.begin(), cut.end());
			cut.erase(std::unique(cut.begin(), cut.end()), cut.end());
			certificates[root].emplace(cut.begin(), cut.end());
		}
		if (certificates.count(root) && !certificates.at(root).empty()) certificate_widths[width]++;
	}

	int cut_cost(const Cut &cut)
	{
		int cost = 0;
		for (int id : cut) {
			auto &state = mapping(id);
			if (state.cost < 0) map_node(id);
			if (!(state.generation & 1)) cost += state.cost;
		}
		return cost;
	}

	void rank_cuts(std::vector<Cut> &cuts, int limit)
	{
		if (GetSize(cuts) <= 1 && GetSize(cuts) <= limit) return;
		struct RankedCut {
			int index, cost;
		};
		std::vector<RankedCut> ranked;
		ranked.reserve(GetSize(cuts));
		for (int i = 0; i < GetSize(cuts); i++) ranked.push_back({i, cut_cost(cuts[i])});
		auto compare = [&](const RankedCut &a, const RankedCut &b) {
			const auto &a_inputs = cuts[a.index], &b_inputs = cuts[b.index];
			if (a.cost != b.cost) return a.cost < b.cost;
			if (a_inputs.size() != b_inputs.size()) return a_inputs.size() < b_inputs.size();
			return a_inputs < b_inputs;
		};
		std::vector<Cut> result;
		int count = std::min(GetSize(ranked), limit);
		if (count < GetSize(ranked)) std::nth_element(ranked.begin(), ranked.begin()+count, ranked.end(), compare);
		std::sort(ranked.begin(), ranked.begin()+count, compare);
		result.reserve(count+1);
		for (int i = 0; i < count; i++) result.push_back(std::move(cuts[ranked[i].index]));
		cuts = std::move(result);
	}

	void map_node(int id)
	{
		if (!valid) return;
		auto &state = mapping(id);
		if (state.cost >= 0) return;
		const auto &node = primary(id);
		if (id <= 1 || node.leaf) {
			state.cost = 0;
			state.cuts.push_back(id <= 1 ? Cut{} : Cut{id});
			return;
		}
		std::vector<Cut> cuts = {{}};
		for (int input : node.inputs) {
			auto &input_state = mapping(input);
			if (input_state.cost < 0) map_node(input);
			if (!valid) return;
			const auto &choices = input_state.cuts;
			pool<Cut> merged;
			for (auto &a : cuts) for (auto &b : choices) {
				if (!spend()) return;
				std::array<int, 8> cut;
				auto end = std::set_union(a.begin(), a.end(), b.begin(), b.end(), cut.begin());
				if (end-cut.begin() <= 4) merged.emplace(cut.begin(), end);
			}
			cuts.assign(merged.begin(), merged.end());
			rank_cuts(cuts, 32);
		}
		if (certificates.count(id)) for (auto &cut : certificates.at(id)) cuts.push_back(cut);
		log_assert(!cuts.empty());
		for (auto &cut : cuts) log_assert(GetSize(cut) <= 4 && std::find(cut.begin(), cut.end(), id) == cut.end());
		rank_cuts(cuts, 31);
		state.cost = 1 + cut_cost(cuts[0]);
		cuts.push_back({id});
		state.cuts = std::move(cuts);
	}

	pool<int> cover(const std::vector<int> &roots)
	{
		required.clear();
		for (int root : roots) required.insert(root);
		if (!spend(node_count())) return {};
		mapping_generation += 4;
		if (!mapping_generation) {
			for (auto &state : original_mapping) state.generation = 0;
			for (auto &node : nodes) node.generation = 0;
			mapping_generation = 4;
		}
		for (int root : roots) mapping(root).generation |= 1;
		pool<int> covered;
		auto pending = roots;
		for (int i = 0; i < GetSize(pending); i++) {
			int id = pending[i];
			if (!spend()) return {};
			map_node(id);
			if (!valid) return {};
			auto &state = mapping(id);
			if (id <= 1 || primary(id).leaf || (state.generation & 2)) continue;
			state.generation |= 2;
			covered.insert(id);
			for (int input : state.best_cut()) pending.push_back(input);
		}
		return covered;
	}
};

enum class CostStatus { Profitable, NoGain, UnsupportedSource, UnsupportedActivatedBoundary, DepthLimit, NodeLimit, BudgetExhausted };

const char *status_name(CostStatus status);

struct CostResult {
	CostStatus status = CostStatus::NoGain;
	int before = 0, after = 0;
	int removed = 0, added = 0, retained = 0;
};

struct Signal {
	int value, care;
};

class Builder {
	struct State;
	State &state;
	explicit Builder(State &state) : state(state) {}
	friend class ModuleCost;

public:
	Signal bit(SigBit bit, int depth = 64);
	Signal operation(uint16_t table, const std::vector<Signal> &args);
	Signal pmux(Signal fallback, const std::vector<Signal> &data, const std::vector<Signal> &controls);
	Signal fail(CostStatus reason);
	bool spend(int amount = 1);
};

using Replacement = std::function<Signal(Builder &, int)>;

struct Request {
	// 替换输出和保留根参与两次覆盖。断连的旧输出只允许出现在改写前的逻辑锥中。
	dict<SigBit, Replacement> replacements;
	pool<SigBit> removed, roots;
};

class Snapshot {
	struct State;
	std::unique_ptr<State> state;
	friend class ModuleCost;
	friend class Builder;

public:
	Snapshot();
	~Snapshot();
};

class ModuleCost {
	struct Model;
	std::unique_ptr<Model> model;
	friend class Builder;

public:
	explicit ModuleCost(PmuxNetlist &netlist);
	~ModuleCost();
	// 已另行规划的输出作为边界，其方案仍需读取的信号作为保留根。
	void preserve(const SigSpec &boundary_outputs, const pool<SigBit> &roots);
	bool modeled_inputs(SigBit bit, SigSpec &inputs, int &work);
	bool observed_outside(SigBit bit, const pool<SigBit> &modeled, const pool<SigBit> &replaced, int &work);
	CostStatus checkpoint(const Request &request, int &work, Snapshot &snapshot);
	CostResult estimate(const Request &request, int &work, const Snapshot *snapshot = nullptr);
};

}
YOSYS_NAMESPACE_END

#endif
