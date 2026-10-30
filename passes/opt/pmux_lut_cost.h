#ifndef PMUX_LUT_COST_H
#define PMUX_LUT_COST_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN
namespace PmuxLutCost {

struct Cut {
private:
	std::array<int, 4> inputs = {};
	int length = 0;

public:
	Cut() = default;
	template<typename Iterator> Cut(Iterator first, Iterator last)
	{
		auto count = std::distance(first, last);
		log_assert(count >= 0 && count <= 4);
		length = int(count);
		std::copy(first, last, inputs.begin());
	}
	Cut(std::initializer_list<int> values) : Cut(values.begin(), values.end()) {}

	int size() const { return length; }
	bool empty() const { return length == 0; }
	void clear() { length = 0; }
	const int *begin() const { return inputs.data(); }
	const int *end() const { return inputs.data()+length; }
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
	struct Node {
		uint16_t table;
		std::vector<int> inputs;
		bool leaf = false;
		int cost = -1;
		std::vector<Cut> cuts;
		Cut best;
		Node(uint16_t table, std::vector<int> inputs, bool leaf = false) : table(table), inputs(std::move(inputs)), leaf(leaf) {}
	};
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

	bool spend()
	{
		if (--work < 0) valid = false;
		return valid;
	}

	int append(Node node)
	{
		if (!spend() || GetSize(nodes) >= 4096) {
			valid = false;
			return 0;
		}
		int id = GetSize(nodes);
		nodes.push_back(std::move(node));
		return id;
	}

	int leaf(SigBit bit)
	{
		if (bit == State::S0 || bit == State::S1) return bit == State::S1 ? 1 : 0;
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
		if (!checked_certificates.insert({root, care}).second || root <= 1 || nodes[root].leaf) return;
		pool<int> visited, support;
		std::vector<int> pending = {root, care};
		for (int i = 0; i < GetSize(pending); i++) {
			int id = pending[i];
			if (!spend()) return;
			if (id <= 1 || !visited.insert(id).second) continue;
			if (GetSize(visited) > 64) return;
			if (nodes[id].leaf) {
				support.insert(id);
				if (GetSize(support) > 7) return;
			} else for (int input : nodes[id].inputs) pending.push_back(input);
		}
		int width = GetSize(support);
		if (width <= 4) return;
		std::vector<int> inputs(support.begin(), support.end()), order(visited.begin(), visited.end());
		std::sort(inputs.begin(), inputs.end());
		std::sort(order.begin(), order.end());
		std::vector<int> truth;
		for (int assignment = 0; assignment < (1 << width); assignment++) {
			dict<int, int> values = {{0, 0}, {1, 1}};
			for (int i = 0; i < width; i++) values[inputs[i]] = (assignment >> i) & 1;
			for (int id : order) {
				if (!spend()) return;
				if (values.count(id)) continue;
				int address = 0;
				for (int i = 0; i < GetSize(nodes[id].inputs); i++) address |= values.at(nodes[id].inputs[i]) << i;
				values[id] = (nodes[id].table >> address) & 1;
			}
			if (!values.at(care)) {
				partial_functions++;
				return;
			}
			truth.push_back(values.at(root));
		}
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
					column |= truth[assignment] << a;
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
			map_node(id);
			if (!required.count(id)) cost += nodes[id].cost;
		}
		return cost;
	}

	void rank_cuts(std::vector<Cut> &cuts, int limit)
	{
		if (GetSize(cuts) <= 1 && GetSize(cuts) <= limit) return;
		struct RankedCut {
			int index;
			mutable int cost = 0;
			mutable bool evaluated = false;
		};
		std::vector<RankedCut> ranked;
		ranked.reserve(GetSize(cuts));
		for (int i = 0; i < GetSize(cuts); i++) ranked.push_back({i, 0, false});
		auto cost = [&](const RankedCut &cut) {
			if (!cut.evaluated) {
				cut.cost = cut_cost(cuts[cut.index]);
				cut.evaluated = true;
			}
			return cut.cost;
		};
		std::sort(ranked.begin(), ranked.end(), [&](const RankedCut &a, const RankedCut &b) {
			const auto &a_inputs = cuts[a.index], &b_inputs = cuts[b.index];
			using Rank = std::tuple<int, int, const Cut &>;
			return Rank(cost(a), GetSize(a_inputs), a_inputs) < Rank(cost(b), GetSize(b_inputs), b_inputs);
		});
		std::vector<Cut> result;
		int count = std::min(GetSize(ranked), limit);
		result.reserve(count+1);
		for (int i = 0; i < count; i++) result.push_back(std::move(cuts[ranked[i].index]));
		cuts = std::move(result);
	}

	void map_node(int id)
	{
		if (!valid || nodes[id].cost >= 0) return;
		if (id <= 1 || nodes[id].leaf) {
			nodes[id].cost = 0;
			nodes[id].cuts = id <= 1 ? std::vector<Cut>{{}} : std::vector<Cut>{{id}};
			return;
		}
		std::vector<Cut> cuts = {{}};
		for (int input : nodes[id].inputs) {
			map_node(input);
			if (!valid) return;
			const auto &choices = nodes[input].cuts;
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
		nodes[id].best = cuts[0];
		nodes[id].cost = 1 + cut_cost(cuts[0]);
		cuts.push_back({id});
		nodes[id].cuts = std::move(cuts);
	}

	pool<int> cover(const std::vector<int> &roots)
	{
		required.clear();
		for (int root : roots) required.insert(root);
		for (auto &node : nodes) {
			if (!spend()) return {};
			node.cost = -1;
			node.cuts.clear();
			node.best.clear();
		}
		pool<int> covered;
		auto pending = roots;
		for (int i = 0; i < GetSize(pending); i++) {
			int id = pending[i];
			if (!spend()) return {};
			map_node(id);
			if (!valid) return {};
			if (id <= 1 || nodes[id].leaf || !covered.insert(id).second) continue;
			for (int input : nodes[id].best) pending.push_back(input);
		}
		return covered;
	}
};

}
YOSYS_NAMESPACE_END

#endif
