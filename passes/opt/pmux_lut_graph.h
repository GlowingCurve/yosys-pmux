#ifndef PMUX_LUT_GRAPH_H
#define PMUX_LUT_GRAPH_H

#include "kernel/yosys.h"
#include <limits>

YOSYS_NAMESPACE_BEGIN

class PmuxLutGraph {
public:
	// Subsets chooses the composition with the smallest reachable LUT count.
	enum class Expansion { None, All, Subsets };
	struct Node {
		SigBit bit;
		std::vector<int> inputs;
		uint16_t mask;
		bool leaf;
	};

	explicit PmuxLutGraph(Expansion expansion = Expansion::None, int node_limit = std::numeric_limits<int>::max());
	int leaf(SigBit bit);
	std::vector<int> bits(const SigSpec &value);
	int lut(const std::vector<int> &args, uint16_t mask);
	int gate(const std::vector<int> &args, uint16_t mask);
	template<typename F> int function(const std::vector<int> &args, F evaluate)
	{
		log_assert(GetSize(args) <= 4);
		uint16_t mask = 0;
		for (int assignment = 0; assignment < (1 << GetSize(args)); assignment++)
			if (evaluate(assignment)) mask |= 1u << assignment;
		return lut(args, mask);
	}
	int invert(int id);
	int mux(int low, int high, int select);
	int select(const std::vector<int> &values, const std::vector<int> &control);
	int reduce(std::vector<int> values, bool conjunction = false);
	std::vector<int> add(const std::vector<int> &a, const std::vector<int> &b, int carry = 0);
	std::vector<int> sum3(const std::vector<int> &a, const std::vector<int> &b, const std::vector<int> &c);

	int node_count() const { return GetSize(nodes); }
	bool overflowed() const { return overflow; }
	const Node &node(int id) const;
	pool<int> live(const std::vector<int> &roots) const;
	pool<SigBit> referenced(const std::vector<int> &roots) const;
	int cost(const std::vector<int> &roots) const;
	int cost(const std::vector<int> &roots, pool<SigBit> &referenced) const;
	int incremental_cost(const std::vector<int> &roots, const pool<int> &covered) const;
	SigSpec emit(Module *module, IdString celltype, const std::vector<int> &roots) const;
	static void map_intel_lut(Cell *cell, IdString celltype);

private:
	using Function = std::pair<std::vector<int>, uint16_t>;
	Expansion expansion;
	int node_limit;
	bool overflow = false;
	std::vector<Node> nodes = {{State::S0, {}, 0, true}, {State::S1, {}, 0, true}};
	dict<SigBit, int> leaves;
	dict<Function, int> functions;

	int append(Node node);
	Function normalize(const std::vector<int> &args, uint16_t mask) const;
	int find(const Function &function) const;
	int intern(Function function);
	bool expand(const Function &function, unsigned selected, Function &result) const;
	int candidate_cost(const Function &function) const;
	int select(const std::vector<int> &values, const std::vector<int> &control, int level, size_t prefix);
};

YOSYS_NAMESPACE_END

#endif
