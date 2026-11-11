#ifndef PMUX_DECODER_H
#define PMUX_DECODER_H

#include "passes/opt/pmux_netlist.h"

YOSYS_NAMESPACE_BEGIN

class PmuxDecoder {
public:
	// The literals describe a conjunction. A dead conjunction is false before inversion.
	struct Cube {
		dict<SigBit, bool> bits;
		bool dead = false;
		bool inverted = false;
		Cell *cell = nullptr;
	};

	struct Table {
		Cell *cell = nullptr;
		SigSpec control;
		std::vector<SigSpec> data;
		// Each address indexes a selector bit, or -1 for the default row.
		std::vector<int> branch_for_code;
		std::vector<Cube> cubes;
		pool<Cell *> region;
		// Every decoded branch requires these additional literals.
		std::vector<std::pair<SigBit, bool>> prefix;
	};

	explicit PmuxDecoder(const PmuxNetlist &netlist);
	bool decode(SigBit bit, Cube &cube, bool allow_inequalities = false, bool allow_literal = false) const;
	bool table(Cell *cell, Table &result) const;
	bool table(Cell *cell, const std::vector<Cube> &cubes, Table &result) const;
	bool condition(SigBit bit, bool value, dict<SigBit, State> &facts, int &budget);

private:
	using Assumptions = std::vector<std::pair<SigBit, bool>>;
	struct Condition {
		dict<SigBit, State> facts;
		bool possible = false;
	};

	const PmuxNetlist &netlist;
	std::size_t cache_revision;
	dict<std::pair<SigBit, bool>, Condition> condition_cache;
	int cached_facts = 0;

	bool infer(SigBit bit, bool value, dict<SigBit, State> &facts, Assumptions &pending, int &budget) const;
};

YOSYS_NAMESPACE_END

#endif
