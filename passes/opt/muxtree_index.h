#ifndef MUXTREE_INDEX_H
#define MUXTREE_INDEX_H

#include "passes/opt/muxledger.h"

YOSYS_NAMESPACE_BEGIN

struct MuxPort {
	Cell *cell;
	int index;
	bool operator==(const MuxPort &other) const { return cell == other.cell && index == other.index; }
	Hasher hash_into(Hasher h) const { h.eat(cell); h.eat(index); return h; }
};

static inline bool is_mux_node(const Cell *cell)
{
	return cell->type.in(ID($mux), ID($pmux));
}

static inline int mux_port_count(const Cell *cell)
{
	return cell->type == ID($mux) ? 2 : cell->getParam(ID::S_WIDTH).as_int() + 1;
}

static inline int mux_width(const Cell *cell)
{
	return cell->getParam(ID::WIDTH).as_int();
}

static inline SigSpec mux_port_sig(const SigMap &sigmap, Cell *cell, int index)
{
	if (index == 0)
		return sigmap(cell->getPort(ID::A));
	if (cell->type == ID($mux))
		return sigmap(cell->getPort(ID::B));
	return sigmap(cell->getPort(ID::B).extract((index - 1) * mux_width(cell), mux_width(cell)));
}

static inline SigBit mux_port_ctrl(const SigMap &sigmap, Cell *cell, int index)
{
	log_assert(index > 0);
	return sigmap(cell->getPort(ID::S)[cell->type == ID($mux) ? 0 : index - 1]);
}

// 父子关系复用模块成本索引中的唯一驱动、端口位置与保护信息。
struct MuxTreeIndex
{
	Module *module;
	MuxCostContext costs;
	SigMap &sigmap;
	dict<SigBit, Cell *> driver;
	dict<Cell *, MuxPort> parent;
	dict<MuxPort, std::vector<Cell *>> children;
	std::vector<Cell *> roots;
	// 推断开始之前登记的证明支持单元并集。
	pool<IdString> registered;

	// 延迟索引：先完成真实必要条件扫描，资格成立之后才建立一次完整成本索引。
	explicit MuxTreeIndex(Module *module) : module(module), costs(module), sigmap(costs.sigmap) { }

	void rebuild()
	{
		driver.clear(); parent.clear(); children.clear(); roots.clear();
		for (const auto &entry : costs.drivers) {
			Cell *cell = costs.unique_driver(entry.first);
			if (cell != nullptr)
				driver[entry.first] = cell;
		}

		for (Cell *cell : module->selected_cells()) {
			if (!is_mux_node(cell) || !costs.mutable_cell(cell))
				continue;
			MuxPort found = {nullptr, -1};
			bool valid = true;
			for (SigBit bit : sigmap(cell->getPort(ID::Y))) {
				MuxPort candidate = find_parent_port(bit);
				if (candidate.cell == nullptr || candidate.cell == cell ||
					(found.cell != nullptr && !(found == candidate))) {
					valid = false;
					break;
				}
				found = candidate;
			}
			if (valid && found.cell != nullptr) {
				parent[cell] = found;
				children[found].push_back(cell);
			}
		}
		for (Cell *cell : module->selected_cells())
			if (is_mux_node(cell) && costs.mutable_cell(cell) && !parent.count(cell))
				roots.push_back(cell);
	}

	// 只有全部Y位具有唯一驱动、use_count=1、没有模块输出或保护观察、
	// 唯一使用者是父MUX的A/B端口时才登记父子路径。
	MuxPort find_parent_port(SigBit bit)
	{
		if (!bit.wire || costs.output_bits.count(bit) || costs.protected_bits.count(bit) ||
			costs.use_count.at(bit, 0) != 1 || costs.unique_driver(bit) == nullptr)
			return {nullptr, -1};
		const auto &ports = costs.users.at(bit);
		if (GetSize(ports) != 1)
			return {nullptr, -1};
		const auto &port = ports.front();
		Cell *user = module->cell(port.cell);
		if (user == nullptr || !is_mux_node(user) || !module->selected(user) ||
			!costs.mutable_cell(user) || !port.port.in(ID::A, ID::B))
			return {nullptr, -1};
		int index = port.port == ID::A ? 0 : user->type == ID($mux) ? 1 : 1 + port.offset / mux_width(user);
		return {user, index};
	}
};

YOSYS_NAMESPACE_END
#endif
