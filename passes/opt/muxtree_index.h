#ifndef MUXTREE_INDEX_H
#define MUXTREE_INDEX_H

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

YOSYS_NAMESPACE_BEGIN

// 一个 $mux/$pmux 的数据端口：$mux 的 0 是 A、1 是 B；$pmux 的 0 是 A、i+1 是 B 的第 i 段
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

// 数据端口在 cell 上的信号，sigmap 之后
static inline SigSpec mux_port_sig(const SigMap &sigmap, Cell *cell, int index)
{
	if (index == 0)
		return sigmap(cell->getPort(ID::A));
	if (cell->type == ID($mux))
		return sigmap(cell->getPort(ID::B));
	return sigmap(cell->getPort(ID::B).extract((index - 1) * mux_width(cell), mux_width(cell)));
}

// 数据端口被选中的条件位：$mux 的 B 是 S，$pmux 的 B_i 是 S[i]；A 端口没有单独的条件位
static inline SigBit mux_port_ctrl(const SigMap &sigmap, Cell *cell, int index)
{
	log_assert(index > 0);
	if (cell->type == ID($mux))
		return sigmap(cell->getPort(ID::S)[0]);
	return sigmap(cell->getPort(ID::S)[index - 1]);
}

// muxtree 的父子关系：子节点的每个输出位只被父节点的某一个数据端口使用一次，并且不是模块输出
struct MuxTreeIndex
{
	Module *module;
	SigMap sigmap;
	CellTypes comb_ct;
	dict<SigBit, Cell *> driver;
	dict<SigBit, int> use_count;
	dict<SigBit, pool<Cell *>> users;
	pool<SigBit> port_bits;
	dict<Cell *, MuxPort> parent;
	dict<MuxPort, vector<Cell *>> children;
	vector<Cell *> roots;

	MuxTreeIndex(Module *module) : module(module), sigmap(module)
	{
		comb_ct.setup_internals_eval();
		comb_ct.setup_stdcells_eval();

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					if (bit.wire)
						port_bits.insert(bit);

		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				bool is_output = cell->output(conn.first);
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire)
						continue;
					if (is_output)
						driver[bit] = cell;
					else {
						use_count[bit]++;
						users[bit].insert(cell);
					}
				}
			}

		for (auto cell : module->selected_cells()) {
			if (!is_mux_node(cell))
				continue;
			MuxPort found = {nullptr, -1};
			bool ok = true;
			for (auto bit : sigmap(cell->getPort(ID::Y))) {
				MuxPort p = find_parent_port(bit);
				if (p.cell == nullptr || p.cell == cell || (found.cell != nullptr && !(found == p))) {
					ok = false;
					break;
				}
				found = p;
			}
			if (ok && found.cell != nullptr) {
				parent[cell] = found;
				children[found].push_back(cell);
			}
		}

		for (auto cell : module->selected_cells())
			if (is_mux_node(cell) && !parent.count(cell))
				roots.push_back(cell);
	}

	// bit 只有一个使用者并且是某个 mux 数据端口里的唯一一次出现时，返回该端口
	MuxPort find_parent_port(SigBit bit)
	{
		if (!bit.wire || port_bits.count(bit) || use_count[bit] != 1)
			return {nullptr, -1};
		Cell *user = *users[bit].begin();
		if (!is_mux_node(user) || !module->selected(user))
			return {nullptr, -1};
		for (auto bit_s : sigmap(user->getPort(ID::S)))
			if (bit_s == bit)
				return {nullptr, -1};
		int n = mux_port_count(user);
		MuxPort found = {nullptr, -1};
		for (int i = 0; i < n; i++)
			for (auto b : mux_port_sig(sigmap, user, i))
				if (b == bit) {
					if (found.cell != nullptr)
						return {nullptr, -1};
					found = {user, i};
				}
		return found;
	}
};

YOSYS_NAMESPACE_END

#endif
