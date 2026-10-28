/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

// 为 clean 与 opt_clean 将临时缓冲单元转换为连接；直接检查高阻常量并复用原始端口信号。
#include "passes/opt/clean/opt_clean.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool is_signed(RTLIL::Cell* cell) {
	return cell->type == ID($pos) && cell->getParam(ID::A_SIGNED).as_bool();
}

bool trim_buf(RTLIL::Cell* cell, ShardedVector<RTLIL::SigSig>& new_connections, const ParallelDispatchThreadPool::RunCtx &ctx) {
	RTLIL::SigSpec a = cell->getPort(ID::A);
	RTLIL::SigSpec y = cell->getPort(ID::Y);
	a.extend_u0(GetSize(y), is_signed(cell));

	if (a.has_const(State::Sz))
		return false;
	if (!y.empty())
		new_connections.insert(ctx, {y, a});
	return true;
}

bool remove(ShardedVector<RTLIL::Cell*>& cells, RTLIL::Module* mod) {
	bool did_something = false;
	for (RTLIL::Cell *cell : cells) {
		mod->remove(cell);
		did_something = true;
	}
	return did_something;
}
PRIVATE_NAMESPACE_END
YOSYS_NAMESPACE_BEGIN

void remove_temporary_cells(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool)
{
	ShardedVector<RTLIL::Cell*> delcells(subpool);
	ShardedVector<RTLIL::SigSig> new_connections(subpool);
	const RTLIL::Module *const_module = module;
	subpool.run([const_module, &delcells, &new_connections](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->cells_size())) {
			RTLIL::Cell *cell = const_module->cell_at(i);
			if (cell->type.in(ID($pos), ID($_BUF_), ID($buf)) && !cell->has_keep_attr()) {
				if (trim_buf(cell, new_connections, ctx))
					delcells.insert(ctx, cell);
			} else if (cell->type.in(ID($connect)) && !cell->has_keep_attr()) {
				RTLIL::SigSpec a = cell->getPort(ID::A);
				RTLIL::SigSpec b = cell->getPort(ID::B);
				if (a.has_const() && !b.has_const())
					std::swap(a, b);
				new_connections.insert(ctx, {a, b});
				delcells.insert(ctx, cell);
			} else if (cell->type.in(ID($input_port)) && !cell->has_keep_attr()) {
				delcells.insert(ctx, cell);
			}
		}
	});
	for (RTLIL::SigSig &connection : new_connections) {
		module->connect(connection);
	}
	if (remove(delcells, module))
		module->design->scratchpad_set_bool("opt.did_something", true);
}

YOSYS_NAMESPACE_END
