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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include "kernel/ffinit.h"
#include "kernel/threading.h"
#include "kernel/yosys_common.h"
#include "passes/opt/opt_clean/shared.h"

YOSYS_NAMESPACE_BEGIN

void remove_temporary_cells(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose)
{
	ShardedVector<RTLIL::Cell*> delcells(subpool);
	ShardedVector<RTLIL::SigSig> new_connections(subpool);
	const RTLIL::Module *const_module = module;
	subpool.run([const_module, &delcells, &new_connections](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->cells_size())) {
			RTLIL::Cell *cell = const_module->cell_at(i);
			if (cell->type.in(ID($pos), ID($_BUF_), ID($buf)) && !cell->has_keep_attr()) {
				bool is_signed = cell->type == ID($pos) && cell->getParam(ID::A_SIGNED).as_bool();
				RTLIL::SigSpec a = cell->getPort(ID::A);
				RTLIL::SigSpec y = cell->getPort(ID::Y);
				a.extend_u0(GetSize(y), is_signed);

				if (a.has_const(State::Sz)) {
					RTLIL::SigSpec new_a;
					RTLIL::SigSpec new_y;
					for (int i = 0; i < GetSize(a); ++i) {
						RTLIL::SigBit b = a[i];
						if (b == State::Sz)
							continue;
						new_a.append(b);
						new_y.append(y[i]);
					}
					a = std::move(new_a);
					y = std::move(new_y);
				}
				if (!y.empty())
					new_connections.insert(ctx, {y, a});
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
	bool did_something = false;
	for (RTLIL::SigSig &connection : new_connections) {
		module->connect(connection);
	}
	for (RTLIL::Cell *cell : delcells) {
		if (verbose) {
			if (cell->type == ID($connect))
				log_debug("  removing connect cell `%s': %s <-> %s\n", cell->name,
						log_signal(cell->getPort(ID::A)), log_signal(cell->getPort(ID::B)));
			else if (cell->type == ID($input_port))
				log_debug("  removing input port marker cell `%s': %s\n", cell->name,
						log_signal(cell->getPort(ID::Y)));
			else
				log_debug("  removing buffer cell `%s': %s = %s\n", cell->name,
						log_signal(cell->getPort(ID::Y)), log_signal(cell->getPort(ID::A)));
		}
		module->remove(cell);
		did_something = true;
	}
	if (did_something)
		module->design->scratchpad_set_bool("opt.did_something", true);
}

YOSYS_NAMESPACE_END
