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

#include "passes/opt/opt_clean/opt_clean.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

ShardedVector<std::pair<SigBit, State>> build_inits(AnalysisContext& actx) {
	ShardedVector<std::pair<SigBit, State>> results(actx.subpool);
	CellTypes fftypes;
	fftypes.setup_internals_mem();
	actx.subpool.run([&results, &fftypes, &actx](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(actx.mod->cells_size())) {
			RTLIL::Cell *cell = actx.mod->cell_at(i);
			if (fftypes.cell_known(cell->type) && cell->hasPort(ID::Q))
			{
				SigSpec sig = cell->getPort(ID::Q);

				for (int i = 0; i < GetSize(sig); i++)
				{
					SigBit bit = sig[i];

					if (bit.wire == nullptr || bit.wire->attributes.count(ID::init) == 0)
						continue;

					Const init = bit.wire->attributes.at(ID::init);

					if (i >= GetSize(init) || init[i] == State::Sx || init[i] == State::Sz)
						continue;

					results.insert(ctx, {bit, init[i]});
				}
			}
		}
	});
	return results;
}

dict<SigBit, State> qbits_from_inits(ShardedVector<std::pair<SigBit, State>>& inits, AnalysisContext& actx) {
	dict<SigBit, State> qbits;
	for (std::pair<SigBit, State> &p : inits) {
		actx.assign_map.add(p.first);
		qbits[p.first] = p.second;
	}
	return qbits;
}

ShardedVector<RTLIL::Wire*> deferred_init_transfer(const dict<SigBit, State>& qbits, AnalysisContext& actx) {
	ShardedVector<RTLIL::Wire*> wire_results(actx.subpool);
	actx.subpool.run([&actx, &qbits, &wire_results](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int j : ctx.item_range(actx.mod->wires_size())) {
			RTLIL::Wire *wire = actx.mod->wire_at(j);
			if (wire->attributes.count(ID::init) == 0)
				continue;
			Const init = wire->attributes.at(ID::init);

			for (int i = 0; i < GetSize(wire) && i < GetSize(init); i++)
			{
				if (init[i] == State::Sx || init[i] == State::Sz)
					continue;

				SigBit wire_bit = SigBit(wire, i);
				SigBit mapped_wire_bit = actx.assign_map(wire_bit);

				if (wire_bit == mapped_wire_bit)
					goto next_wire;

				if (mapped_wire_bit.wire) {
					if (qbits.count(mapped_wire_bit) == 0)
						goto next_wire;

					if (qbits.at(mapped_wire_bit) != init[i])
						goto next_wire;
				}
				else {
					if (mapped_wire_bit == State::Sx || mapped_wire_bit == State::Sz)
						goto next_wire;

					if (mapped_wire_bit != init[i]) {
						log_warning("Initial value conflict for %s resolving to %s but with init %s.\n", log_signal(wire_bit), log_signal(mapped_wire_bit), log_signal(init[i]));
						goto next_wire;
					}
				}
			}
			wire_results.insert(ctx, wire);

			next_wire:;
		}
	});
	return wire_results;
}

bool remove_redundant_inits(ShardedVector<RTLIL::Wire*> wires, bool verbose) {
	bool did_something = false;
	for (RTLIL::Wire *wire : wires) {
		if (verbose)
			log_debug("  removing redundant init attribute on %s.\n", log_id(wire));
		wire->attributes.erase(ID::init);
		did_something = true;
	}
	return did_something;
}

PRIVATE_NAMESPACE_END
YOSYS_NAMESPACE_BEGIN

bool rmunused_module_init(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose)
{
	AnalysisContext actx(module, subpool);

	ShardedVector<std::pair<SigBit, State>> inits = build_inits(actx);
	dict<SigBit, State> qbits = qbits_from_inits(inits, actx);
	ShardedVector<RTLIL::Wire*> inits_to_transfer = deferred_init_transfer(qbits, actx);

	bool did_something = remove_redundant_inits(inits_to_transfer, verbose);
	if (did_something)
		module->design->scratchpad_set_bool("opt.did_something", true);

	return did_something;
}

YOSYS_NAMESPACE_END
