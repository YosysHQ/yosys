/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Marcelina Kościelnicka <mwk@0x04.net>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct DemuxmapPass : public Pass {
	DemuxmapPass() : Pass("demuxmap", "transform $demux cells to $eq + $mux cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    demuxmap [selection]\n");
		log("\n");
		log("This pass transforms $demux cells to a bunch of equality comparisons.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing DEMUXMAP pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : module->selected_cells())
		{
			if (cell->type != TW($demux))
				continue;

			SigSpec sel = cell->getPort(TW::S);
			SigSpec data = cell->getPort(TW::A);
			SigSpec out = cell->getPort(TW::Y);
			int width = GetSize(cell->getPort(TW::A));

			for (int i = 0; i < 1 << GetSize(sel); i++) {
				if (width == 1 && data == State::S1) {
					RTLIL::Cell *eq_cell = module->addEq(NEW_TWINE, sel, Const(i, GetSize(sel)), out[i]);
					module->design->merge_src(eq_cell, cell);
				} else {
					Wire *eq = module->addWire(NEW_TWINE);
					RTLIL::Cell *eq_cell = module->addEq(NEW_TWINE, sel, Const(i, GetSize(sel)), eq);
					module->design->merge_src(eq_cell, cell);
					RTLIL::Cell *mux = module->addMux(NEW_TWINE,
							Const(State::S0, width),
							data,
							eq,
							out.extract(i*width, width));
					module->design->merge_src(mux, cell);
				}
			}

			module->remove(cell);
		}
	}
} DemuxmapPass;

PRIVATE_NAMESPACE_END
