/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
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
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct DffunmapPass : public Pass {
	DffunmapPass() : Pass("dffunmap", "unmap clock enable and synchronous reset from FFs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dffunmap [options] [selection]\n");
		log("\n");
		log("This pass transforms FF types with clock enable and/or synchronous reset into\n");
		log("their base type (with neither clock enable nor sync reset) by emulating the clock\n");
		log("enable and synchronous reset with multiplexers on the cell input.\n");
		log("\n");
		log("    -ce-only\n");
		log("        unmap only clock enables, leave synchronous resets alone.\n");
		log("\n");
		log("    -srst-only\n");
		log("        unmap only synchronous resets, leave clock enables alone.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing DFFUNMAP pass (unmap clock enable and synchronous reset from FFs).\n");

		bool ce_only = false;
		bool srst_only = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-ce-only") {
				ce_only = true;
				continue;
			}
			if (args[argidx] == "-srst-only") {
				srst_only = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (ce_only && srst_only)
			log_cmd_error("Options -ce-only and -srst-only are mutually exclusive!\n");

		for (auto mod : design->selected_modules())
		{
			SigMap sigmap(mod);
			FfInitVals initvals(&sigmap, mod);

			for (auto cell : mod->selected_cells())
			{
				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(&initvals, cell);
				IdString name = cell->name;

				if (!ff.has_clk)
					continue;

				if (ce_only) {
					if (!ff.has_en)
						continue;
					ff.unmap_ce(mod);
				} else if (srst_only) {
					if (!ff.has_srst)
						continue;
					ff.unmap_srst(mod);
				} else {
					if (!ff.has_en && !ff.has_srst)
						continue;
					ff.unmap_ce_srst(mod);
				}

				mod->remove(cell);
				ff.emit(mod, name);
			}
		}
	}
} DffunmapPass;

PRIVATE_NAMESPACE_END
