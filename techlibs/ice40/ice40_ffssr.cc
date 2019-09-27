/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

struct Ice40FfssrPass : public Pass {
	Ice40FfssrPass() : Pass("ice40_ffssr", "iCE40: merge synchronous set/reset into FF cells") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    ice40_ffssr [options] [selection]\n");
		log("\n");
		log("Merge synchronous set/reset $_MUX_ cells into iCE40 FFs.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ICE40_FFSSR pass (merge synchronous set/reset into FF cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		pool<IdString> sb_dff_types;
		sb_dff_types.insert("\\SB_DFF");
		sb_dff_types.insert("\\SB_DFFE");
		sb_dff_types.insert("\\SB_DFFN");
		sb_dff_types.insert("\\SB_DFFNE");

		for (auto module : design->selected_modules())
		{
			log("Merging set/reset $_MUX_ cells into SB_FFs in %s.\n", log_id(module));

			SigMap sigmap(module);
			dict<SigBit, Cell*> sr_muxes;
			vector<Cell*> ff_cells;

			for (auto cell : module->selected_cells())
			{
				if (sb_dff_types.count(cell->type)) {
					ff_cells.push_back(cell);
					continue;
				}

				if (cell->type != "$_MUX_")
					continue;

				SigBit bit_a = sigmap(cell->getPort("\\A"));
				SigBit bit_b = sigmap(cell->getPort("\\B"));

				if (bit_a.wire == nullptr || bit_b.wire == nullptr)
					sr_muxes[sigmap(cell->getPort("\\Y"))] = cell;
			}

			for (auto cell : ff_cells)
			{
				if (cell->get_bool_attribute("\\dont_touch"))
					continue;

				SigSpec sig_d = cell->getPort("\\D");

				if (GetSize(sig_d) < 1)
					continue;

				SigBit bit_d = sigmap(sig_d[0]);

				if (sr_muxes.count(bit_d) == 0)
					continue;

				Cell *mux_cell = sr_muxes.at(bit_d);
				SigBit bit_a = sigmap(mux_cell->getPort("\\A"));
				SigBit bit_b = sigmap(mux_cell->getPort("\\B"));
				SigBit bit_s = sigmap(mux_cell->getPort("\\S"));

				log("  Merging %s (A=%s, B=%s, S=%s) into %s (%s).\n", log_id(mux_cell),
						log_signal(bit_a), log_signal(bit_b), log_signal(bit_s), log_id(cell), log_id(cell->type));

				SigBit sr_val, sr_sig;
				if (bit_a.wire == nullptr) {
					bit_d = bit_b;
					sr_val = bit_a;
					sr_sig = module->NotGate(NEW_ID, bit_s);
				} else {
					log_assert(bit_b.wire == nullptr);
					bit_d = bit_a;
					sr_val = bit_b;
					sr_sig = bit_s;
				}

				if (sr_val == State::S1) {
					cell->type = cell->type.str() + "SS";
					cell->setPort("\\S", sr_sig);
					cell->setPort("\\D", bit_d);
				} else {
					cell->type = cell->type.str() + "SR";
					cell->setPort("\\R", sr_sig);
					cell->setPort("\\D", bit_d);
				}
			}
		}
	}
} Ice40FfssrPass;

PRIVATE_NAMESPACE_END
