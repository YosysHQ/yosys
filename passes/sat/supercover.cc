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

struct SupercoverPass : public Pass {
	SupercoverPass() : Pass("supercover", "add hi/lo cover cells for each wire bit") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    supercover [options] [selection]\n");
		log("\n");
		log("This command adds two cover cells for each bit of each selected wire, one\n");
		log("checking for a hi signal level and one checking for lo level.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		// bool flag_noinit = false;

		log_header(design, "Executing SUPERCOVER pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-noinit") {
			// 	flag_noinit = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			pool<SigBit> handled_bits;

			int cnt_wire = 0, cnt_bits = 0;
			log("Adding cover cells to module %s.\n", log_id(module));
			for (auto wire : module->selected_wires())
			{
				bool counted_wire = false;
				std::string src = wire->get_src_attribute();

				for (auto bit : sigmap(SigSpec(wire)))
				{
					if (bit.wire == nullptr)
						continue;

					if (handled_bits.count(bit))
						continue;

					SigSpec inv = module->Not(NEW_ID, bit);
					module->addCover(NEW_ID, bit, State::S1, src);
					module->addCover(NEW_ID, inv, State::S1, src);

					handled_bits.insert(bit);
					if (!counted_wire) {
						counted_wire = false;
						cnt_wire++;
					}
					cnt_bits++;
				}
			}
			log("  added cover cells to %d wires, %d bits.\n", cnt_wire, cnt_bits);
		}
	}
} SupercoverPass;

PRIVATE_NAMESPACE_END
