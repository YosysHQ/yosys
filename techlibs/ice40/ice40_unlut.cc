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
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static SigBit get_bit_or_zero(const SigSpec &sig)
{
	if (GetSize(sig) == 0)
		return State::S0;
	return sig[0];
}

static void run_ice40_unlut(Module *module)
{
	SigMap sigmap(module);

	for (auto cell : module->selected_cells())
	{
		if (cell->type == "\\SB_LUT4")
		{
			SigSpec inbits;

			inbits.append(get_bit_or_zero(cell->getPort("\\I0")));
			inbits.append(get_bit_or_zero(cell->getPort("\\I1")));
			inbits.append(get_bit_or_zero(cell->getPort("\\I2")));
			inbits.append(get_bit_or_zero(cell->getPort("\\I3")));
			sigmap.apply(inbits);

			log("Mapping SB_LUT4 cell %s.%s to $lut.\n", log_id(module), log_id(cell));

			cell->type ="$lut";
			cell->setParam("\\WIDTH", 4);
			cell->setParam("\\LUT", cell->getParam("\\LUT_INIT"));
			cell->unsetParam("\\LUT_INIT");

			cell->setPort("\\A", SigSpec({
				get_bit_or_zero(cell->getPort("\\I3")),
				get_bit_or_zero(cell->getPort("\\I2")),
				get_bit_or_zero(cell->getPort("\\I1")),
				get_bit_or_zero(cell->getPort("\\I0"))
			}));
			cell->setPort("\\Y", cell->getPort("\\O")[0]);
			cell->unsetPort("\\I0");
			cell->unsetPort("\\I1");
			cell->unsetPort("\\I2");
			cell->unsetPort("\\I3");
			cell->unsetPort("\\O");

			cell->check();
		}
	}
}

struct Ice40UnlutPass : public Pass {
	Ice40UnlutPass() : Pass("ice40_unlut", "iCE40: perform simple optimizations") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ice40_unlut [options] [selection]\n");
		log("\n");
		log("This command transforms all SB_LUT4 cells to generic $lut cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ICE40_UNLUT pass (convert SB_LUT4 to $lut).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-???") {
			//  continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			run_ice40_unlut(module);
	}
} Ice40UnlutPass;

PRIVATE_NAMESPACE_END
