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
#include "passes/pmgen/ice40_dsp_pm.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Ice40DspPass : public Pass {
	Ice40DspPass() : Pass("ice40_dsp", "iCE40: map multipliers") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ice40_dsp [options] [selection]\n");
		log("\n");
		log("Map multipliers and iCE40 DSP resources.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ICE40_DSP pass (map multipliers).\n");

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

		for (auto module : design->selected_modules())
		{
			ice40_dsp_pm pm(module, module->cells());
			pm.match([&]()
			{
				log("\n");
				log("ffA:   %s\n", log_id(pm.st.ffA, "--"));
				log("ffB:   %s\n", log_id(pm.st.ffB, "--"));
				log("mul:   %s\n", log_id(pm.st.mul, "--"));
				log("ffY:   %s\n", log_id(pm.st.ffY, "--"));
				log("addAB: %s\n", log_id(pm.st.addAB, "--"));
				log("muxAB: %s\n", log_id(pm.st.muxAB, "--"));
				log("ffS:   %s\n", log_id(pm.st.ffS, "--"));

				pm.blacklist(pm.st.mul);
				pm.blacklist(pm.st.ffA);
				pm.blacklist(pm.st.ffB);
				pm.blacklist(pm.st.ffY);
				pm.blacklist(pm.st.ffS);
			});
		}
	}
} Ice40DspPass;

PRIVATE_NAMESPACE_END
