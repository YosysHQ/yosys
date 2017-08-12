/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2017 Robert Ou <rqou@robertou.com>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RecoverTFFPass : public ScriptPass
{
	RecoverTFFPass() : ScriptPass("recover_tff", "recovers toggle flip-flops from gates") {}
	virtual void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    recover_tff [options]\n");
		log("\n");
		log("recovers toggle flip-flops from gates\n");
		log("\n");
		log("Reconstructs toggle flip-flops given a netlist of gates. This pass is intended\n");
		log("to be used as part of a circuit reverse-engineering workflow, but it does also\n");
		log("work with synthesis. Note that this command will completely destroy the\n");
		log("structure of combinatorial logic as it works.\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this command:\n");
		help_script();
		log("\n");
	}

	bool no_final_abc;
	bool already_loaded_lib;

	virtual void clear_flags() YS_OVERRIDE
	{
		no_final_abc = false;
		already_loaded_lib = false;
	}

	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		clear_flags();

		if (design->has("\\__TFF_N_"))
			already_loaded_lib = true;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-no_final_abc") {
				no_final_abc = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		log_header(design, "Executing recover_tff.\n");
		log_push();

		run_script(design, "", "");

		log_pop();
	}

	virtual void script() YS_OVERRIDE
	{
		run("abc -g AND,XOR");
		run("clean");
		run("extract -map +/untechmap/tff_untechmap.v");

		// Load this library only if the design doesn't already have it
		if (!already_loaded_lib)
			run("read_verilog -lib +/untechmap/tff_untechmap.v");

		if (!no_final_abc)
		    run("abc");

		run("clean");
	}
} RecoverTFFPass;

PRIVATE_NAMESPACE_END
