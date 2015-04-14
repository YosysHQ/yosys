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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool check_label(bool &active, std::string run_from, std::string run_to, std::string label)
{
	if (label == run_from)
		active = true;
	if (label == run_to)
		active = false;
	return active;
}

struct SynthIce40Pass : public Pass {
	SynthIce40Pass() : Pass("synth_ice40", "synthesis for iCE40 FPGAs") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_ice40 [options]\n");
		log("\n");
		log("This command runs synthesis for iCE40 FPGAs. This work is experimental.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		log("\n");
		log("    begin:\n");
		log("        read_verilog -lib +/ice40/cells_sim.v\n");
		log("        hierarchy -check -top <top>\n");
		log("\n");
		log("    coarse:\n");
		log("        synth -run coarse\n");
		log("\n");
		log("    fine:\n");
		log("        opt -fast -full\n");
		log("        memory_map\n");
		log("        opt -full\n");
		log("        techmap\n");
		log("        opt -fast\n");
		log("\n");
		log("    map_luts:\n");
		log("        abc -lut 4\n");
		log("        clean\n");
		log("\n");
		log("    map_cells:\n");
		log("        techmap -map +/ice40/cells_map.v\n");
		log("        clean\n");
		log("\n");
		log("    check:\n");
		log("        hierarchy -check\n");
		log("        stat\n");
		log("        check -noinit\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_opt = "-auto-top";
		std::string run_from, run_to;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos+1);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This comannd only operates on fully selected designs!\n");

		bool active = run_from.empty();

		log_header("Executing SYNTH_ICE40 pass.\n");
		log_push();

		if (check_label(active, run_from, run_to, "begin"))
		{
			Pass::call(design, "read_verilog -lib +/ice40/cells_sim.v");
			Pass::call(design, stringf("hierarchy -check %s", top_opt.c_str()));
		}

		if (check_label(active, run_from, run_to, "coarse"))
		{
			Pass::call(design, "synth -run coarse");
		}

		if (check_label(active, run_from, run_to, "fine"))
		{
			Pass::call(design, "opt -fast -full");
			Pass::call(design, "memory_map");
			Pass::call(design, "opt -full");
			Pass::call(design, "techmap");
			Pass::call(design, "opt -fast");
		}

		if (check_label(active, run_from, run_to, "map_luts"))
		{
			Pass::call(design, "abc -lut 4");
			Pass::call(design, "clean");
		}

		if (check_label(active, run_from, run_to, "map_cells"))
		{
			Pass::call(design, "techmap -map +/ice40/cells_map.v");
			Pass::call(design, "clean");
		}

		if (check_label(active, run_from, run_to, "check"))
		{
			Pass::call(design, "hierarchy -check");
			Pass::call(design, "stat");
			Pass::call(design, "check -noinit");
		}

		log_pop();
	}
} SynthIce40Pass;
 
PRIVATE_NAMESPACE_END
