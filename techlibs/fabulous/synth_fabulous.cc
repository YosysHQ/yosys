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
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthPass : public ScriptPass
{
	SynthPass() : ScriptPass("synth_fabulous", "FABulous synthesis script") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_fabulous [options]\n");
		log("\n");
		log("This command runs synthesis for FPGA fabrics generated with FABulous. This command does not operate\n");
		log("on partly selected designs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -auto-top\n");
		log("        automatically determine the top of the design hierarchy\n");
		log("\n");
		log("    -lut <k>\n");
		log("        perform synthesis for a k-LUT architecture (default 4).\n");
		log("\n");
		log("    -plib <primitive_library.v>\n");
		log("        use the specified Verilog file as a primitive library.\n");
		log("\n");
		log("    -run <from_label>[:<to_label>]\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_module, plib;
	bool autotop, forvpr;
	int lut;

	void clear_flags() override
	{
		top_module.clear();
		plib.clear();
		autotop = false;
		lut = 4;
		forvpr = false;
	}

	// TODO: bring back relevant flags to carry through to synth call
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module = args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos) {
					run_from = args[++argidx];
					run_to = args[argidx];
				} else {
					run_from = args[++argidx].substr(0, pos);
					run_to = args[argidx].substr(pos+1);
				}
				continue;
			}
			if (args[argidx] == "-vpr") {
				forvpr = true;
				continue;
			}
			if (args[argidx] == "-auto-top") {
				autotop = true;
				continue;
			}
			if (args[argidx] == "-lut") {
				lut = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-plib" && argidx+1 < args.size()) {
				plib = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH_FABULOUS pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (plib.empty())
			run("read_verilog -lib +/fabulous/prims.v");
		else
			run("read_verilog -lib " + plib);

		if (top_module.empty()) {
			if (autotop)
				run("hierarchy -check -auto-top");
			else
				run("hierarchy -check");
		} else
			run(stringf("hierarchy -check -top %s", top_module.c_str()));

		run("proc");
 		run("tribuf -logic");
		run("deminout");
		run("synth -run coarse");
		run("memory_map");
		run("opt -full");
		run("techmap -map +/techmap.v");
		run("opt -fast");
		run("dfflegalize -cell $_DFF_P_ 0 -cell $_DLATCH_?_ x");
		run("techmap -map +/fabulous/latches_map.v");
		run("abc -lut $LUT_K -dress");
		run("clean");
		if (forvpr) 
			run("techmap -D LUT_K=$LUT_K -map +/fabulous/cells_map.v");
		run("clean");
		run("hierarchy -check");
		run("stat");
	}
} SynthPass;

PRIVATE_NAMESPACE_END
