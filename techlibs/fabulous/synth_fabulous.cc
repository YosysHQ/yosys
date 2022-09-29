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
		log("    -vpr\n");
		log("        perform synthesis for the FABulous VPR flow (using slightly different techmapping).\n");
		log("\n");
		log("    -plib <primitive_library.v>\n");
		log("        use the specified Verilog file as a primitive library.\n");
		log("\n");
		log("    -encfile <file>\n");
		log("        passed to 'fsm_recode' via 'fsm'\n");
		log("\n");
		log("    -nofsm\n");
		log("        do not run FSM optimization\n");
		log("\n");
		log("    -noalumacc\n");
		log("        do not run 'alumacc' pass. i.e. keep arithmetic operators in\n");
		log("        their direct form ($add, $sub, etc.).\n");
		log("\n");
		log("    -nordff\n");
		log("        passed to 'memory'. prohibits merging of FFs into memory read ports\n");
		log("\n");
		log("    -noshare\n");
		log("        do not run SAT-based resource sharing\n");
		log("\n");
		log("    -run <from_label>[:<to_label>]\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -no-rw-check\n");
		log("        marks all recognized read ports as \"return don't-care value on\n");
		log("        read/write collision\" (same result as setting the no_rw_check\n");
		log("        attribute on all memories).\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_module, plib, fsm_opts, memory_opts;
	bool autotop, forvpr, noalumacc, nofsm, noshare;
	int lut;

	void clear_flags() override
	{
		top_module.clear();
		plib.clear();
		autotop = false;
		lut = 4;
		forvpr = false;
		noalumacc = false;
		nofsm = false;
		noshare = false;
	}

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
			if (args[argidx] == "-nofsm") {
				nofsm = true;
				continue;
			}
			if (args[argidx] == "-noalumacc") {
				noalumacc = true;
				continue;
			}
			if (args[argidx] == "-nordff") {
				memory_opts += " -nordff";
				continue;
			}
			if (args[argidx] == "-noshare") {
				noshare = true;
				continue;
			}
			if (args[argidx] == "-no-rw-check") {
				memory_opts += " -no-rw-check";
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

		// synth pass
		run("opt_expr");
		run("opt_clean");
		run("check");
		run("opt -nodffe -nosdff");
		if (!nofsm)
			run("fsm" + fsm_opts, "      (unless -nofsm)");
		run("opt");
		run("wreduce");
		run("peepopt");
		run("opt_clean");
		if (help_mode)
			run("techmap -map +/cmp2lut.v -map +/cmp2lcu.v", " (if -lut)");
		else if (lut)
			run(stringf("techmap -map +/cmp2lut.v -map +/cmp2lcu.v -D LUT_WIDTH=%d", lut));
		if (!noalumacc)
			run("alumacc", "  (unless -noalumacc)");
		if (!noshare)
			run("share", "    (unless -noshare)");
		run("opt");
		run("memory -nomap" + memory_opts);
		run("opt_clean");

		// RegFile extraction

		run("memory_libmap -lib +/fabulous/ram_regfile.txt");
		run("techmap -map +/fabulous/regfile_map.v");
		run("opt -fast -mux_undef -undriven -fine");

		run("memory_map");
		run("opt -undriven -fine");
		run("opt -full");
		run("techmap -map +/techmap.v");
		run("opt -fast");
		run("dfflegalize -cell $_DFF_P_ 0 -cell $_DLATCH_?_ x");
		run("techmap -map +/fabulous/latches_map.v");
		run("abc -lut $LUT_K -dress");
		run("clean");
		if (!forvpr) 
			run("techmap -D LUT_K=$LUT_K -map +/fabulous/cells_map.v");
		run("clean");
		run("hierarchy -check");
		run("stat");
	}
} SynthPass;

PRIVATE_NAMESPACE_END
