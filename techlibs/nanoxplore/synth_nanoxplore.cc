/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024 Hannah Ravensloft <lofty@yosyshq.com> 
 *  Copyright (C) 2024 Miodrag Milanovic <micko@yosyshq.com> 
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

struct SynthNanoXplorePass : public ScriptPass
{
	SynthNanoXplorePass() : ScriptPass("synth_nanoxplore", "synthesis for NanoXplore FPGAs") { }

	void on_register() override
	{
		RTLIL::constpad["synth_nanoxplore.abc9.W"] = "300";
	}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_nanoxplore [options]\n");
		log("\n");
		log("This command runs synthesis for NanoXplore FPGAs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -family <family>\n");
		log("        run synthesis for the specified NanoXplore architecture\n");
		log("        generate the synthesis netlist for the specified family.\n");
		log("        supported values:\n");
		log("        - medium: NG-Medium\n");
		log("        - large: NG-Large\n");
		log("        - ultra: NG-Ultra\n");
		log("        - u300: NG-Ultra300\n");
		log("\n");
		log("    -json <file>\n");
		log("        write the design to the specified JSON file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis\n");
		log("\n");
		log("    -abc9\n");
		log("        use new ABC9 flow (EXPERIMENTAL)\n");
		log("\n");
		log("    -nocy\n");
		log("        do not map adders to CY cells\n");
		log("\n");
		log("    -norfram\n");
		log("        do not use Register File RAM cells in output netlist\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use block NX_RAM cells in output netlist\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not map multipliers to NX_DSP cells\n");
		log("\n");
		log("    -iopad\n");
		log("       insert IO buffers\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, json_file, family;
	bool flatten, abc9, nocy, norfram, nobram, nodsp, iopad;
	std::string postfix, rf_postfix;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		json_file = "";
		family = "";
		flatten = true;
		abc9 = false;
		nocy = false;
		norfram = false;
		nobram = false;
		nodsp = false;
		iopad = false;
		postfix = "";
		rf_postfix = "";
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if ((args[argidx] == "-family" || args[argidx] == "-arch") && argidx+1 < args.size()) {
				family = args[++argidx];
				continue;
			}
			if (args[argidx] == "-json" && argidx+1 < args.size()) {
				json_file = args[++argidx];
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
			if (args[argidx] == "-flatten") {
				flatten = true;
				continue;
			}
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-abc9") {
				abc9 = true;
				continue;
			}
			if (args[argidx] == "-nocy") {
				nocy = true;
				continue;
			}
			if (args[argidx] == "-norfram") {
				norfram = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
				continue;
			}
			if (args[argidx] == "-iopad") {
				iopad = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (family.empty()) {
			//log_warning("NanoXplore family not set, setting it to NG-ULTRA.\n");
			family = "ultra";
		}

		if (family == "ultra") {
			postfix = "_u";
			rf_postfix = "_u";
		} else if (family == "u300") {
			postfix = "_u";
			rf_postfix = "_u";
		} else if (family == "medium") {
			postfix = "_m";
			rf_postfix = "_l";
		} else if (family == "large") {
			postfix = "_l";
			rf_postfix = "_l";
		} else 
			log_cmd_error("Invalid NanoXplore -family setting: '%s'.\n", family.c_str());

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH_NANOXPLORE pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib -specify +/nanoxplore/cells_sim.v +/nanoxplore/cells_bb.v +/nanoxplore/cells_bb" + postfix + ".v");
			run("techmap -map +/nanoxplore/cells_wrap.v");
			run("techmap -map +/nanoxplore/cells_wrap" + postfix + ".v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (check_label("coarse"))
		{
			run("proc");
			if (flatten || help_mode)
				run("flatten", "(skip if -noflatten)");
			run("tribuf -logic");
			run("deminout");
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt -nodffe -nosdff");
			run("fsm");
			run("opt");
			run("wreduce");
			run("peepopt");
			run("opt_clean");
			run("share");
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=4");
			run("opt_expr");
			run("opt_clean");
			run("alumacc");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (check_label("map_ram"))
		{
			std::string args = "";
			if (nobram)
				args += " -no-auto-block";
			if (norfram)
				args += " -no-auto-distributed";
			if (help_mode)
				args += " [-no-auto-block] [-no-auto-distributed]";
			run("memory_libmap -lib +/nanoxplore/rf_rams"+  rf_postfix+ ".txt -lib +/nanoxplore/brams.txt" + args, "(-no-auto-block if -nobram, -no-auto-distributed if -norfram)");
			run("techmap -map +/nanoxplore/rf_rams_map"+  rf_postfix+ ".v -map +/nanoxplore/brams_map.v");
			run("techmap -map +/nanoxplore/cells_wrap" + postfix + ".v t:NX_XRFB* t:NX_RFB*");
		}

		if (check_label("map_ffram"))
		{
			//run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -full");
			//run("opt -undriven -fine -mux_undef");
		}

		if (check_label("map_gates"))
		{
			if (nocy)
				run("techmap");
			else
				run("techmap -map +/techmap.v -map +/nanoxplore/arith_map.v");
			if (help_mode || iopad) {
				run("iopadmap -bits -outpad $__BEYOND_OBUF I:PAD -inpad $__BEYOND_IBUF O:PAD A:top", "(only if '-iopad')");
				run("techmap -map +/nanoxplore/io_map.v");
				run("attrmvcp -attr LOC t:NX_IOB_O n:*");
				run("attrmvcp -attr LOC -driven t:NX_IOB_I n:*");
			}
			run("opt -fast");
		}

		if (check_label("map_ffs"))
		{
			run("dfflegalize -cell $_DFF_?P?_ 0 -cell $_ALDFF_?P_ 0 -cell $_SDFF_?P?_ 0");
			run("techmap -map +/nanoxplore/cells_map.v");
			run("opt_expr -undriven -mux_undef");
			run("clean -purge");
		}

		if (check_label("map_luts"))
		{
			if (abc9) {
				std::string abc9_opts = " -maxlut 4";
				std::string k = "synth_nanoxplore.abc9.W";
				if (active_design && active_design->scratchpad.count(k))
					abc9_opts += stringf(" -W %s", active_design->scratchpad_get_string(k).c_str());
				else
					abc9_opts += stringf(" -W %s", RTLIL::constpad.at(k).c_str());
				run("abc9" + abc9_opts);
			} else {
				std::string abc_args = " -dress";
				abc_args += " -lut 4";
				run("abc" + abc_args);
			}
			run("techmap -map +/nanoxplore/cells_map.v t:$lut");
			run("opt -fast");
			run("clean");
		}

		if (check_label("check"))
		{
			run("autoname");
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
			run("blackbox =A:whitebox");
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file.c_str()));
		}
	}
} SynthNanoXplorePass;

PRIVATE_NAMESPACE_END
