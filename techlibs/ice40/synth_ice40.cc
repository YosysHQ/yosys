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

struct SynthIce40Pass : public ScriptPass
{
	SynthIce40Pass() : ScriptPass("synth_ice40", "synthesis for iCE40 FPGAs") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_ice40 [options]\n");
		log("\n");
		log("This command runs synthesis for iCE40 FPGAs.\n");
		log("\n");
		log("    -device < hx | lp | u >\n");
		log("        relevant only for '-abc9' flow, optimise timing for the specified device.\n");
		log("        default: hx\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -blif <file>\n");
		log("        write the design to the specified BLIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -edif <file>\n");
		log("        write the design to the specified EDIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
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
		log("    -retime\n");
		log("        run 'abc' with '-dff -D 1' options\n");
		log("\n");
		log("    -nocarry\n");
		log("        do not use SB_CARRY cells in output netlist\n");
		log("\n");
		log("    -nodffe\n");
		log("        do not use SB_DFFE* cells in output netlist\n");
		log("\n");
		log("    -dffe_min_ce_use <min_ce_use>\n");
		log("        do not use SB_DFFE* cells if the resulting CE line would go to less\n");
		log("        than min_ce_use SB_DFFE* in output netlist\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use SB_RAM40_4K* cells in output netlist\n");
		log("\n");
		log("    -dsp\n");
		log("        use iCE40 UltraPlus DSP cells for large arithmetic\n");
		log("\n");
		log("    -noabc\n");
		log("        use built-in Yosys LUT techmapping instead of abc\n");
		log("\n");
		log("    -abc2\n");
		log("        run two passes of 'abc' for slightly improved logic density\n");
		log("\n");
		log("    -vpr\n");
		log("        generate an output netlist (and BLIF file) suitable for VPR\n");
		log("        (this feature is experimental and incomplete)\n");
		log("\n");
		log("    -abc9\n");
		log("        use new ABC9 flow (EXPERIMENTAL)\n");
		log("\n");
        log("    -flowmap\n");
        log("        use FlowMap LUT techmapping instead of abc (EXPERIMENTAL)\n");
        log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, blif_file, edif_file, json_file, device_opt;
	bool nocarry, nodffe, nobram, dsp, flatten, retime, noabc, abc2, vpr, abc9, flowmap;
	int min_ce_use;

	void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
		blif_file = "";
		edif_file = "";
		json_file = "";
		nocarry = false;
		nodffe = false;
		min_ce_use = -1;
		nobram = false;
		dsp = false;
		flatten = true;
		retime = false;
		noabc = false;
		abc2 = false;
		vpr = false;
		abc9 = false;
        flowmap = false;
		device_opt = "hx";
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
			if (args[argidx] == "-blif" && argidx+1 < args.size()) {
				blif_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-edif" && argidx+1 < args.size()) {
				edif_file = args[++argidx];
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
			if (args[argidx] == "-retime") {
				retime = true;
				continue;
			}
			if (args[argidx] == "-relut") {
				// removed, opt_lut is always run
				continue;
			}
			if (args[argidx] == "-nocarry") {
				nocarry = true;
				continue;
			}
			if (args[argidx] == "-nodffe") {
				nodffe = true;
				continue;
			}
			if (args[argidx] == "-dffe_min_ce_use" && argidx+1 < args.size()) {
				min_ce_use = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-dsp") {
				dsp = true;
				continue;
			}
			if (args[argidx] == "-noabc") {
				noabc = true;
				continue;
			}
			if (args[argidx] == "-abc2") {
				abc2 = true;
				continue;
			}
			if (args[argidx] == "-vpr") {
				vpr = true;
				continue;
			}
			if (args[argidx] == "-abc9") {
				abc9 = true;
				continue;
			}
			if (args[argidx] == "-device" && argidx+1 < args.size()) {
				device_opt = args[++argidx];
				continue;
			}
            if (args[argidx] == "-flowmap") {
                flowmap = true;
                continue;
            }
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");
		if (device_opt != "hx" && device_opt != "lp" && device_opt !="u")
			log_cmd_error("Invalid or no device specified: '%s'\n", device_opt.c_str());

		if (abc9 && retime)
			log_cmd_error("-retime option not currently compatible with -abc9!\n");

        if (abc9 && noabc)
            log_cmd_error("-abc9 is incompatible with -noabc!\n");
        if (abc9 && flowmap)
            log_cmd_error("-abc9 is incompatible with -flowmap!\n");
        if (flowmap && noabc)
            log_cmd_error("-flowmap is incompatible with -noabc!\n");

		log_header(design, "Executing SYNTH_ICE40 pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
	{
		std::string define;
		if (device_opt == "lp")
			define = "-D ICE40_LP";
		else if (device_opt == "u")
			define = "-D ICE40_U";
		else
			define = "-D ICE40_HX";
		if (check_label("begin"))
		{
			run("read_verilog " + define + " -lib -specify +/ice40/cells_sim.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
			run("proc");
		}

		if (check_label("flatten", "(unless -noflatten)"))
		{
			if (flatten) {
				run("flatten");
				run("tribuf -logic");
				run("deminout");
			}
		}

		if (check_label("coarse"))
		{
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt");
			run("wreduce");
			run("peepopt");
			run("opt_clean");
			run("share");
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=4");
			run("opt_expr");
			run("opt_clean");
			if (help_mode || dsp) {
				run("memory_dff"); // ice40_dsp will merge registers, reserve memory port registers first
				run("wreduce t:$mul");
				run("techmap -map +/mul2dsp.v -map +/ice40/dsp_map.v -D DSP_A_MAXWIDTH=16 -D DSP_B_MAXWIDTH=16 "
						"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 -D DSP_Y_MINWIDTH=11 "
						"-D DSP_NAME=$__MUL16X16", "(if -dsp)");
				run("select a:mul2dsp", "              (if -dsp)");
				run("setattr -unset mul2dsp", "        (if -dsp)");
				run("opt_expr -fine", "                (if -dsp)");
				run("wreduce", "                       (if -dsp)");
				run("select -clear", "                 (if -dsp)");
				run("ice40_dsp", "                     (if -dsp)");
				run("chtype -set $mul t:$__soft_mul", "(if -dsp)");
			}
			run("alumacc");
			run("opt");
			run("fsm");
			run("opt -fast");
			run("memory -nomap");
			run("opt_clean");
		}

		if (!nobram && check_label("map_bram", "(skip if -nobram)"))
		{
			run("memory_bram -rules +/ice40/brams.txt");
			run("techmap -map +/ice40/brams_map.v");
			run("ice40_braminit");
		}

		if (check_label("map_ffram"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates"))
		{
			if (nocarry)
				run("techmap");
			else {
				run("ice40_wrapcarry");
				run("techmap -map +/techmap.v -map +/ice40/arith_map.v");
			}
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
			run("ice40_opt");
		}

		if (check_label("map_ffs"))
		{
			run("dffsr2dff");
			if (!nodffe)
				run("dff2dffe -direct-match $_DFF_*");
			if (min_ce_use >= 0) {
				run("opt_merge");
				run(stringf("dff2dffe -unmap-mince %d", min_ce_use));
			}
			run("techmap -D NO_LUT -D NO_ADDER -map +/ice40/cells_map.v");
			run("opt_expr -mux_undef");
			run("simplemap");
			run("ice40_ffinit");
			run("ice40_ffssr");
			run("ice40_opt -full");
		}

		if (check_label("map_luts"))
		{
			if (abc2 || help_mode) {
				run("abc", "      (only if -abc2)");
				run("ice40_opt", "(only if -abc2)");
			}
			run("techmap -map +/ice40/latches_map.v");
			if (noabc || flowmap || help_mode) {
				run("simplemap", "                               (if -noabc or -flowmap)");
                if (noabc || help_mode)
				    run("techmap -map +/gate2lut.v -D LUT_WIDTH=4", "(only if -noabc)");
                if (flowmap || help_mode)
                    run("flowmap -maxlut 4", "(only if -flowmap)");
			}
			if (!noabc) {
				if (abc9) {
					run("read_verilog " + define + " -icells -lib -specify +/abc9_model.v +/ice40/abc9_model.v");
					int wire_delay;
					if (device_opt == "lp")
						wire_delay = 400;
					else if (device_opt == "u")
						wire_delay = 750;
					else
						wire_delay = 250;
					run(stringf("abc9 -W %d", wire_delay));
				}
				else
					run("abc -dress -lut 4", "(skip if -noabc)");
			}
			run("ice40_wrapcarry -unwrap");
			run("techmap -D NO_LUT -map +/ice40/cells_map.v");
			run("clean");
			run("opt_lut -dlogic SB_CARRY:I0=2:I1=1:CI=0");
		}

		if (check_label("map_cells"))
		{
			if (vpr)
				run("techmap -D NO_LUT -map +/ice40/cells_map.v");
			else
				run("techmap -map +/ice40/cells_map.v", "(with -D NO_LUT in vpr mode)");

			run("clean");
		}

		if (check_label("check"))
		{
			run("autoname");
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
		}

		if (check_label("blif"))
		{
			if (!blif_file.empty() || help_mode) {
				if (vpr || help_mode) {
					run(stringf("opt_clean -purge"),
							"                                 (vpr mode)");
					run(stringf("write_blif -attr -cname -conn -param %s",
							help_mode ? "<file-name>" : blif_file.c_str()),
							" (vpr mode)");
				}
				if (!vpr)
					run(stringf("write_blif -gates -attr -param %s",
							help_mode ? "<file-name>" : blif_file.c_str()),
							"       (non-vpr mode)");
			}
		}

		if (check_label("edif"))
		{
			if (!edif_file.empty() || help_mode)
				run(stringf("write_edif %s", help_mode ? "<file-name>" : edif_file.c_str()));
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file.c_str()));
		}
	}
} SynthIce40Pass;

PRIVATE_NAMESPACE_END
