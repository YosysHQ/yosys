/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021 QuickLogic Corp.
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
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthQuickLogicPass : public ScriptPass {

	SynthQuickLogicPass() : ScriptPass("synth_quicklogic", "Synthesis for QuickLogic FPGAs") {}

	void help() override
	{
		log("\n");
		log("   synth_quicklogic [options]\n");
		log("This command runs synthesis for QuickLogic FPGAs\n");
		log("\n");
		log("    -top <module>\n");
		log("         use the specified module as top module\n");
		log("\n");
		log("    -family <family>\n");
		log("        run synthesis for the specified QuickLogic architecture\n");
		log("        generate the synthesis netlist for the specified family.\n");
		log("        supported values:\n");
		log("        - pp3: PolarPro 3 \n");
		log("\n");
		log("    -blif <file>\n");
		log("        write the design to the specified BLIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -verilog <file>\n");
		log("        write the design to the specified verilog file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -abc\n");
		log("        use old ABC flow, which has generally worse mapping results but is less\n");
		log("        likely to have bugs.\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, blif_file, family, currmodule, verilog_file;
	bool abc9;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		blif_file = "";
		verilog_file = "";
		currmodule = "";
		family = "pp3";
		abc9 = true;
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
			if (args[argidx] == "-family" && argidx+1 < args.size()) {
				family = args[++argidx];
				continue;
			}
			if (args[argidx] == "-blif" && argidx+1 < args.size()) {
				blif_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-verilog" && argidx+1 < args.size()) {
				verilog_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-abc") {
				abc9 = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (family != "pp3")
			log_cmd_error("Invalid family specified: '%s'\n", family.c_str());

		if (abc9 && design->scratchpad_get_int("abc9.D", 0) == 0) {
			log_warning("delay target has not been set via SDC or scratchpad; assuming 12 MHz clock.\n");
			design->scratchpad_set_int("abc9.D", 41667); // 12MHz = 83.33.. ns; divided by two to allow for interconnect delay.
		}

		log_header(design, "Executing SYNTH_QUICKLOGIC pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (check_label("begin")) {
			run(stringf("read_verilog -lib -specify +/quicklogic/cells_sim.v +/quicklogic/%s_cells_sim.v", family.c_str()));
			run("read_verilog -lib -specify +/quicklogic/lut_sim.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (check_label("coarse")) {
			run("proc");
			run("flatten");
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
			run("pmuxtree");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (check_label("map_ffram")) {
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map -iattr -attr !ram_block -attr !rom_block -attr logic_block "
				"-attr syn_ramstyle=auto -attr syn_ramstyle=registers "
				"-attr syn_romstyle=auto -attr syn_romstyle=logic");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates")) {
			run("techmap");
			run("opt -fast");
			run("muxcover -mux8 -mux4");
		}

		if (check_label("map_ffs")) {
			run("opt_expr");
			run("dfflegalize -cell $_DFFSRE_PPPP_ 0 -cell $_DLATCH_?_ x");

			run(stringf("techmap -map +/quicklogic/%s_cells_map.v -map +/quicklogic/%s_ffs_map.v", family.c_str(), family.c_str()));

			run("opt_expr -mux_undef");
		}

		if (check_label("map_luts")) {
			run(stringf("techmap -map +/quicklogic/%s_latches_map.v", family.c_str()));
			if (abc9) {
				run("read_verilog -lib -specify -icells +/quicklogic/abc9_model.v");
				run("techmap -map +/quicklogic/abc9_map.v");
				run("abc9 -maxlut 4 -dff");
				run("techmap -map +/quicklogic/abc9_unmap.v");
			} else {
				run("abc -luts 1,2,2,4 -dress");
			}
			run("clean");
		}

		if (check_label("map_cells")) {
			run(stringf("techmap -map +/quicklogic/%s_lut_map.v", family.c_str()));
			run("clean");
		}

		if (check_label("check")) {
			run("autoname");
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
		}

		if (check_label("iomap")) {
			run("clkbufmap -inpad ckpad Q:P");
			run("iopadmap -bits -outpad outpad A:P -inpad inpad Q:P -tinoutpad bipad EN:Q:A:P A:top");
		}

		if (check_label("finalize")) {
			run("setundef -zero -params -undriven");
			run("hilomap -hicell logic_1 A -locell logic_0 A -singleton A:top");
			run("opt_clean -purge");
			run("check");
			run("blackbox =A:whitebox");
		}

		if (check_label("blif")) {
			if (!blif_file.empty() || help_mode) {
				run(stringf("write_blif -attr -param %s %s", top_opt.c_str(), blif_file.c_str()));
			}
		}

		if (check_label("verilog")) {
			if (!verilog_file.empty()) {
				run("write_verilog -noattr -nohex " + verilog_file);
			}
		}
	}

} SynthQuicklogicPass;

PRIVATE_NAMESPACE_END
