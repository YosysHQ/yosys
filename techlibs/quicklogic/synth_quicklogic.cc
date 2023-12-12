/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021 QuickLogic Corp.
 *  Copyright 2020-2022 F4PGA Authors
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
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
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
		log("        - qlf_k6n10f: K6N10f\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not use dsp_t1_* to implement multipliers and associated logic\n");
		log("        (qlf_k6n10f only).\n");
		log("\n");
		log("    -nocarry\n");
		log("        do not use adder_carry cells in output netlist.\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist.\n");
		log("\n");
		log("    -bramtypes\n");
		log("        Emit specialized BRAM cells for particular address and data width\n");
		log("        configurations.\n");
		log("\n");
		log("    -blif <file>\n");
		log("        write the design to the specified BLIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -verilog <file>\n");
		log("        write the design to the specified verilog file. writing of an output\n");
		log("        file is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -abc\n");
		log("        use old ABC flow, which has generally worse mapping results but is less\n");
		log("        likely to have bugs.\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, blif_file, edif_file, family, currmodule, verilog_file, lib_path;
	bool abc9, inferAdder, nobram, bramTypes, dsp;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		blif_file = "";
		edif_file = "";
		verilog_file = "";
		currmodule = "";
		family = "pp3";
		abc9 = true;
		inferAdder = true;
		nobram = false;
		bramTypes = false;
		lib_path = "+/quicklogic/";
		dsp = true;
	}

	void set_scratchpad_defaults(RTLIL::Design *design) {
		lib_path = design->scratchpad_get_string("ql.lib_path", lib_path);
		if (lib_path.back() != '/')
			lib_path += "/";
		inferAdder = !design->scratchpad_get_bool("ql.nocarry", false);
		nobram = design->scratchpad_get_bool("ql.nobram", false);
		bramTypes = design->scratchpad_get_bool("ql.bramtypes", false);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		clear_flags();
		set_scratchpad_defaults(design);

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos+1);
				continue;
			}
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
			if (args[argidx] == "-nocarry" || args[argidx] == "-no_adder") {
				inferAdder = false;
				continue;
			}
			if (args[argidx] == "-nobram" || args[argidx] == "-no_bram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-bramtypes" || args[argidx] == "-bram_types") {
				bramTypes = true;
				continue;
			}
			if (args[argidx] == "-nodsp" || args[argidx] == "-no_dsp") {
				dsp = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (family != "pp3" && family != "qlf_k6n10f")
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
		if (help_mode) {
			family = "<family>";
		}

		if (check_label("begin")) {
			std::string read_simlibs = stringf("read_verilog -lib -specify %scommon/cells_sim.v %s%s/cells_sim.v", lib_path.c_str(), lib_path.c_str(), family.c_str());
			if (family == "qlf_k6n10f") {
				read_simlibs += stringf(" %sqlf_k6n10f/brams_sim.v", lib_path.c_str());
				if (bramTypes)
					read_simlibs += stringf(" %sqlf_k6n10f/bram_types_sim.v", lib_path.c_str());
				if (dsp)
					read_simlibs += stringf(" %sqlf_k6n10f/dsp_sim.v", lib_path.c_str());
			}
			run(read_simlibs);
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (check_label("prepare")) {
			run("proc");
			run("flatten");
			if (help_mode || family == "pp3") {
				run("tribuf -logic", "                   (for pp3)");
			}
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
		}

		if (check_label("map_dsp", "(for qlf_k6n10f, skip if -nodsp)")
				&& ((dsp && family == "qlf_k6n10f") || help_mode)) {
			run("wreduce t:$mul");
			run("ql_dsp_macc");

			run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=20 -D DSP_B_MAXWIDTH=18 -D DSP_A_MINWIDTH=11 -D DSP_B_MINWIDTH=10 -D DSP_NAME=$__QL_MUL20X18");
			run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=10 -D DSP_B_MAXWIDTH=9 -D DSP_A_MINWIDTH=4 -D DSP_B_MINWIDTH=4 -D DSP_NAME=$__QL_MUL10X9");
			run("chtype -set $mul t:$__soft_mul");

			run("techmap -map " + lib_path + family + "/dsp_map.v -D USE_DSP_CFG_PARAMS=0");
			run("ql_dsp_simd");
			run("techmap -map " + lib_path + family + "/dsp_final_map.v");
			run("ql_dsp_io_regs");
		}

		if (check_label("coarse")) {
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=4");
			run("opt_expr");
			run("opt_clean");
			run("alumacc");
			run("pmuxtree");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (check_label("map_bram", "(for qlf_k6n10f, skip if -no_bram)")
				&& (family == "qlf_k6n10f" || help_mode)) {
			run("memory_libmap -lib " + lib_path + family + "/libmap_brams.txt");
			run("ql_bram_merge");
			run("techmap -map " + lib_path + family + "/libmap_brams_map.v");
			run("techmap -autoproc -map " + lib_path + family + "/brams_map.v");

			if (bramTypes || help_mode)
				run("ql_bram_types", "(if -bramtypes)");
		}

		if (check_label("map_ffram")) {
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map -iattr -attr !ram_block -attr !rom_block -attr logic_block "
				"-attr syn_ramstyle=auto -attr syn_ramstyle=registers "
				"-attr syn_romstyle=auto -attr syn_romstyle=logic");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates")) {
			if (inferAdder && family == "qlf_k6n10f") {
				run("techmap -map +/techmap.v -map " + lib_path + family + "/arith_map.v", "(unless -no_adder)");
			} else {
				run("techmap");
			}
			run("opt -fast");
			if (help_mode || family == "pp3") {
				run("muxcover -mux8 -mux4", "(for pp3)");
			}
		}

		if (check_label("map_ffs")) {
			run("opt_expr");
			if (help_mode) {
				run("shregmap -minlen <min> -maxlen <max>", "(for qlf_k6n10f)");
				run("dfflegalize -cell <supported FF types>");
				run("techmap -map " + lib_path + family + "/cells_map.v", "(for pp3)");
				run("techmap -map " + lib_path + family + "/ffs_map.v", "(for ql_k6n10f)");
			}
			if (family == "pp3") {
				run("dfflegalize -cell $_DFFSRE_PPPP_ 0 -cell $_DLATCH_?_ x");
				run("techmap -map " + lib_path + family + "/cells_map.v -map " + lib_path + family + "/ffs_map.v");
				run("opt_expr -mux_undef");
			} else if (family == "qlf_k6n10f") {
				run("shregmap -minlen 8 -maxlen 20");
				// FIXME: Apparently dfflegalize leaves around $_DLATCH_[NP]_ even if
				// not in the allowed set. As a workaround we put them in the allowed
				// set explicitly and map them later to $_DLATCHSR_[NP]NN_.
				run("dfflegalize -cell $_DFFSRE_?NNP_ 0 -cell $_DLATCHSR_?NN_ 0 -cell $_DLATCH_?_ 0" " -cell $_SDFFE_?N?P_ 0");
				run("techmap -map " + lib_path + family + "/ffs_map.v");
			}
			run("opt");
		}

		if (check_label("map_luts", "(for pp3)") && (help_mode || family == "pp3")) {
			run("techmap -map " + lib_path + family + "/latches_map.v");
			if (abc9) {
				run("read_verilog -lib -specify -icells " + lib_path + family + "/abc9_model.v");
				run("techmap -map " + lib_path + family + "/abc9_map.v");
				run("abc9 -maxlut 4 -dff");
				run("techmap -map " + lib_path + family + "/abc9_unmap.v");
			} else {
				run("abc -luts 1,2,2,4 -dress");
			}
			run("clean");
		}

		if (check_label("map_luts", "(for qlf_k6n10f)") && (help_mode || family == "qlf_k6n10f")) {
			if (abc9) {
				run("abc9 -maxlut 6");
			} else {
				run("abc -lut 6 -dress");
			}
			run("clean");
			run("opt_lut");
		}

		if (check_label("map_cells", "(for pp3)") && (help_mode || family == "pp3")) {
			run("techmap -map " + lib_path + family + "/lut_map.v");
			run("clean");
			run("opt_lut");
		}

		if (check_label("check")) {
			run("autoname");
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
		}

		if (check_label("iomap", "(for pp3)") && (family == "pp3" || help_mode)) {
			run("clkbufmap -inpad ckpad Q:P");
			run("iopadmap -bits -outpad outpad A:P -inpad inpad Q:P -tinoutpad bipad EN:Q:A:P A:top");
		}

		if (check_label("finalize")) {
			if (help_mode || family == "pp3") {
				run("setundef -zero -params -undriven", "(for pp3)");
			}
			if (family == "pp3" || !edif_file.empty()) {
				run("hilomap -hicell logic_1 A -locell logic_0 A -singleton A:top", "(for pp3 or if -edif)");
			}
			run("opt_clean -purge");
			run("check");
			run("blackbox =A:whitebox");
		}

		if (check_label("blif", "(if -blif)")) {
			if (!blif_file.empty() || help_mode) {
				run(stringf("write_blif -attr -param %s %s", top_opt.c_str(), blif_file.c_str()));
			}
		}

		if (check_label("verilog", "(if -verilog)")) {
			if (!verilog_file.empty() || help_mode) {
				run(stringf("write_verilog -noattr -nohex %s", help_mode ? "<file-name>" : verilog_file.c_str()));
			}
		}
	}

} SynthQuicklogicPass;

PRIVATE_NAMESPACE_END
