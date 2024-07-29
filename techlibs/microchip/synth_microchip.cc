/*
ISC License

Copyright (C) 2024 Microchip Technology Inc. and its subsidiaries

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthMicrochipPass : public ScriptPass {
	SynthMicrochipPass() : ScriptPass("synth_microchip", "synthesis for Microchip FPGAs") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_microchip [options]\n");
		log("\n");
		log("This command runs synthesis for Microchip FPGAs. This command creates \n");
		log("netlists that are compatible with Microchip PolarFire devices. \n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as the top module\n");
		log("\n");
		log("    -family <family>\n");
		log("        Run synthesis for the specified Microchip architecture. \n");
		log("        Generate the synthesis netlist for the specified family.\n");
		log("        supported values:\n");
		log("        - polarfire: PolarFire\n");
		log("\n");
		log("    -edif <file>\n");
		log("        Write the design to the specified edif file. Writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -blif <file>\n");
		log("        Write the design to the specified BLIF file. Writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -vlog <file>\n");
		log("        write the design to the specified Verilog file. writing of an output\n");
		log("        file is omitted if this parameter is not specified.\n");
		log("    -nobram\n");
		log("        Do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nocarry\n");
		log("        Do not use ARI1 cells in output netlist\n");
		log("\n");
		log("    -nodsp\n");
		log("        Do not use MATH blocks to implement multipliers and associated logic\n");
		log("\n");
		log("    -noiopad\n");
		log("        Disable I/O buffer insertion (useful for hierarchical or \n");
		log("        out-of-context flows)\n");
		log("\n");
		log("    -noclkbuf\n");
		log("        Disable automatic clock buffer insertion\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        Only run the commands between the labels (see below). an empty\n");
		log("        'from_label' is synonymous to 'begin', and empty 'to_label' is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis\n");
		log("\n");
		log("    -dff\n");
		log("        Run 'abc'/'abc9' with -dff option\n");
		log("\n");
		log("    -retime\n");
		log("        Run 'abc' with '-D 1' option to enable flip-flop retiming.\n");
		log("        implies -dff.\n");
		log("\n");
		log("    -noabc9\n");
		log("        Use classic ABC flow instead of ABC9\n");
		log("\n");
		log("    -discard-ffinit\n");
		log("        discard FF init value instead of emitting an error\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	std::string top_opt, edif_file, blif_file, vlog_file, family;
	bool flatten, retime, noiopad, noclkbuf, nobram, nocarry, nowidelut, nodsp;
	bool abc9, dff;
	bool discard_ffinit;
	int lut_size;

	// debug dump switches
	bool debug_memory, debug_carry;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		edif_file.clear();
		blif_file.clear();
		vlog_file.clear();
		family = "polarfire";
		flatten = true;
		retime = false;
		noiopad = false;
		noclkbuf = false;
		nocarry = false;
		nobram = false;
		nowidelut = false;
		nodsp = false;
		abc9 = true;
		dff = false;
		lut_size = 4;
		discard_ffinit = false;

		debug_memory = false;
		debug_carry = false;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-top" && argidx + 1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if ((args[argidx] == "-family" || args[argidx] == "-arch") && argidx + 1 < args.size()) {
				family = args[++argidx];
				continue;
			}
			if (args[argidx] == "-edif" && argidx + 1 < args.size()) {
				edif_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-blif" && argidx + 1 < args.size()) {
				blif_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-vlog" && argidx + 1 < args.size()) {
				vlog_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx + 1 < args.size()) {
				size_t pos = args[argidx + 1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos + 1);
				continue;
			}
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-retime") {
				dff = true;
				retime = true;
				continue;
			}
			if (args[argidx] == "-nocarry") {
				nocarry = true;
				continue;
			}
			if (args[argidx] == "-nowidelut") {
				nowidelut = true;
				continue;
			}
			if (args[argidx] == "-iopad") {
				continue;
			}
			if (args[argidx] == "-noiopad") {
				noiopad = true;
				continue;
			}
			if (args[argidx] == "-noclkbuf") {
				noclkbuf = true;
				continue;
			}
			if (args[argidx] == "-nocarry") {
				nocarry = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-noabc9") {
				abc9 = false;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
				continue;
			}
			if (args[argidx] == "-dff") {
				dff = true;
				continue;
			}
			if (args[argidx] == "-debug_memory") {
				debug_memory = true;
				continue;
			}
			if (args[argidx] == "-debug_carry") {
				debug_carry = true;
				continue;
			}
			if (args[argidx] == "-discard-ffinit") {
				discard_ffinit = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (family == "polarfire") {
			lut_size = 4;
		} else {
			log_cmd_error("Invalid Microchip -family setting: '%s'.\n", family.c_str());
		}

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (abc9 && retime)
			log_cmd_error("-retime option not currently compatible with -abc9!\n");

		log_header(design, "Executing SYNTH_MICROCHIP pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		std::string lut_size_s = std::to_string(lut_size);
		if (help_mode)
			lut_size_s = "[4]";

		if (check_label("begin")) {
			std::string read_args;
			read_args += " -lib -specify +/microchip/cells_sim.v";
			run("read_verilog" + read_args);

			run(stringf("hierarchy -check %s", top_opt.c_str()));
		}

		if (check_label("prepare")) {
			run("proc");
			if (flatten || help_mode)
				run("flatten", "(with '-flatten')");
			if (active_design)
				active_design->scratchpad_unset("tribuf.added_something");
			run("tribuf -logic");
			if (noiopad && active_design && active_design->scratchpad_get_bool("tribuf.added_something"))
				log_error("Tristate buffers are unsupported without the '-iopad' option.\n");
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
		}

		if (check_label("map_dsp", "(skip if '-nodsp')")) {
			if (!nodsp || help_mode) {
				run("memory_dff"); // microchip_dsp will merge registers, reserve memory port registers first
				if (help_mode)
					run("techmap -map +/mul2dsp.v -map +/microchip/{family}_dsp_map.v {options}");
				else if (family == "polarfire") // Microchip - map multipliers to DSP
					run("techmap -map +/mul2dsp.v -map +/microchip/polarfire_dsp_map.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18 "
					    "-D DSP_A_MAXWIDTH_PARTIAL=18 " // Partial multipliers are intentionally
									    // limited to 18x18 in order to take
									    // advantage of the (PCOUT >> 17) -> PCIN
									    // dedicated cascade chain capability
					    "-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
					    "-D DSP_Y_MINWIDTH=9 "
					    "-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL18X18");

				run("select a:mul2dsp");
				run("setattr -unset mul2dsp");
				run("opt_expr -fine");
				run("wreduce");
				run("select -clear");
				if (help_mode)
					run("microchip_dsp -family <family>");
				else if (family == "polarfire") // Microchip - absorb cells into DSP
					run("microchip_dsp -family " + family);

				run("chtype -set $mul t:$__soft_mul");
			}
		}

		if (check_label("coarse")) {
			run("techmap -map +/cmp2lut.v -map +/cmp2lcu.v -D LUT_WIDTH=" + lut_size_s);
			run("alumacc");
			run("share");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
			if (discard_ffinit || help_mode)
				run("attrmap -remove init", "(only if -discard-ffinit)");
		}

		if (check_label("map_memory")) {
			std::string params = "";
			std::string LSRAM_map = "+/microchip/LSRAM_map.v";
			std::string uSRAM_map = "+/microchip/uSRAM_map.v";
			if (debug_memory)
				run("write_verilog -noexpr memory_map_pre.vm");
			if (help_mode) {
				params = " [...]";
			} else {

				if (family == "polarfire") {
					// cost of a single bit for memory lowered to soft logic
					params += " -logic-cost-rom 0.015625";

					params += " -lib +/microchip/LSRAM.txt";
					params += " -lib +/microchip/uSRAM.txt";
					LSRAM_map = "+/microchip/LSRAM_map.v";
					uSRAM_map = "+/microchip/uSRAM_map.v";
				}
				if (nobram)
					params += " -no-auto-block";
			}

			// transform memories into intermediate cells
			// Cost based transformation. The cost is assigned by us for each cell.
			run("memory_libmap" + params);
			if (debug_memory)
				run("write_verilog -noexpr memory_map_libmap.vm");

			// map intermediate cells to actual RAM macros
			// NOTE: order doesnt matter here
			run("techmap -map " + LSRAM_map);
			run("techmap -map " + uSRAM_map);
			if (debug_memory)
				run("write_verilog -noexpr memory_map_final.vm");
		}

		if (check_label("map_ffram")) {
			run("opt -fast -full");

			// blast unmapped RAM to flops or LUTs
			run("memory_map");
		}

		if (check_label("fine")) {
			run("opt -full");

			if (debug_carry)
				run("write_verilog -noexpr ARI1_cells.vm");

			if (!nocarry) {
				// converts $mux -> $_MUX_ to allow muxcover to work
				run("simplemap t:$mux");

				// converts $and/$or/$xor to gate representation for extract_reduce to work
				run("simplemap t:$xor"); // only mapping reduce_xor

				// mapping based on Yosys internal gates
				if (debug_carry)
					run("write_verilog -noexpr ARI1_pre.vm");

				// collapse $_AND_/$_OR_/$_XOR_ chains into reduction cells
				run("extract_reduce");

				if (debug_carry)
					run("write_verilog -noexpr ARI1_extract_reduce.vm");

				// pack mux trees into $_MUX4_
				run("muxcover -nodecode -mux4=220");

				if (debug_carry)
					run("write_verilog -noexpr ARI1_muxcover.vm");

				run("techmap -map +/microchip/arith_map.v");
				if (debug_carry)
					run("write_verilog -noexpr ARI1_post.vm");
			}

			// convert all remaining cells to gates
			run("techmap -map +/techmap.v");

			run("opt -fast");
		}

		if (check_label("map_cells")) {
			// Needs to be done before logic optimization, so that inverters (inserted
			// 			here because of negative-polarity output enable) are handled.
			if (help_mode || !noiopad) {
				run("iopadmap -bits -inpad INBUF Y:PAD -outpad OUTBUF D:PAD -toutpad TRIBUFF E:D:PAD -tinoutpad BIBUF E:Y:D:PAD",
				    "(unless -noiobs)");
			}

			std::string techmap_args = "-map +/techmap.v -map +/microchip/cells_map.v";
			run("techmap " + techmap_args);
			run("clean");
		}

		if (check_label("map_ffs")) {
			// dfflegalize : Converts FFs to types supported by the target
			// 		this can convert less capable cells into more capable cells (e.g. dff -> dffe)

			// Based on PolarFire® FPGA Macro Library Guide
			// D-flop:
			// 		active high enable
			// 		active low clear or active low set
			// Latch:
			//		active low clear or active low set
			// SLE (can implement D-flop/Latch):
			//		active high EN
			//		active low async load (set/reset) with static load configuration via ADn (Q = ~ADn)
			//		active low sync load (set/reset) with static load configuration via SD
			//		static latch configuration bit
			// init not supported

			// Yosys internal cell description
			// 		see: https://yosyshq.readthedocs.io/projects/yosys/en/latest/yosys_internals/formats/cell_library.html
			//		see: common/simcells.v
			// $_DFF_[NP]_ 						(regular dff)
			// $_DFFE_[NP][NP]_ 				(enable)
			// $_DFF_[NP][NP][01]_ 				(async reset to 0/1)
			// $_DFFE_[NP][NP][01][NP]_ 		(async reset to 0/1 + enable)
			// $_ALDFF_[NP][NP]_				(async load)
			// $_ALDFFE_[NP][NP][NP]_			(async load + enable)
			// $_DFFSR_[NP][NP][NP]_			(async set & reset)
			// $_DFFSRE_[NP][NP][NP][NP]_		(async set & reset + enable)
			// $_SDFF_[NP][NP][01]_				(sync reset to 0/1)
			// $_SDFFE_[NP][NP][01][NP]_		(sync reset to 0/1 + enable, reset prioritize over enable)
			// $_SDFFCE_[NP][NP][01][NP]_		(sync reset to 0/1 + enable, enable prioritize over reset)
			// $_SR_[NP][NP]_					(set/reset latch)
			// $_DLATCH_[NP]_					(D-latch)
			// $_DLATCH_[NP][NP][01]_			(D-latch + reset to 0/1)
			// $_DLATCHSR_[NP][NP][NP]_			(D-latch + set + reset)

			if (family == "polarfire") {
				std::string params = "";

				// D-flop with async reset and enable
				// posedge CLK, active low reset to 1 or 0, active high EN
				params += " -cell $_DFFE_PN?P_ x";

				// D-flop with sync reset and enable, enable takes priority over reset
				// posedge CLK, active low reset to 1 or 0, active high EN
				params += " -cell $_SDFFCE_PN?P_ x";

				// D-latch + reset to 0/1
				// posedge CLK, active low reset to 1 or 0
				params += " -cell $_DLATCH_PN?_ x";

				run("dfflegalize" + params, "(Converts FFs to supported types)");
			}

			if (abc9 || help_mode) {
				if (dff || help_mode)
					run("zinit -all w:* t:$_SDFFCE_*", "('-dff' only)");
				run("techmap -D NO_LUT -map +/microchip/cells_map.v", "('-abc9' only)");
			}
		}

		if (check_label("map_luts")) {
			run("opt_expr -mux_undef -noclkinv");
			if (help_mode)
				run("abc -luts 2:2,3,6:5[,10,20] [-dff] [-D 1]", "(option for '-nowidelut', '-dff', '-retime')");
			else if (abc9) {

				std::string abc9_opts;
				// for the if command in abc to specify wire delay between adjacent LUTs (default = 0)
				// NOTE: should not have 0 wire delay between LUTs,
				//		 otherwise abc might use LUT2+LUT3 instead of single LUT4
				abc9_opts += " -W 300";
				if (nowidelut)
					abc9_opts += stringf(" -maxlut %d", lut_size);
				if (dff)
					abc9_opts += " -dff";
				run("abc9" + abc9_opts);
			} else {
				std::string abc_opts = " -lut " + lut_size_s;
				if (dff)
					abc_opts += " -dff";
				if (retime)
					abc_opts += " -D 1";
				run("abc" + abc_opts);
			}
			run("clean");

			if (help_mode || !abc9)
				run("techmap -D NO_LUT -map +/microchip/cells_map.v", "(only if not '-abc9')");
			std::string techmap_args = "-map +/microchip/cells_map.v -D FINAL_MAP";
			techmap_args += " -D LUT_WIDTH=" + lut_size_s;
			run("techmap " + techmap_args);

			if (help_mode || lut_size == 4)
				run("microchip_dffopt");
		}

		run("clkbufmap -buf CLKINT Y:A -inpad CLKBUF Y:PAD");

		run("clean -purge");

		if (check_label("check")) {
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
			run("blackbox =A:whitebox");
		}

		if (check_label("edif")) {
			if (!edif_file.empty() || help_mode)
				run(stringf("write_edif -pvector bra %s", edif_file.c_str()));
		}

		if (check_label("blif")) {
			if (!blif_file.empty() || help_mode)
				run(stringf("write_blif %s", blif_file.c_str()));
		}

		if (check_label("vlog"))
		{
			if (!vlog_file.empty() || help_mode)
				run(stringf("write_verilog %s", help_mode ? "<file-name>" : vlog_file.c_str()));
		}
	}
} SynthMicrochipPass;

PRIVATE_NAMESPACE_END
