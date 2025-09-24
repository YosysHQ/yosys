/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *            (C) 2019  Eddie Hung    <eddie@fpgeh.com>
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

struct SynthAnalogDevicesPass : public ScriptPass
{
	SynthAnalogDevicesPass() : ScriptPass("synth_analogdevices", "synthesis for Analog Devices FPGAs") { }

	void on_register() override
	{
		RTLIL::constpad["synth_analogdevices.abc9.W"] = "300"; // Number with which ABC will map a 6-input gate
								    // to one LUT6 (instead of a LUT5 + LUT2)
	}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_analogdevices [options]\n");
		log("\n");
		log("This command runs synthesis for Analog Devices FPGAs. This command does not operate on\n");
		log("partly selected designs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -edif <file>\n");
		log("        write the design to the specified edif file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nolutram\n");
		log("        do not use distributed RAM cells in output netlist\n");
		log("\n");
		log("    -nosrl\n");
		log("        do not use distributed SRL cells in output netlist\n");
		log("\n");
		log("    -nocarry\n");
		log("        do not use XORCY/MUXCY/CARRY4 cells in output netlist\n");
		log("\n");
		log("    -nowidelut\n");
		log("        do not use MUXF[7-8] resources to implement LUTs larger than native for\n");
		log("        the target\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not use DSP48*s to implement multipliers and associated logic\n");
		log("\n");
		log("    -noiopad\n");
		log("        disable I/O buffer insertion (useful for hierarchical or \n");
		log("        out-of-context flows)\n");
		log("\n");
		log("    -noclkbuf\n");
		log("        disable automatic clock buffer insertion\n");
		log("\n");
		log("    -widemux <int>\n");
		log("        enable inference of hard multiplexer resources (MUXF[78]) for muxes at\n");
		log("        or above this number of inputs (minimum value 2, recommended value >= 5)\n");
		log("        default: 0 (no inference)\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis\n");
		log("\n");
		log("    -dff\n");
		log("        run 'abc'/'abc9' with -dff option\n");
		log("\n");
		log("    -retime\n");
		log("        run 'abc' with '-D 1' option to enable flip-flop retiming.\n");
		log("        implies -dff.\n");
		log("\n");
		log("    -noabc9\n");
		log("        disable use of new ABC9 flow\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	std::string top_opt, edif_file, json_file;
	bool flatten, retime, noiopad, noclkbuf, nobram, nolutram, nosrl, nocarry, nowidelut, nodsp;
	bool abc9, dff;
	bool flatten_before_abc;
	int widemux;
	int widelut_size;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		edif_file.clear();
		flatten = true;
		retime = false;
		noiopad = false;
		noclkbuf = false;
		nocarry = false;
		nobram = false;
		nolutram = false;
		nosrl = false;
		nocarry = false;
		nowidelut = false;
		nodsp = false;
		abc9 = true;
		dff = false;
		flatten_before_abc = false;
		widemux = 0;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-edif" && argidx+1 < args.size()) {
				edif_file = args[++argidx];
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
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-flatten_before_abc") {
				flatten_before_abc = true;
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
			if (args[argidx] == "-nolutram") {
				nolutram = true;
				continue;
			}
			if (args[argidx] == "-nosrl") {
				nosrl = true;
				continue;
			}
			if (args[argidx] == "-widemux" && argidx+1 < args.size()) {
				widemux = atoi(args[++argidx].c_str());
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
			if (args[argidx] == "-json" && argidx+1 < args.size()) {
				json_file = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (widemux != 0 && widemux < 2)
			log_cmd_error("-widemux value must be 0 or >= 2.\n");

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (abc9 && retime)
			log_cmd_error("-retime option not currently compatible with -abc9!\n");

		log_header(design, "Executing SYNTH_ANALOGDEVICES pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (check_label("begin")) {
			std::string read_args;
			read_args += " -lib -specify +/analogdevices/cells_sim.v";
			run("read_verilog" + read_args);

			run("read_verilog -lib +/analogdevices/cells_xtra.v");

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
			if (help_mode)
				run("wreduce [-keepdc]", "(option for '-widemux')");
			else
				run("wreduce" + std::string(widemux > 0 ? " -keepdc" : ""));
			run("peepopt");
			run("opt_clean");

			if (widemux > 0 || help_mode)
				run("muxpack", "    ('-widemux' only)");

			// xilinx_srl looks for $shiftx cells for identifying variable-length
			//   shift registers, so attempt to convert $pmux-es to this
			// Also: wide multiplexer inference benefits from this too
			if (!(nosrl && widemux == 0) || help_mode) {
				run("pmux2shiftx", "(skip if '-nosrl' and '-widemux=0')");
				run("clean", "      (skip if '-nosrl' and '-widemux=0')");
			}
		}

		if (check_label("map_dsp", "(skip if '-nodsp')")) {
			if (!nodsp || help_mode) {
				run("memory_dff"); // xilinx_dsp will merge registers, reserve memory port registers first
				// NB: Xilinx multipliers are signed only
				if (help_mode)
					run("techmap -map +/mul2dsp.v -map +/analogdevices/{family}_dsp_map.v {options}");
				run("techmap -map +/mul2dsp.v -map +/analogdevices/dsp_map.v -D DSP_A_MAXWIDTH=25 -D DSP_B_MAXWIDTH=18 "
					"-D DSP_A_MAXWIDTH_PARTIAL=18 "	// Partial multipliers are intentionally
									// limited to 18x18 in order to take
									// advantage of the (PCOUT << 17) -> PCIN
									// dedicated cascade chain capability
					"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
					"-D DSP_Y_MINWIDTH=9 " // UG901 suggests small multiplies are those 4x4 and smaller
					"-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL25X18");

				run("select a:mul2dsp");
				run("setattr -unset mul2dsp");
				run("opt_expr -fine");
				run("wreduce");
				run("select -clear");
				if (help_mode)
					run("xilinx_dsp -family <family>");
				else
					run("xilinx_dsp -family xc7");
				run("chtype -set $mul t:$__soft_mul");
			}
		}

		if (check_label("coarse")) {
			run("techmap -map +/cmp2lut.v -map +/cmp2lcu.v -D LUT_WIDTH=6");
			run("alumacc");
			run("share");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (check_label("map_memory")) {
			std::string params = "";
			std::string lutrams_map = "+/analogdevices/lutrams_<family>_map.v";
			std::string brams_map = "+/analogdevices/brams_<family>_map.v";
			if (help_mode) {
				params = " [...]";
			} else {
				params += " -logic-cost-rom 0.015625";
				params += " -lib +/analogdevices/lutrams.txt";
				lutrams_map = "+/analogdevices/lutrams_map.v";
				params += " -lib +/analogdevices/brams.txt";
				params += " -D HAS_SIZE_36";
				params += " -D HAS_CASCADE";
				params += " -D HAS_CONFLICT_BUG";
				params += " -D HAS_MIXWIDTH_SDP";
				brams_map = "+/analogdevices/brams_map.v";
				if (nolutram)
					params += " -no-auto-distributed";
				if (nobram)
					params += " -no-auto-block";
			}
			run("memory_libmap" + params);
			run("techmap -map " + lutrams_map);
			run("techmap -map " + brams_map);
		}

		if (check_label("map_ffram")) {
			if (widemux > 0) {
				run("opt -fast -mux_bool -undriven -fine"); // Necessary to omit -mux_undef otherwise muxcover
									    // performs less efficiently
			} else {
				run("opt -fast -full");
			}
			run("memory_map");
		}

		if (check_label("fine")) {
			if (help_mode) {
				run("simplemap t:$mux", "('-widemux' only)");
				run("muxcover <internal options>", "('-widemux' only)");
			} else if (widemux > 0) {
				run("simplemap t:$mux");
				constexpr int cost_mux2 = 100;
				std::string muxcover_args = stringf(" -nodecode -mux2=%d", cost_mux2);
				switch (widemux) {
					case  2: muxcover_args += stringf(" -mux4=%d -mux8=%d -mux16=%d", cost_mux2+1, cost_mux2+2, cost_mux2+3); break;
					case  3:
					case  4: muxcover_args += stringf(" -mux4=%d -mux8=%d -mux16=%d", cost_mux2*(widemux-1)-2, cost_mux2*(widemux-1)-1, cost_mux2*(widemux-1)); break;
					case  5:
					case  6:
					case  7:
					case  8: muxcover_args += stringf(" -mux8=%d -mux16=%d", cost_mux2*(widemux-1)-1, cost_mux2*(widemux-1)); break;
					case  9:
					case 10:
					case 11:
					case 12:
					case 13:
					case 14:
					case 15:
					default: muxcover_args += stringf(" -mux16=%d", cost_mux2*(widemux-1)-1); break;
				}
				run("muxcover " + muxcover_args);
			}
			run("opt -full");

			if (!nosrl || help_mode)
				run("xilinx_srl -variable -minlen 3", "(skip if '-nosrl')");

			std::string techmap_args = " -map +/techmap.v -D LUT_SIZE=6";
			if (help_mode)
				techmap_args += " [-map +/analogdevices/mux_map.v]";
			else if (widemux > 0)
				techmap_args += stringf(" -D MIN_MUX_INPUTS=%d -map +/analogdevices/mux_map.v", widemux);
			if (!nocarry) {
				techmap_args += " -map +/analogdevices/arith_map.v";
			}
			run("techmap " + techmap_args);
			run("opt -fast");
		}

		if (check_label("map_cells")) {
			// Needs to be done before logic optimization, so that inverters (inserted
			// here because of negative-polarity output enable) are handled.
			if (help_mode || !noiopad)
				run("iopadmap -bits -outpad OUTBUF I:O -inpad INBUF O:I -toutpad OBUFT ~T:I:O -tinoutpad IOBUF ~T:O:I:IO A:top", "(skip if '-noiopad')");
			std::string techmap_args = "-map +/techmap.v -map +/analogdevices/cells_map.v";
			if (widemux > 0)
				techmap_args += stringf(" -D MIN_MUX_INPUTS=%d", widemux);
			run("techmap " + techmap_args);
			run("clean");
		}

		if (check_label("map_ffs")) {
			run("dfflegalize -cell $_DFFE_?P?P_ 01 -cell $_SDFFE_?P?P_ 01");
			if (abc9 || help_mode) {
				if (dff || help_mode)
					run("zinit -all w:* t:$_SDFFE_*", "('-dff' only)");
				run("techmap -map +/analogdevices/ff_map.v", "('-abc9' only)");
			}
		}

		if (check_label("map_luts")) {
			run("opt_expr -mux_undef -noclkinv");
			if (flatten_before_abc)
				run("flatten");
			if (help_mode)
				run("abc -luts 2:2,3,6:5[,10,20] [-dff] [-D 1]", "(option for '-nowidelut', '-dff', '-retime')");
			else if (abc9) {
				run("read_verilog -icells -lib -specify +/analogdevices/abc9_model.v");
				std::string abc9_opts;
				std::string k = "synth_analogdevices.abc9.W";
				if (active_design && active_design->scratchpad.count(k))
					abc9_opts += stringf(" -W %s", active_design->scratchpad_get_string(k).c_str());
				else {
					abc9_opts += stringf(" -W %s", RTLIL::constpad.at("synth_analogdevices.abc9.W").c_str());
				}
				if (nowidelut)
					abc9_opts += stringf(" -maxlut 6");
				if (dff)
					abc9_opts += " -dff";
				run("abc9" + abc9_opts);
			}
			else {
				std::string abc_opts;
				if (nowidelut)
					abc_opts += " -luts 2:2,3,6:5";
				else
					abc_opts += " -luts 2:2,3,6:5,10,20";
				if (dff)
					abc_opts += " -dff";
				if (retime)
					abc_opts += " -D 1";
				run("abc" + abc_opts);
			}
			run("clean");

			if (help_mode || !abc9)
				run("techmap -map +/analogdevices/ff_map.v", "(only if not '-abc9')");
			// This shregmap call infers fixed length shift registers after abc
			//   has performed any necessary retiming
			if (!nosrl || help_mode)
				run("xilinx_srl -fixed -minlen 3", "(skip if '-nosrl')");
			std::string techmap_args = "-map +/analogdevices/lut_map.v -map +/analogdevices/cells_map.v";
			techmap_args += " -D LUT_WIDTH=6";
			run("techmap " + techmap_args);
			run("xilinx_dffopt");
			run("opt_lut_ins -tech xilinx");
		}

		if (check_label("finalize")) {
			if (help_mode || !noclkbuf)
				run("clkbufmap -buf BUFG O:I", "(skip if '-noclkbuf')");
			run("clean");
		}

		if (check_label("check")) {
			run("hierarchy -check");
			run("stat -tech xilinx");
			run("check -noinit");
			run("blackbox =A:whitebox");
		}

		if (check_label("edif")) {
			if (!edif_file.empty() || help_mode) {
				run("delete t:$scopeinfo");
				run(stringf("write_edif %s", edif_file.c_str()));
			}
		}
	}
} SynthAnalogDevicesPass;

PRIVATE_NAMESPACE_END
