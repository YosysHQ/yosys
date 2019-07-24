/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#define XC7_WIRE_DELAY 300 // Number with which ABC will map a 6-input gate
                           // to one LUT6 (instead of a LUT5 + LUT2)

struct SynthXilinxPass : public ScriptPass
{
	SynthXilinxPass() : ScriptPass("synth_xilinx", "synthesis for Xilinx FPGAs") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_xilinx [options]\n");
		log("\n");
		log("This command runs synthesis for Xilinx FPGAs. This command does not operate on\n");
		log("partly selected designs. At the moment this command creates netlists that are\n");
		log("compatible with 7-Series Xilinx devices.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -family {xcup|xcu|xc7|xc6s}\n");
		log("        run synthesis for the specified Xilinx architecture\n");
		log("        generate the synthesis netlist for the specified family.\n");
		log("        default: xc7\n");
		log("\n");
		log("    -edif <file>\n");
		log("        write the design to the specified edif file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -blif <file>\n");
		log("        write the design to the specified BLIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -vpr\n");
		log("        generate an output netlist (and BLIF file) suitable for VPR\n");
		log("        (this feature is experimental and incomplete)\n");
		log("\n");
		log("    -nobram\n");
		log("        disable inference of block rams\n");
		log("\n");
		log("    -nodram\n");
		log("        disable inference of distributed rams\n");
		log("\n");
		log("    -nosrl\n");
		log("        disable inference of shift registers\n");
		log("\n");
		log("    -nocarry\n");
		log("        do not use XORCY/MUXCY/CARRY4 cells in output netlist\n");
		log("\n");
		log("    -nowidelut\n");
		log("        do not use MUXF[78] resources to implement LUTs larger than LUT6s\n");
		log("\n");
		log("    -widemux <int>\n");
		log("        enable inference of hard multiplexer resources (MUXF[78]) for muxes at or\n");
		log("        above this number of inputs (minimum value 2, recommended value >= 5).\n");
		log("        default: 0 (no inference)\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -flatten\n");
		log("        flatten design before synthesis\n");
		log("\n");
		log("    -retime\n");
		log("        run 'abc' with -dff option\n");
		log("\n");
		log("    -abc9\n");
		log("        use new ABC9 flow (EXPERIMENTAL)\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	std::string top_opt, edif_file, blif_file, family;
	bool flatten, retime, vpr, nobram, nodram, nosrl, nocarry, nowidelut, abc9;
	int widemux;

	void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
		edif_file.clear();
		blif_file.clear();
		family = "xc7";
		flatten = false;
		retime = false;
		vpr = false;
		nocarry = false;
		nobram = false;
		nodram = false;
		nosrl = false;
		nocarry = false;
		nowidelut = false;
		abc9 = false;
		widemux = 0;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
			if ((args[argidx] == "-family" || args[argidx] == "-arch") && argidx+1 < args.size()) {
				family = args[++argidx];
				continue;
			}
			if (args[argidx] == "-edif" && argidx+1 < args.size()) {
				edif_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-blif" && argidx+1 < args.size()) {
				blif_file = args[++argidx];
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
			if (args[argidx] == "-retime") {
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
			if (args[argidx] == "-vpr") {
				vpr = true;
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
			if (args[argidx] == "-nodram") {
				nodram = true;
				continue;
			}
			if (args[argidx] == "-nosrl") {
				nosrl = true;
				continue;
			}
			if (args[argidx] == "-widemux" && argidx+1 < args.size()) {
				widemux = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-abc9") {
				abc9 = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (family != "xcup" && family != "xcu" && family != "xc7" && family != "xc6s")
			log_cmd_error("Invalid Xilinx -family setting: '%s'.\n", family.c_str());

		if (widemux != 0 && widemux < 2)
			log_cmd_error("-widemux value must be 0 or >= 2.\n");

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (abc9 && retime)
			log_cmd_error("-retime option not currently compatible with -abc9!\n");

		log_header(design, "Executing SYNTH_XILINX pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
	{
		if (check_label("begin")) {
			if (vpr)
				run("read_verilog -lib -icells -D _ABC -D_EXPLICIT_CARRY +/xilinx/cells_sim.v");
			else
				run("read_verilog -lib -icells -D _ABC +/xilinx/cells_sim.v");

			run("read_verilog -lib +/xilinx/cells_xtra.v");

			if (help_mode) {
				run("read_verilog -lib +/xilinx/{family}_brams_bb.v");
			} else if (family == "xc6s") {
				run("read_verilog -lib +/xilinx/xc6s_brams_bb.v");
			} else if (family == "xc7") {
				run("read_verilog -lib +/xilinx/xc7_brams_bb.v");
			}

			run(stringf("hierarchy -check %s", top_opt.c_str()));
		}

		if (check_label("coarse")) {
			run("proc");
			if (help_mode || flatten)
				run("flatten", "(if -flatten)");
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt");
			if (help_mode)
				run("wreduce [-keepdc]", "(option for '-widemux')");
			else
				run("wreduce" + std::string(widemux > 0 ? " -keepdc" : ""));
			run("peepopt");
			run("opt_clean");

			if (widemux > 0 || help_mode)
				run("muxpack", "    ('-widemux' only)");

			// shregmap -tech xilinx can cope with $shiftx and $mux
			//   cells for identifying variable-length shift registers,
			//   so attempt to convert $pmux-es to the former
			// Also: wide multiplexer inference benefits from this too
			if (!(nosrl && widemux == 0) || help_mode) {
				run("pmux2shiftx", "(skip if '-nosrl' and '-widemux=0')");
				run("clean", "      (skip if '-nosrl' and '-widemux=0')");
			}

			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=6");
			run("alumacc");
			run("share");
			run("opt");
			run("fsm");
			run("opt -fast");
			run("memory -nomap");
			run("opt_clean");
		}

		if (check_label("bram", "(skip if '-nobram')")) {
			if (help_mode) {
				run("memory_bram -rules +/xilinx/{family}_brams.txt");
				run("techmap -map +/xilinx/{family}_brams_map.v");
			} else if (!nobram) {
				if (family == "xc6s") {
					run("memory_bram -rules +/xilinx/xc6s_brams.txt");
					run("techmap -map +/xilinx/xc6s_brams_map.v");
				} else if (family == "xc7") {
					run("memory_bram -rules +/xilinx/xc7_brams.txt");
					run("techmap -map +/xilinx/xc7_brams_map.v");
				} else {
					log_warning("Block RAM inference not yet supported for family %s.\n", family.c_str());
				}
			}
		}

		if (check_label("dram", "(skip if '-nodram')")) {
			if (!nodram || help_mode) {
				run("memory_bram -rules +/xilinx/drams.txt");
				run("techmap -map +/xilinx/drams_map.v");
			}
		}

		if (check_label("fine")) {
			if (widemux > 0)
				run("opt -fast -mux_bool -undriven -fine"); // Necessary to omit -mux_undef otherwise muxcover
									    // performs less efficiently
			else
				run("opt -fast -full");
			run("memory_map");
			run("dffsr2dff");
			run("dff2dffe");
			if (help_mode) {
				run("simplemap t:$mux", "         ('-widemux' only)");
				run("muxcover <internal options>, ('-widemux' only)");
			}
			else if (widemux > 0) {
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

			if (!nosrl || help_mode) {
				// shregmap operates on bit-level flops, not word-level,
				//   so break those down here
				run("simplemap t:$dff t:$dffe", "       (skip if '-nosrl')");
				// shregmap with '-tech xilinx' infers variable length shift regs
				run("shregmap -tech xilinx -minlen 3", "(skip if '-nosrl')");
			}

			std::string techmap_args = " -map +/techmap.v";
			if (help_mode)
				techmap_args += " [-map +/xilinx/mux_map.v]";
			else if (widemux > 0)
				techmap_args += stringf(" -D MIN_MUX_INPUTS=%d -map +/xilinx/mux_map.v", widemux);
			if (help_mode)
				techmap_args += " [-map +/xilinx/arith_map.v]";
			else if (!nocarry) {
				techmap_args += " -map +/xilinx/arith_map.v";
				if (vpr)
					techmap_args += " -D _EXPLICIT_CARRY";
				else if (abc9)
					techmap_args += " -D _CLB_CARRY";
			}
			run("techmap " + techmap_args);
			run("opt -fast");
		}

		if (check_label("map_cells")) {
			std::string techmap_args = "-map +/techmap.v -D _ABC -map +/xilinx/cells_map.v";
			if (widemux > 0)
				techmap_args += stringf(" -D MIN_MUX_INPUTS=%d", widemux);
			run("techmap " + techmap_args);
			run("clean");
		}

		if (check_label("map_luts")) {
			run("opt_expr -mux_undef");
			if (help_mode)
				run("abc -luts 2:2,3,6:5[,10,20] [-dff]", "(option for 'nowidelut', option for '-retime')");
			else if (abc9) {
				if (family != "xc7")
					log_warning("'synth_xilinx -abc9' currently supports '-family xc7' only.\n");
				if (nowidelut)
					run("abc9 -lut +/xilinx/abc_xc7_nowide.lut -box +/xilinx/abc_xc7.box -W " + std::to_string(XC7_WIRE_DELAY));
				else
					run("abc9 -lut +/xilinx/abc_xc7.lut -box +/xilinx/abc_xc7.box -W " + std::to_string(XC7_WIRE_DELAY));
			}
			else {
				if (nowidelut)
					run("abc -luts 2:2,3,6:5" + string(retime ? " -dff" : ""));
				else
					run("abc -luts 2:2,3,6:5,10,20" + string(retime ? " -dff" : ""));
			}
			run("clean");

			// This shregmap call infers fixed length shift registers after abc
			//   has performed any necessary retiming
			if (!nosrl || help_mode)
				run("shregmap -minlen 3 -init -params -enpol any_or_none", "(skip if '-nosrl')");
			run("techmap -map +/xilinx/lut_map.v -map +/xilinx/ff_map.v -map +/xilinx/cells_map.v");
			run("dffinit -ff FDRE Q INIT -ff FDCE Q INIT -ff FDPE Q INIT -ff FDSE Q INIT "
					"-ff FDRE_1 Q INIT -ff FDCE_1 Q INIT -ff FDPE_1 Q INIT -ff FDSE_1 Q INIT");
			run("clean");
		}

		if (check_label("check")) {
			run("hierarchy -check");
			run("stat -tech xilinx");
			run("check -noinit");
		}

		if (check_label("edif")) {
			if (!edif_file.empty() || help_mode)
				run(stringf("write_edif -pvector bra %s", edif_file.c_str()));
		}

		if (check_label("blif")) {
			if (!blif_file.empty() || help_mode)
				run(stringf("write_blif %s", edif_file.c_str()));
		}
	}
} SynthXilinxPass;

PRIVATE_NAMESPACE_END
