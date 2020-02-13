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

struct SynthXilinxPass : public ScriptPass
{
	SynthXilinxPass() : ScriptPass("synth_xilinx", "synthesis for Xilinx FPGAs") { }

	void on_register() YS_OVERRIDE
	{
		RTLIL::constpad["synth_xilinx.abc9.xc7.W"] = "300"; // Number with which ABC will map a 6-input gate
								    // to one LUT6 (instead of a LUT5 + LUT2)
	}

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
		log("    -family <family>\n");
		log("        run synthesis for the specified Xilinx architecture\n");
		log("        generate the synthesis netlist for the specified family.\n");
		log("        supported values:\n");
		log("        - xcup: Ultrascale Plus\n");
		log("        - xcu: Ultrascale\n");
		log("        - xc7: Series 7 (default)\n");
		log("        - xc6s: Spartan 6\n");
		log("        - xc6v: Virtex 6\n");
		log("        - xc5v: Virtex 5 (EXPERIMENTAL)\n");
		log("        - xc4v: Virtex 4 (EXPERIMENTAL)\n");
		log("        - xc3sda: Spartan 3A DSP (EXPERIMENTAL)\n");
		log("        - xc3sa: Spartan 3A (EXPERIMENTAL)\n");
		log("        - xc3se: Spartan 3E (EXPERIMENTAL)\n");
		log("        - xc3s: Spartan 3 (EXPERIMENTAL)\n");
		log("        - xc2vp: Virtex 2 Pro (EXPERIMENTAL)\n");
		log("        - xc2v: Virtex 2 (EXPERIMENTAL)\n");
		log("        - xcve: Virtex E, Spartan 2E (EXPERIMENTAL)\n");
		log("        - xcv: Virtex, Spartan 2 (EXPERIMENTAL)\n");
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
		log("    -ise\n");
		log("        generate an output netlist suitable for ISE\n");
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
		log("        do not use MUXF[5-9] resources to implement LUTs larger than native for the target\n");
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
		log("    -uram\n");
		log("        infer URAM288s for large memories (xcup only)\n");
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
		log("    -dff\n");
		log("        run 'abc'/'abc9' with -dff option\n");
		log("\n");
		log("    -retime\n");
		log("        run 'abc' with '-D 1' option to enable flip-flop retiming.\n");
		log("        implies -dff.\n");
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
	bool flatten, retime, vpr, ise, noiopad, noclkbuf, nobram, nolutram, nosrl, nocarry, nowidelut, nodsp, uram;
	bool abc9, dff_mode;
	bool flatten_before_abc;
	int widemux;
	int lut_size;
	int widelut_size;

	void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
		edif_file.clear();
		blif_file.clear();
		family = "xc7";
		flatten = false;
		retime = false;
		vpr = false;
		ise = false;
		noiopad = false;
		noclkbuf = false;
		nocarry = false;
		nobram = false;
		nolutram = false;
		nosrl = false;
		nocarry = false;
		nowidelut = false;
		nodsp = false;
		uram = false;
		abc9 = false;
		dff_mode = false;
		flatten_before_abc = false;
		widemux = 0;
		lut_size = 6;
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
			if (args[argidx] == "-flatten_before_abc") {
				flatten_before_abc = true;
				continue;
			}
			if (args[argidx] == "-retime") {
				dff_mode = true;
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
			if (args[argidx] == "-ise") {
				ise = true;
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
			if (args[argidx] == "-nolutram" || /*deprecated alias*/ args[argidx] == "-nodram") {
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
			if (args[argidx] == "-abc9") {
				abc9 = true;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
				continue;
			}
			if (args[argidx] == "-uram") {
				uram = true;
				continue;
			}
			if (args[argidx] == "-dff") {
				dff_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (family == "xcup" || family == "xcu") {
			lut_size = 6;
			widelut_size = 9;
		} else if (family == "xc7" ||
				family == "xc6v" ||
				family == "xc5v" ||
				family == "xc6s") {
			lut_size = 6;
			widelut_size = 8;
		} else if (family == "xc4v" ||
				family == "xc3sda" ||
				family == "xc3sa" ||
				family == "xc3se" ||
				family == "xc3s" ||
				family == "xc2vp" ||
				family == "xc2v") {
			lut_size = 4;
			widelut_size = 8;
		} else if (family == "xcve" || family == "xcv") {
			lut_size = 4;
			widelut_size = 6;
		} else
			log_cmd_error("Invalid Xilinx -family setting: '%s'.\n", family.c_str());

		if (widemux != 0 && lut_size != 6)
			log_cmd_error("-widemux is not currently supported for LUT4-based architectures.\n");

		if (lut_size != 6) {
			log_warning("Shift register inference not yet supported for family %s.\n", family.c_str());
			nosrl = true;
		}

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
		std::string lut_size_s = std::to_string(lut_size);
		if (help_mode)
			lut_size_s = "[46]";
		std::string ff_map_file;
		if (help_mode)
			ff_map_file = "+/xilinx/{family}_ff_map.v";
		else if (family == "xc6s")
			ff_map_file = "+/xilinx/xc6s_ff_map.v";
		else
			ff_map_file = "+/xilinx/xc7_ff_map.v";

		if (check_label("begin")) {
			std::string read_args;
			if (vpr)
				read_args += " -D_EXPLICIT_CARRY";
			read_args += " -lib -specify +/xilinx/cells_sim.v";
			run("read_verilog" + read_args);

			run("read_verilog -lib +/xilinx/cells_xtra.v");

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

			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=" + lut_size_s);
		}

		if (check_label("map_dsp", "(skip if '-nodsp')")) {
			if (!nodsp || help_mode) {
				run("memory_dff"); // xilinx_dsp will merge registers, reserve memory port registers first
				// NB: Xilinx multipliers are signed only
				if (help_mode)
					run("techmap -map +/mul2dsp.v -map +/xilinx/{family}_dsp_map.v {options}");
				else if (family == "xc2v" || family == "xc2vp" || family == "xc3s" || family == "xc3se" || family == "xc3sa")
					run("techmap -map +/mul2dsp.v -map +/xilinx/xc3s_mult_map.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18 "
						"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
						"-D DSP_Y_MINWIDTH=9 " // UG901 suggests small multiplies are those 4x4 and smaller
						"-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL18X18");
				else if (family == "xc3sda")
					run("techmap -map +/mul2dsp.v -map +/xilinx/xc3sda_dsp_map.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18 "
						"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
						"-D DSP_Y_MINWIDTH=9 " // UG901 suggests small multiplies are those 4x4 and smaller
						"-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL18X18");
				else if (family == "xc6s")
					run("techmap -map +/mul2dsp.v -map +/xilinx/xc6s_dsp_map.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18 "
						"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
						"-D DSP_Y_MINWIDTH=9 " // UG901 suggests small multiplies are those 4x4 and smaller
						"-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL18X18");
				else if (family == "xc4v")
					run("techmap -map +/mul2dsp.v -map +/xilinx/xc4v_dsp_map.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18 "
						"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
						"-D DSP_Y_MINWIDTH=9 " // UG901 suggests small multiplies are those 4x4 and smaller
						"-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL18X18");
				else if (family == "xc5v")
					run("techmap -map +/mul2dsp.v -map +/xilinx/xc5v_dsp_map.v -D DSP_A_MAXWIDTH=25 -D DSP_B_MAXWIDTH=18 "
						"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
						"-D DSP_Y_MINWIDTH=9 " // UG901 suggests small multiplies are those 4x4 and smaller
						"-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL25X18");
				else if (family == "xc6v" || family == "xc7")
					run("techmap -map +/mul2dsp.v -map +/xilinx/xc7_dsp_map.v -D DSP_A_MAXWIDTH=25 -D DSP_B_MAXWIDTH=18 "
						"-D DSP_A_MAXWIDTH_PARTIAL=18 "	// Partial multipliers are intentionally
										// limited to 18x18 in order to take
										// advantage of the (PCOUT << 17) -> PCIN
										// dedicated cascade chain capability
						"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
						"-D DSP_Y_MINWIDTH=9 " // UG901 suggests small multiplies are those 4x4 and smaller
						"-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL25X18");
				else if (family == "xcu" || family == "xcup")
					run("techmap -map +/mul2dsp.v -map +/xilinx/xcu_dsp_map.v -D DSP_A_MAXWIDTH=27 -D DSP_B_MAXWIDTH=18 "
						"-D DSP_A_MAXWIDTH_PARTIAL=18 "	// Partial multipliers are intentionally
										// limited to 18x18 in order to take
										// advantage of the (PCOUT << 17) -> PCIN
										// dedicated cascade chain capability
						"-D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2 " // Blocks Nx1 multipliers
						"-D DSP_Y_MINWIDTH=9 " // UG901 suggests small multiplies are those 4x4 and smaller
						"-D DSP_SIGNEDONLY=1 -D DSP_NAME=$__MUL27X18");
				run("select a:mul2dsp");
				run("setattr -unset mul2dsp");
				run("opt_expr -fine");
				run("wreduce");
				run("select -clear");
				if (help_mode)
					run("xilinx_dsp -family <family>");
				else
					run("xilinx_dsp -family " + family);
				run("chtype -set $mul t:$__soft_mul");
			}
		}

		if (check_label("coarse")) {
			run("alumacc");
			run("share");
			run("opt");
			run("fsm");
			run("opt -fast");
			run("memory -nomap");
			run("opt_clean");
		}

		if (check_label("map_uram", "(only if '-uram')")) {
			if (help_mode) {
				run("memory_bram -rules +/xilinx/{family}_urams.txt");
				run("techmap -map +/xilinx/{family}_urams_map.v");
			} else if (uram) {
				if (family == "xcup") {
					run("memory_bram -rules +/xilinx/xcup_urams.txt");
					run("techmap -map +/xilinx/xcup_urams_map.v");
				} else {
					log_warning("UltraRAM inference not supported for family %s.\n", family.c_str());
				}
			}
		}

		if (check_label("map_bram", "(skip if '-nobram')")) {
			if (help_mode) {
				run("memory_bram -rules +/xilinx/{family}_brams.txt");
				run("techmap -map +/xilinx/{family}_brams_map.v");
			} else if (!nobram) {
				if (family == "xc2v" || family == "xc2vp" || family == "xc3s" || family == "xc3se") {
					run("memory_bram -rules +/xilinx/xc2v_brams.txt");
					run("techmap -map +/xilinx/xc2v_brams_map.v");
				} else if (family == "xc3sa") {
					// Superset of Virtex 2 primitives — uses common map file.
					run("memory_bram -rules +/xilinx/xc3sa_brams.txt");
					run("techmap -map +/xilinx/xc2v_brams_map.v");
				} else if (family == "xc3sda") {
					// Supported block RAMs for Spartan 3A DSP are
					// a subset of Spartan 6's ones.
					run("memory_bram -rules +/xilinx/xc3sda_brams.txt");
					run("techmap -map +/xilinx/xc6s_brams_map.v");
				} else if (family == "xc6s") {
					run("memory_bram -rules +/xilinx/xc6s_brams.txt");
					run("techmap -map +/xilinx/xc6s_brams_map.v");
				} else if (family == "xc6v" || family == "xc7") {
					run("memory_bram -rules +/xilinx/xc7_xcu_brams.txt");
					run("techmap -map +/xilinx/xc7_brams_map.v");
				} else if (family == "xcu" || family == "xcup") {
					run("memory_bram -rules +/xilinx/xc7_xcu_brams.txt");
					run("techmap -map +/xilinx/xcu_brams_map.v");					
				} else {
					log_warning("Block RAM inference not yet supported for family %s.\n", family.c_str());
				}
			}
		}

		if (check_label("map_lutram", "(skip if '-nolutram')")) {
			if (!nolutram || help_mode) {
				run("memory_bram -rules +/xilinx/lut" + lut_size_s + "_lutrams.txt");
				run("techmap -map +/xilinx/lutrams_map.v");
			}
		}

		if (check_label("map_ffram")) {
			// Required for dffsr2dff to work.
			run("simplemap t:$dff t:$adff t:$mux");
			// Needs to be done before opt -mux_bool happens.
			run("dffsr2dff");
			if (help_mode)
				run("dff2dffs [-match-init]", "(-match-init for xc6s only)");
			else if (family == "xc6s")
				run("dff2dffs -match-init");
			else
				run("dff2dffs");
			if (widemux > 0)
				run("opt -fast -mux_bool -undriven -fine"); // Necessary to omit -mux_undef otherwise muxcover
									    // performs less efficiently
			else
				run("opt -fast -full");
			run("memory_map");
		}

		if (check_label("fine")) {
			run("dff2dffe -direct-match $_DFF_* -direct-match $__DFFS_*");
			if (help_mode)
				run("muxcover <internal options> ('-widemux' only)");
			else if (widemux > 0) {
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

			std::string techmap_args = " -map +/techmap.v -D LUT_SIZE=" + lut_size_s;
			if (help_mode)
				techmap_args += " [-map +/xilinx/mux_map.v]";
			else if (widemux > 0)
				techmap_args += stringf(" -D MIN_MUX_INPUTS=%d -map +/xilinx/mux_map.v", widemux);
			if (!nocarry) {
				techmap_args += " -map +/xilinx/arith_map.v";
				if (vpr)
					techmap_args += " -D _EXPLICIT_CARRY";
			}
			run("techmap " + techmap_args);
			run("opt -fast");
		}

		if (check_label("map_cells")) {
			// Needs to be done before logic optimization, so that inverters (OE vs T) are handled.
			if (help_mode || !noiopad)
				run("iopadmap -bits -outpad OBUF I:O -inpad IBUF O:I -toutpad $__XILINX_TOUTPAD OE:I:O -tinoutpad $__XILINX_TINOUTPAD OE:O:I:IO A:top", "(skip if '-noiopad')");
			std::string techmap_args = "-map +/techmap.v -map +/xilinx/cells_map.v";
			if (widemux > 0)
				techmap_args += stringf(" -D MIN_MUX_INPUTS=%d", widemux);
			run("techmap " + techmap_args);
			run("clean");
		}

		if (check_label("map_ffs")) {
			if (abc9 || help_mode) {
				run("techmap -map " + ff_map_file, "('-abc9' only)");
			}
		}

		if (check_label("map_luts")) {
			run("opt_expr -mux_undef");
			if (flatten_before_abc)
				run("flatten");
			if (help_mode)
				run("abc -luts 2:2,3,6:5[,10,20] [-dff] [-D 1]", "(option for 'nowidelut', '-dff', '-retime')");
			else if (abc9) {
				if (lut_size != 6)
					log_error("'synth_xilinx -abc9' not currently supported for LUT4-based devices.\n");
				if (family != "xc7")
					log_warning("'synth_xilinx -abc9' not currently supported for the '%s' family, "
							"will use timing for 'xc7' instead.\n", family.c_str());
				std::string techmap_args = "-map +/xilinx/abc9_map.v -max_iter 1";
				if (dff_mode)
					techmap_args += " -D DFF_MODE";
				run("techmap " + techmap_args);
				run("read_verilog -icells -lib -specify +/abc9_model.v +/xilinx/abc9_model.v");
				std::string abc9_opts;
				auto k = stringf("synth_xilinx.abc9.%s.W", family.c_str());
				if (active_design->scratchpad.count(k))
					abc9_opts += stringf(" -W %s", active_design->scratchpad_get_string(k).c_str());
				else
					abc9_opts += stringf(" -W %s", RTLIL::constpad.at(k, RTLIL::constpad.at("synth_xilinx.abc9.xc7.W")).c_str());
				if (nowidelut)
					abc9_opts += stringf(" -maxlut %d", lut_size);
				if (dff_mode)
					abc9_opts += " -dff";
				run("abc9" + abc9_opts);
				run("techmap -map +/xilinx/abc9_unmap.v");
			}
			else {
				std::string abc_opts;
				if (lut_size != 6) {
					if (nowidelut)
						abc_opts += " -lut " + lut_size_s;
					else
						abc_opts += " -lut " + lut_size_s + ":" + std::to_string(widelut_size);
				} else {
					if (nowidelut)
						abc_opts += " -luts 2:2,3,6:5";
					else if (widelut_size == 8)
						abc_opts += " -luts 2:2,3,6:5,10,20";
					else
						abc_opts += " -luts 2:2,3,6:5,10,20,40";
				}
				if (dff_mode)
					abc_opts += " -dff";
				if (retime)
					abc_opts += " -D 1";
				run("abc" + abc_opts);
			}
			run("clean");

			// This shregmap call infers fixed length shift registers after abc
			//   has performed any necessary retiming
			if (!nosrl || help_mode)
				run("xilinx_srl -fixed -minlen 3", "(skip if '-nosrl')");
			std::string techmap_args = "-map +/xilinx/lut_map.v -map +/xilinx/cells_map.v";
			if (help_mode || !abc9)
				techmap_args += stringf(" -map %s", ff_map_file.c_str());
			techmap_args += " -D LUT_WIDTH=" + lut_size_s;
			run("techmap " + techmap_args);
			if (help_mode)
				run("xilinx_dffopt [-lut4]");
			else if (lut_size == 4)
				run("xilinx_dffopt -lut4");
			else
				run("xilinx_dffopt");
			run("opt_lut_ins -tech xilinx");
		}

		if (check_label("finalize")) {
			if (help_mode || !noclkbuf)
				run("clkbufmap -buf BUFG O:I", "(skip if '-noclkbuf')");
			if (help_mode || ise)
				run("extractinv -inv INV O:I", "(only if '-ise')");
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
