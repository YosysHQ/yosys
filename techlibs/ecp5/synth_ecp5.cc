/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012 Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018 gatecat <gatecat@ds0.me>
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

struct SynthEcp5Pass : public ScriptPass
{
	SynthEcp5Pass() : ScriptPass("synth_ecp5", "synthesis for ECP5 FPGAs") { }

	void on_register() override
	{
		RTLIL::constpad["synth_ecp5.abc9.W"] = "300";
	}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_ecp5 [options]\n");
		log("\n");
		log("This command runs synthesis for ECP5 FPGAs.\n");
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
		log("    -dff\n");
		log("        run 'abc'/'abc9' with -dff option\n");
		log("\n");
		log("    -retime\n");
		log("        run 'abc' with '-dff -D 1' options\n");
		log("\n");
		log("    -noccu2\n");
		log("        do not use CCU2 cells in output netlist\n");
		log("\n");
		log("    -nodffe\n");
		log("        do not use flipflops with CE in output netlist\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nolutram\n");
		log("        do not use LUT RAM cells in output netlist\n");
		log("\n");
		log("    -nowidelut\n");
		log("        do not use PFU muxes to implement LUTs larger than LUT4s\n");
		log("\n");
		log("    -asyncprld\n");
		log("        use async PRLD mode to implement ALDFF (EXPERIMENTAL)\n");
		log("\n");
		log("    -abc2\n");
		log("        run two passes of 'abc' for slightly improved logic density\n");
		log("\n");
		log("    -noabc9\n");
		log("        disable use of new ABC9 flow\n");
		log("\n");
		log("    -vpr\n");
		log("        generate an output netlist (and BLIF file) suitable for VPR\n");
		log("        (this feature is experimental and incomplete)\n");
		log("\n");
		log("    -iopad\n");
		log("        insert IO buffers\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not map multipliers to MULT18X18D\n");
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

	string top_opt, blif_file, edif_file, json_file;
	bool noccu2, nodffe, nobram, nolutram, nowidelut, asyncprld, flatten, dff, retime, abc2, abc9, iopad, nodsp, vpr, no_rw_check;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		blif_file = "";
		edif_file = "";
		json_file = "";
		noccu2 = false;
		nodffe = false;
		nobram = false;
		nolutram = false;
		nowidelut = false;
		asyncprld = false;
		flatten = true;
		dff = false;
		retime = false;
		abc2 = false;
		vpr = false;
		abc9 = true;
		iopad = false;
		nodsp = false;
		no_rw_check = false;
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
			if (args[argidx] == "-dff") {
				dff = true;
				continue;
			}
			if (args[argidx] == "-retime") {
				retime = true;
				continue;
			}
			if (args[argidx] == "-noccu2") {
				noccu2 = true;
				continue;
			}
			if (args[argidx] == "-nodffe") {
				nodffe = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-asyncprld") {
				asyncprld = true;
				continue;
			}
			if (args[argidx] == "-nolutram" || /*deprecated alias*/ args[argidx] == "-nodram") {
				nolutram = true;
				continue;
			}
			if (args[argidx] == "-nowidelut" || /*deprecated alias*/ args[argidx] == "-nomux") {
				nowidelut = true;
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
				// removed, ABC9 is on by default.
				continue;
			}
			if (args[argidx] == "-noabc9") {
				abc9 = false;
				continue;
			}
			if (args[argidx] == "-iopad") {
				iopad = true;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
				continue;
			}
			if (args[argidx] == "-no-rw-check") {
				no_rw_check = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (abc9 && retime)
				log_cmd_error("-retime option not currently compatible with -abc9!\n");

		log_header(design, "Executing SYNTH_ECP5 pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		std::string no_rw_check_opt = "";
		if (no_rw_check)
			no_rw_check_opt = " -no-rw-check";
		if (help_mode)
			no_rw_check_opt = " [-no-rw-check]";

		if (check_label("begin"))
		{
			run("read_verilog -lib -specify +/ecp5/cells_sim.v +/ecp5/cells_bb.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (check_label("coarse"))
		{
			run("proc");
			if (flatten || help_mode)
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
			if (!nodsp) {
				run("techmap -map +/mul2dsp.v -map +/ecp5/dsp_map.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18  -D DSP_A_MINWIDTH=2 -D DSP_B_MINWIDTH=2  -D DSP_NAME=$__MUL18X18", "(unless -nodsp)");
				run("chtype -set $mul t:$__soft_mul", "(unless -nodsp)");
			}
			run("alumacc");
			run("opt");
			run("memory -nomap" + no_rw_check_opt);
			run("opt_clean");
		}

		if (check_label("map_ram"))
		{
			std::string args = "";
			if (nobram)
				args += " -no-auto-block";
			if (nolutram)
				args += " -no-auto-distributed";
			if (help_mode)
				args += " [-no-auto-block] [-no-auto-distributed]";
			run("memory_libmap -lib +/ecp5/lutrams.txt -lib +/ecp5/brams.txt" + args, "(-no-auto-block if -nobram, -no-auto-distributed if -nolutram)");
			run("techmap -map +/ecp5/lutrams_map.v -map +/ecp5/brams_map.v");
		}

		if (check_label("map_ffram"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates"))
		{
			if (noccu2)
				run("techmap");
			else
				run("techmap -map +/techmap.v -map +/ecp5/arith_map.v");
			if (help_mode || iopad) {
				run("iopadmap -bits -outpad OB I:O -inpad IB O:I -toutpad OBZ ~T:I:O -tinoutpad BB ~T:O:I:B A:top", "(only if '-iopad')");
				run("attrmvcp -attr src -attr LOC t:OB %x:+[O] t:OBZ %x:+[O] t:BB %x:+[B]");
				run("attrmvcp -attr src -attr LOC -driven t:IB %x:+[I]");
			}
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
		}

		if (check_label("map_ffs"))
		{
			run("opt_clean");
			std::string dfflegalize_args = " -cell $_DFF_?_ 01 -cell $_DFF_?P?_ r -cell $_SDFF_?P?_ r";
			if (help_mode) {
				dfflegalize_args += " [-cell $_DFFE_??_ 01 -cell $_DFFE_?P??_ r -cell $_SDFFE_?P??_ r]";
			} else if (!nodffe) {
				dfflegalize_args += " -cell $_DFFE_??_ 01 -cell $_DFFE_?P??_ r -cell $_SDFFE_?P??_ r";
			}
			if (help_mode) {
				dfflegalize_args += " [-cell $_ALDFF_?P_ x -cell $_ALDFFE_?P?_ x] [-cell $_DLATCH_?_ x]";
			} else if (asyncprld) {
				dfflegalize_args += " -cell $_ALDFF_?P_ x -cell $_ALDFFE_?P?_ x";
			} else {
				dfflegalize_args += " -cell $_DLATCH_?_ x";
			}
			run("dfflegalize" + dfflegalize_args, "($_ALDFF_*_ only if -asyncprld, $_DLATCH_* only if not -asyncprld, $_*DFFE_* only if not -nodffe)");
			if ((abc9 && dff) || help_mode)
				run("zinit -all w:* t:$_DFF_?_ t:$_DFFE_??_ t:$_SDFF*", "(only if -abc9 and -dff)");
			run("techmap -D NO_LUT -map +/ecp5/cells_map.v");
			run("opt_expr -undriven -mux_undef");
			run("simplemap");
			run("lattice_gsr");
			run("attrmvcp -copy -attr syn_useioff");
			run("opt_clean");
		}

		if (check_label("map_luts"))
		{
			if (abc2 || help_mode)
				run("abc", "      (only if -abc2)");
			if (!asyncprld || help_mode)
				run("techmap -map +/ecp5/latches_map.v", "(skip if -asyncprld)");

			if (abc9) {
				std::string abc9_opts;
				if (nowidelut)
					abc9_opts += " -maxlut 4";
				std::string k = "synth_ecp5.abc9.W";
				if (active_design && active_design->scratchpad.count(k))
					abc9_opts += stringf(" -W %s", active_design->scratchpad_get_string(k).c_str());
				else
					abc9_opts += stringf(" -W %s", RTLIL::constpad.at(k).c_str());
				if (nowidelut)
					abc9_opts += " -maxlut 4";
				if (dff)
					abc9_opts += " -dff";
				run("abc9" + abc9_opts);
			} else {
				std::string abc_args = " -dress";
				if (nowidelut)
					abc_args += " -lut 4";
				else
					abc_args += " -lut 4:7";
				if (dff)
					abc_args += " -dff";
				run("abc" + abc_args);
			}
			run("clean");
		}

		if (check_label("map_cells"))
		{
			if (help_mode)
				run("techmap -map +/ecp5/cells_map.v", "(skip if -vpr)");
			else if (!vpr)
				run("techmap -map +/ecp5/cells_map.v");
			run("opt_lut_ins -tech lattice");
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
} SynthEcp5Pass;

PRIVATE_NAMESPACE_END
