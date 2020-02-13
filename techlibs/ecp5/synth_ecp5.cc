/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012 Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2018 David Shah <dave@ds0.me>
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

	void help() YS_OVERRIDE
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
		log("        use async PRLD mode to implement DLATCH and DFFSR (EXPERIMENTAL)\n");
		log("\n");
		log("    -abc2\n");
		log("        run two passes of 'abc' for slightly improved logic density\n");
		log("\n");
		log("    -abc9\n");
		log("        use new ABC9 flow (EXPERIMENTAL)\n");
		log("\n");
		log("    -vpr\n");
		log("        generate an output netlist (and BLIF file) suitable for VPR\n");
		log("        (this feature is experimental and incomplete)\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not map multipliers to MULT18X18D\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, blif_file, edif_file, json_file;
	bool noccu2, nodffe, nobram, nolutram, nowidelut, asyncprld, flatten, retime, abc2, abc9, nodsp, vpr;

	void clear_flags() YS_OVERRIDE
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
		retime = false;
		abc2 = false;
		vpr = false;
		abc9 = false;
		nodsp = false;
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
				abc9 = true;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
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

	void script() YS_OVERRIDE
	{
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
			run("fsm");
			run("opt -fast");
			run("memory -nomap");
			run("opt_clean");
		}

		if (!nobram && check_label("map_bram", "(skip if -nobram)"))
		{
			run("memory_bram -rules +/ecp5/brams.txt");
			run("techmap -map +/ecp5/brams_map.v");
		}

		if (!nolutram && check_label("map_lutram", "(skip if -nolutram)"))
		{
			run("memory_bram -rules +/ecp5/lutrams.txt");
			run("techmap -map +/ecp5/lutrams_map.v");
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
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
		}

		if (check_label("map_ffs"))
		{
			run("dffsr2dff");
			run("dff2dffs");
			run("opt_clean");
			if (!nodffe)
				run("dff2dffe -direct-match $_DFF_* -direct-match $__DFFS_*");
			run(stringf("techmap -D NO_LUT %s -map +/ecp5/cells_map.v", help_mode ? "[-D ASYNC_PRLD]" : (asyncprld ? "-D ASYNC_PRLD" : "")));
			run("opt_expr -undriven -mux_undef");
			run("simplemap");
			run("ecp5_ffinit");
			run("ecp5_gsr");
			run("attrmvcp -copy -attr syn_useioff");
			run("opt_clean");
		}

		if (check_label("map_luts"))
		{
			if (abc2 || help_mode) {
				run("abc", "      (only if -abc2)");
			}
			std::string techmap_args = asyncprld ? "" : "-map +/ecp5/latches_map.v";
			if (abc9)
				techmap_args += " -map +/ecp5/abc9_map.v -max_iter 1";
			if (!asyncprld || abc9)
				run("techmap " + techmap_args);

			if (abc9) {
				run("read_verilog -icells -lib -specify +/abc9_model.v +/ecp5/abc9_model.v");
				if (nowidelut)
					run("abc9 -maxlut 4 -W 200");
				else
					run("abc9 -W 200");
				run("techmap -map +/ecp5/abc9_unmap.v");
			} else {
				if (nowidelut)
					run("abc -lut 4 -dress");
				else
					run("abc -lut 4:7 -dress");
			}
			run("clean");
		}

		if (check_label("map_cells"))
		{
			if (vpr)
				run("techmap -D NO_LUT -map +/ecp5/cells_map.v");
			else
				run("techmap -map +/ecp5/cells_map.v", "(with -D NO_LUT in vpr mode)");

			run("opt_lut_ins -tech ecp5");
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
} SynthEcp5Pass;

PRIVATE_NAMESPACE_END
