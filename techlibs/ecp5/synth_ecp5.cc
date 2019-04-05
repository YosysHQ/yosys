/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012 Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2018 Clifford Wolf <dave@ds0.me>
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
		log("        run 'abc' with -dff option\n");
		log("\n");
		log("    -noccu2\n");
		log("        do not use CCU2 cells in output netlist\n");
		log("\n");
		log("    -nodffe\n");
		log("        do not use flipflops with CE in output netlist\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use BRAM cells in output netlist\n");
		log("\n");
		log("    -nodram\n");
		log("        do not use distributed RAM cells in output netlist\n");
		log("\n");
		log("    -nomux\n");
		log("        do not use PFU muxes to implement LUTs larger than LUT4s\n");
		log("\n");
		log("    -abc2\n");
		log("        run two passes of 'abc' for slightly improved logic density\n");
		log("\n");
		log("    -vpr\n");
		log("        generate an output netlist (and BLIF file) suitable for VPR\n");
		log("        (this feature is experimental and incomplete)\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, blif_file, edif_file, json_file;
	bool noccu2, nodffe, nobram, nodram, nomux, flatten, retime, abc2, vpr;

	void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
		blif_file = "";
		edif_file = "";
		json_file = "";
		noccu2 = false;
		nodffe = false;
		nobram = false;
		nodram = false;
		nomux = false;
		flatten = true;
		retime = false;
		abc2 = false;
		vpr = false;
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
			if (args[argidx] == "-nodram") {
				nodram = true;
				continue;
			}
			if (args[argidx] == "-nomux") {
				nomux = true;
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
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH_ECP5 pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib +/ecp5/cells_sim.v +/ecp5/cells_bb.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (flatten && check_label("flatten", "(unless -noflatten)"))
		{
			run("proc");
			run("flatten");
			run("tribuf -logic");
			run("deminout");
		}

		if (check_label("coarse"))
		{
			run("synth -run coarse");
		}

		if (!nobram && check_label("bram", "(skip if -nobram)"))
		{
			run("memory_bram -rules +/ecp5/bram.txt");
			run("techmap -map +/ecp5/brams_map.v");
		}

		if (!nodram && check_label("dram", "(skip if -nodram)"))
		{
			run("memory_bram -rules +/ecp5/dram.txt");
			run("techmap -map +/ecp5/drams_map.v");
		}

		if (check_label("fine"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
			if (noccu2)
				run("techmap");
			else
				run("techmap -map +/techmap.v -map +/ecp5/arith_map.v");
			if (retime || help_mode)
				run("abc -dff", "(only if -retime)");
		}

		if (check_label("map_ffs"))
		{
			run("dffsr2dff");
			run("dff2dffs");
			run("opt_clean");
			if (!nodffe)
				run("dff2dffe -direct-match $_DFF_* -direct-match $__DFFS_*");
			run("techmap -D NO_LUT -map +/ecp5/cells_map.v");
			run("opt_expr -mux_undef");
			run("simplemap");
			run("ecp5_ffinit");
		}

		if (check_label("map_luts"))
		{
			if (abc2 || help_mode) {
				run("abc", "      (only if -abc2)");
			}
			run("techmap -map +/ecp5/latches_map.v");
			if (nomux)
				run("abc -lut 4 -dress");
			else
				run("abc -lut 4:7 -dress");
			run("clean");
		}

		if (check_label("map_cells"))
		{
			if (vpr)
				run("techmap -D NO_LUT -map +/ecp5/cells_map.v");
			else
				run("techmap -map +/ecp5/cells_map.v", "(with -D NO_LUT in vpr mode)");

			run("clean");
		}

		if (check_label("check"))
		{
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
