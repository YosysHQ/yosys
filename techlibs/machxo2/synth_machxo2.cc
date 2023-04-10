/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020 William D. Jones <wjones@wdj-consulting.com>
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

struct SynthMachXO2Pass : public ScriptPass
{
	SynthMachXO2Pass() : ScriptPass("synth_machxo2", "synthesis for MachXO2 FPGAs. This work is experimental.") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_machxo2 [options]\n");
		log("\n");
		log("This command runs synthesis for MachXO2 FPGAs.\n");
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
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nolutram\n");
		log("        do not use LUT RAM cells in output netlist\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis\n");
		log("\n");
		log("    -noiopad\n");
		log("        do not insert IO buffers\n");
		log("\n");
		log("    -ccu2\n");
		log("        use CCU2 cells in output netlist\n");
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
	bool ccu2, nobram, nolutram, flatten, vpr, noiopad;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		blif_file = "";
		edif_file = "";
		json_file = "";
		ccu2 = false;
		nobram = false;
		nolutram = false;
		flatten = true;
		vpr = false;
		noiopad = false;
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
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-nolutram") {
				nolutram = true;
				continue;
			}
			if (args[argidx] == "-noiopad") {
				noiopad = true;
				continue;
			}
			if (args[argidx] == "-ccu2") {
				ccu2 = true;
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

		log_header(design, "Executing SYNTH_MACHXO2 pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib -icells +/machxo2/cells_sim.v +/machxo2/cells_bb.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (check_label("flatten", "(unless -noflatten)"))
		{
			if (flatten || help_mode) {
				run("proc");
				run("flatten");
				run("tribuf -logic");
				run("deminout");
			}
		}

		if (check_label("coarse"))
		{
			run("synth -run coarse");
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
			run("memory_libmap -lib +/machxo2/lutrams.txt -lib +/machxo2/brams.txt" + args, "(-no-auto-block if -nobram, -no-auto-distributed if -nolutram)");
			run("techmap -map +/machxo2/lutrams_map.v -map +/machxo2/brams_map.v");
		}

		if (check_label("fine"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates", "(unless -noiopad)"))
		{
			if (!ccu2)
				run("techmap");
			else
				run("techmap -map +/techmap.v -map +/machxo2/arith_map.v");
			if (!noiopad || help_mode)
			{
				run("iopadmap -bits -outpad OB I:O -inpad IB O:I -toutpad OBZ ~T:I:O -tinoutpad BB ~T:O:I:B A:top", "(only if '-iopad')");
				run("attrmvcp -attr src -attr LOC t:OB %x:+[O] t:OBZ %x:+[O] t:BB %x:+[B]");
				run("attrmvcp -attr src -attr LOC -driven t:IB %x:+[I]");
			}
		}

		if (check_label("map_ffs"))
		{
			run("opt_clean");
			std::string dfflegalize_args = " -cell $_DFF_?_ 01 -cell $_DFF_?P?_ r -cell $_SDFF_?P?_ r";
			run("dfflegalize" + dfflegalize_args);
			run("techmap -D NO_LUT -map +/machxo2/cells_map.v");
			run("opt_expr -undriven -mux_undef");
			run("simplemap");
			run("ecp5_gsr");
			run("attrmvcp -copy -attr syn_useioff");
			run("opt_clean");
		}

		if (check_label("map_luts"))
		{
			run("abc -lut 4 -dress");
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("techmap -map +/machxo2/cells_map.v");
			run("clean");
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat");
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
} SynthMachXO2Pass;

PRIVATE_NAMESPACE_END
