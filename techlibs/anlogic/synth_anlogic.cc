/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018  Miodrag Milanovic <micko@yosyshq.com>
 *  Copyright (C) 2018  Claire Xenia Wolf <claire@yosyshq.com>
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

struct SynthAnlogicPass : public ScriptPass
{
	SynthAnlogicPass() : ScriptPass("synth_anlogic", "synthesis for Anlogic FPGAs") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_anlogic [options]\n");
		log("\n");
		log("This command runs synthesis for Anlogic FPGAs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
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
		log("    -nolutram\n");
		log("        do not use EG_LOGIC_DRAM16X4 cells in output netlist\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use EG_PHY_BRAM or EG_PHY_BRAM32K cells in output netlist\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, edif_file, json_file;
	bool flatten, retime, nolutram, nobram;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		edif_file = "";
		json_file = "";
		flatten = true;
		retime = false;
		nolutram = false;
		nobram = false;
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
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-nolutram") {
				nolutram = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-retime") {
				retime = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH_ANLOGIC pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib +/anlogic/cells_sim.v +/anlogic/eagle_bb.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt));
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

		if (check_label("map_ram"))
		{
			std::string args = "";
			if (help_mode)
				args += " [-no-auto-block] [-no-auto-distributed]";
			else {
				if (nobram)
					args += " -no-auto-block";
				if (nolutram)
					args += " -no-auto-distributed";
			}
			run("memory_libmap -lib +/anlogic/lutrams.txt -lib +/anlogic/brams.txt" + args, "(-no-auto-block if -nobram, -no-auto-distributed if -nolutram)");
			run("techmap -map +/anlogic/lutrams_map.v -map +/anlogic/brams_map.v");
		}

		if (check_label("map_ffram"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates"))
		{
			run("techmap -map +/techmap.v -map +/anlogic/arith_map.v");
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
		}

		if (check_label("map_ffs"))
		{
			run("dfflegalize -cell $_DFFE_P??P_ r -cell $_SDFFE_P??P_ r -cell $_DLATCH_N??_ r");
			run("techmap -D NO_LUT -map +/anlogic/cells_map.v");
			run("opt_expr -mux_undef");
			run("simplemap");
		}

		if (check_label("map_luts"))
		{
			run("abc -lut 4:6");
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("techmap -map +/anlogic/cells_map.v");
			run("clean");
		}

		if (check_label("map_anlogic"))
		{
			run("anlogic_fixcarry");
			run("anlogic_eqn");
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
			run("blackbox =A:whitebox");
		}

		if (check_label("edif"))
		{
			if (!edif_file.empty() || help_mode)
				run(stringf("write_edif %s", help_mode ? "<file-name>" : edif_file));
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file));
		}
	}
} SynthAnlogicPass;

PRIVATE_NAMESPACE_END
