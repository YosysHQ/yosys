/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

struct SynthGreenPAK4Pass : public ScriptPass
{
	SynthGreenPAK4Pass() : ScriptPass("synth_greenpak4", "synthesis for GreenPAK4 FPGAs") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_greenpak4 [options]\n");
		log("\n");
		log("This command runs synthesis for GreenPAK4 FPGAs. This work is experimental.\n");
		log("It is intended to be used with https://github.com/azonenberg/openfpga as the\n");
		log("place-and-route.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -part <part>\n");
		log("        synthesize for the specified part. Valid values are SLG46140V,\n");
		log("        SLG46620V, and SLG46621V (default).\n");
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
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, part, json_file;
	bool flatten, retime;

	void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
		part = "SLG46621V";
		json_file = "";
		flatten = true;
		retime = false;
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
			if (args[argidx] == "-json" && argidx+1 < args.size()) {
				json_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-part" && argidx+1 < args.size()) {
				part = args[++argidx];
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
			if (args[argidx] == "-retime") {
				retime = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (part != "SLG46140V" && part != "SLG46620V" && part != "SLG46621V")
			log_cmd_error("Invalid part name: '%s'\n", part.c_str());

		log_header(design, "Executing SYNTH_GREENPAK4 pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib +/greenpak4/cells_sim.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (flatten && check_label("flatten", "(unless -noflatten)"))
		{
			run("proc");
			run("flatten");
			run("tribuf -logic");
		}

		if (check_label("coarse"))
		{
			run("synth -run coarse");
		}

		if (check_label("fine"))
		{
			run("extract_counter -pout GP_DCMP,GP_DAC -maxwidth 14");
			run("clean");
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
			run("techmap -map +/techmap.v -map +/greenpak4/cells_latch.v");
			run("dfflibmap -prepare -liberty +/greenpak4/gp_dff.lib");
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
		}

		if (check_label("map_luts"))
		{
			if (help_mode || part == "SLG46140V") run("nlutmap -assert -luts 0,6,8,2", " (for -part SLG46140V)");
			if (help_mode || part == "SLG46620V") run("nlutmap -assert -luts 2,8,16,2", "(for -part SLG46620V)");
			if (help_mode || part == "SLG46621V") run("nlutmap -assert -luts 2,8,16,2", "(for -part SLG46621V)");
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("shregmap -tech greenpak4");
			run("dfflibmap -liberty +/greenpak4/gp_dff.lib");
			run("dffinit -ff GP_DFF Q INIT");
			run("dffinit -ff GP_DFFR Q INIT");
			run("dffinit -ff GP_DFFS Q INIT");
			run("dffinit -ff GP_DFFSR Q INIT");
			run("iopadmap -bits -inpad GP_IBUF OUT:IN -outpad GP_OBUF IN:OUT -inoutpad GP_OBUF OUT:IN -toutpad GP_OBUFT OE:IN:OUT -tinoutpad GP_IOBUF OE:OUT:IN:IO");
			run("attrmvcp -attr src -attr LOC t:GP_OBUF t:GP_OBUFT t:GP_IOBUF n:*");
			run("attrmvcp -attr src -attr LOC -driven t:GP_IBUF n:*");
			run("techmap -map +/greenpak4/cells_map.v");
			run("greenpak4_dffinv");
			run("clean");
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file.c_str()));
		}
	}
} SynthGreenPAK4Pass;

PRIVATE_NAMESPACE_END
