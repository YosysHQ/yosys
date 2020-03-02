/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2017 Robert Ou <rqou@robertou.com>
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

struct SynthCoolrunner2Pass : public ScriptPass
{
	SynthCoolrunner2Pass() : ScriptPass("synth_coolrunner2", "synthesis for Xilinx Coolrunner-II CPLDs") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_coolrunner2 [options]\n");
		log("\n");
		log("This command runs synthesis for Coolrunner-II CPLDs. This work is experimental.\n");
		log("It is intended to be used with https://github.com/azonenberg/openfpga as the\n");
		log("place-and-route.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
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

	string top_opt, json_file;
	bool flatten, retime;

	void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
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

		log_header(design, "Executing SYNTH_COOLRUNNER2 pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib +/coolrunner2/cells_sim.v");
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
			run("extract_counter -dir up -allow_arst no");
			run("techmap -map +/coolrunner2/cells_counter_map.v");
			run("clean");
			run("opt -fast -full");
			run("techmap -map +/techmap.v -map +/coolrunner2/cells_latch.v");
			run("opt -fast");
			run("dfflibmap -prepare -liberty +/coolrunner2/xc2_dff.lib");
		}

		if (check_label("map_tff"))
		{
			// This is quite hacky. By telling abc that it can only use AND and XOR gates, abc will try and use XOR
			// gates "whenever possible." This will hopefully cause toggle flip-flop structures to turn into an XOR
			// connected to a D flip-flop. We then match on these and convert them into XC2 TFF cells.
			run("abc -g AND,XOR");
			run("clean");
			run("extract -map +/coolrunner2/tff_extract.v");
		}

		if (check_label("map_pla"))
		{
			run("abc -sop -I 40 -P 56" + string(retime ? " -dff -D 1" : ""));
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("dfflibmap -liberty +/coolrunner2/xc2_dff.lib");
			run("dffinit -ff FDCP Q INIT");
			run("dffinit -ff FDCP_N Q INIT");
			run("dffinit -ff FTCP Q INIT");
			run("dffinit -ff FTCP_N Q INIT");
			run("dffinit -ff LDCP Q INIT");
			run("dffinit -ff LDCP_N Q INIT");
			run("coolrunner2_sop");
			run("clean");
			run("iopadmap -bits -inpad IBUF O:I -outpad IOBUFE I:IO -inoutpad IOBUFE O:IO -toutpad IOBUFE E:I:IO -tinoutpad IOBUFE E:O:I:IO");
			run("attrmvcp -attr src -attr LOC t:IOBUFE n:*");
			run("attrmvcp -attr src -attr LOC -driven t:IBUF n:*");
			run("coolrunner2_fixup");
			run("splitnets");
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
} SynthCoolrunner2Pass;

PRIVATE_NAMESPACE_END
