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

struct SynthEasicPass : public ScriptPass
{
	SynthEasicPass() : ScriptPass("synth_easic", "synthesis for eASIC platform") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_easic [options]\n");
		log("\n");
		log("This command runs synthesis for eASIC platform.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -vlog <file>\n");
		log("        write the design to the specified structural Verilog file. writing of\n");
		log("        an output file is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -etools <path>\n");
		log("        set path to the eTools installation. (default=/opt/eTools)\n");
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

	string top_opt, vlog_file, etools_path;
	bool flatten, retime;

	void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
		vlog_file = "";
		etools_path = "/opt/eTools";
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
			if (args[argidx] == "-vlog" && argidx+1 < args.size()) {
				vlog_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-etools" && argidx+1 < args.size()) {
				etools_path = args[++argidx];
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

		log_header(design, "Executing SYNTH_EASIC pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
	{
		string phys_clk_lib = stringf("%s/data_ruby28/design_libs/logical/timing/gp/n3x_phys_clk_0v893ff125c.lib", etools_path.c_str());
		string logic_lut_lib = stringf("%s/data_ruby28/design_libs/logical/timing/gp/n3x_logic_lut_0v893ff125c.lib", etools_path.c_str());

		if (check_label("begin"))
		{
			run(stringf("read_liberty -lib %s", help_mode ? "<etools_phys_clk_lib>" : phys_clk_lib.c_str()));
			run(stringf("read_liberty -lib %s", help_mode ? "<etools_logic_lut_lib>" : logic_lut_lib.c_str()));
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (flatten && check_label("flatten", "(unless -noflatten)"))
		{
			run("proc");
			run("flatten");
		}

		if (check_label("coarse"))
		{
			run("synth -run coarse");
		}

		if (check_label("fine"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
			run("techmap");
			run("opt -fast");
			if (retime || help_mode) {
				run("abc -dff -D 1", " (only if -retime)");
				run("opt_clean", "(only if -retime)");
			}
		}

		if (check_label("map"))
		{
			run(stringf("dfflibmap -liberty %s", help_mode ? "<etools_phys_clk_lib>" : phys_clk_lib.c_str()));
			run(stringf("abc -liberty %s", help_mode ? "<etools_logic_lut_lib>" : logic_lut_lib.c_str()));
			run("opt_clean");
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
		}

		if (check_label("vlog"))
		{
			if (!vlog_file.empty() || help_mode)
				run(stringf("write_verilog -noexpr -attr2comment %s", help_mode ? "<file-name>" : vlog_file.c_str()));
		}
	}
} SynthEasicPass;

PRIVATE_NAMESPACE_END
