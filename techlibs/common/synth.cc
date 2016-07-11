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

struct SynthPass : public ScriptPass
{
	SynthPass() : ScriptPass("synth", "generic synthesis script") { }

	virtual void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth [options]\n");
		log("\n");
		log("This command runs the default synthesis script. This command does not operate\n");
		log("on partly selected designs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -auto-top\n");
		log("        automatically determine the top of the design hierarchy\n");
		log("\n");
		log("    -flatten\n");
		log("        flatten the design before synthesis. this will pass '-auto-top' to\n");
		log("        'hierarchy' if no top module is specified.\n");
		log("\n");
		log("    -encfile <file>\n");
		log("        passed to 'fsm_recode' via 'fsm'\n");
		log("\n");
		log("    -nofsm\n");
		log("        do not run FSM optimization\n");
		log("\n");
		log("    -noabc\n");
		log("        do not run abc (as if yosys was compiled without ABC support)\n");
		log("\n");
		log("    -noalumacc\n");
		log("        do not run 'alumacc' pass. i.e. keep arithmetic operators in\n");
		log("        their direct form ($add, $sub, etc.).\n");
		log("\n");
		log("    -nordff\n");
		log("        passed to 'memory'. prohibits merging of FFs into memory read ports\n");
		log("\n");
		log("    -run <from_label>[:<to_label>]\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_module, fsm_opts, memory_opts;
	bool autotop, flatten, noalumacc, nofsm, noabc;

	virtual void clear_flags() YS_OVERRIDE
	{
		top_module.clear();
		fsm_opts.clear();
		memory_opts.clear();

		autotop = false;
		flatten = false;
		noalumacc = false;
		nofsm = false;
		noabc = false;
	}

	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module = args[++argidx];
				continue;
			}
			if (args[argidx] == "-encfile" && argidx+1 < args.size()) {
				fsm_opts = " -encfile " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos) {
					run_from = args[++argidx];
					run_to = args[argidx];
				} else {
					run_from = args[++argidx].substr(0, pos);
					run_to = args[argidx].substr(pos+1);
				}
				continue;
			}
			if (args[argidx] == "-auto-top") {
				autotop = true;
				continue;
			}
			if (args[argidx] == "-flatten") {
				flatten = true;
				continue;
			}
			if (args[argidx] == "-nofsm") {
				nofsm = true;
				continue;
			}
			if (args[argidx] == "-noabc") {
				noabc = true;
				continue;
			}
			if (args[argidx] == "-noalumacc") {
				noalumacc = true;
				continue;
			}
			if (args[argidx] == "-nordff") {
				memory_opts += " -nordff";
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This comannd only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	virtual void script() YS_OVERRIDE
	{
		if (check_label("begin"))
		{
			if (help_mode) {
				run("hierarchy -check [-top <top> | -auto-top]");
			} else {
				if (top_module.empty()) {
					if (flatten || autotop)
						run("hierarchy -check -auto-top");
					else
						run("hierarchy -check");
				} else
					run(stringf("hierarchy -check -top %s", top_module.c_str()));
			}
		}

		if (check_label("coarse"))
		{
			run("proc");
			if (help_mode || flatten)
				run("flatten", "(if -flatten)");
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt");
			run("wreduce");
			if (!noalumacc)
				run("alumacc");
			run("share");
			run("opt");
			if (!nofsm)
				run("fsm" + fsm_opts);
			run("opt -fast");
			run("memory -nomap" + memory_opts);
			run("opt_clean");
		}

		if (check_label("fine"))
		{
			run("opt -fast -full");
			run("memory_map");
			run("opt -full");
			run("techmap");
			run("opt -fast");

			if (!noabc) {
		#ifdef YOSYS_ENABLE_ABC
				run("abc -fast");
				run("opt -fast");
		#endif
			}
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat");
			run("check");
		}
	}
} SynthPass;

PRIVATE_NAMESPACE_END
