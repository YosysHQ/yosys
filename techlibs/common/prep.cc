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

struct PrepPass : public ScriptPass
{
	PrepPass() : ScriptPass("prep", "generic synthesis script") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    prep [options]\n");
		log("\n");
		log("This command runs a conservative RTL synthesis. A typical application for this\n");
		log("is the preparation stage of a verification flow. This command does not operate\n");
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
		log("    -ifx\n");
		log("        passed to 'proc'. uses verilog simulation behavior for verilog if/case\n");
		log("        undef handling. this also prevents 'wreduce' from being run.\n");
		log("\n");
		log("    -memx\n");
		log("        simulate verilog simulation behavior for out-of-bounds memory accesses\n");
		log("        using the 'memory_memx' pass.\n");
		log("\n");
		log("    -nomem\n");
		log("        do not run any of the memory_* passes\n");
		log("\n");
		log("    -rdff\n");
		log("        do not pass -nordff to 'memory_dff'. This enables merging of FFs into\n");
		log("        memory read ports.\n");
		log("\n");
		log("    -nokeepdc\n");
		log("        do not call opt_* with -keepdc\n");
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

	string top_module, fsm_opts;
	bool autotop, flatten, ifxmode, memxmode, nomemmode, nokeepdc, nordff;

	void clear_flags() YS_OVERRIDE
	{
		top_module.clear();

		autotop = false;
		flatten = false;
		ifxmode = false;
		memxmode = false;
		nomemmode = false;
		nokeepdc = false;
		nordff = true;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		string run_from, run_to;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module = args[++argidx];
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
			if (args[argidx] == "-ifx") {
				ifxmode = true;
				continue;
			}
			if (args[argidx] == "-memx") {
				memxmode = true;
				continue;
			}
			if (args[argidx] == "-nomem") {
				nomemmode = true;
				continue;
			}
			if (args[argidx] == "-nordff") {
				nordff = true;
				continue;
			}
			if (args[argidx] == "-rdff") {
				nordff = false;
				continue;
			}
			if (args[argidx] == "-nokeepdc") {
				nokeepdc = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing PREP pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
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
			if (help_mode)
				run("proc [-ifx]");
			else
				run(ifxmode ? "proc -ifx" : "proc");
			if (help_mode || flatten)
				run("flatten", "(if -flatten)");
			run(nokeepdc ? "opt_expr" : "opt_expr -keepdc");
			run("opt_clean");
			run("check");
			run(nokeepdc ? "opt" : "opt -keepdc");
			if (!ifxmode) {
				if (help_mode)
					run("wreduce -keepdc [-memx]");
				else if (nokeepdc)
					run(memxmode ? "wreduce -memx" : "wreduce");
				else
					run(memxmode ? "wreduce -keepdc -memx" : "wreduce -keepdc");
			}
			if (!nomemmode) {
				run(string("memory_dff") + (help_mode ? " [-nordff]" : nordff ? " -nordff" : ""));
				if (help_mode || memxmode)
					run("memory_memx", "(if -memx)");
				run("opt_clean");
				run("memory_collect");
			}
			run(nokeepdc ? "opt -fast" : "opt -keepdc -fast");
		}

		if (check_label("check"))
		{
			run("stat");
			run("check");
		}
	}
} PrepPass;

PRIVATE_NAMESPACE_END
