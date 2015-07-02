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

bool check_label(bool &active, std::string run_from, std::string run_to, std::string label)
{
	if (!run_from.empty() && run_from == run_to) {
		active = (label == run_from);
	} else {
		if (label == run_from)
			active = true;
		if (label == run_to)
			active = false;
	}
	return active;
}

struct SynthPass : public Pass {
	SynthPass() : Pass("synth", "generic synthesis script") { }
	virtual void help()
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
		log("\n");
		log("    begin:\n");
		log("        hierarchy -check [-top <top>]\n");
		log("\n");
		log("    coarse:\n");
		log("        proc\n");
		log("        opt_clean\n");
		log("        check\n");
		log("        opt\n");
		log("        wreduce\n");
		log("        alumacc\n");
		log("        share\n");
		log("        opt\n");
		log("        fsm\n");
		log("        opt -fast\n");
		log("        memory -nomap\n");
		log("        opt_clean\n");
		log("\n");
		log("    fine:\n");
		log("        opt -fast -full\n");
		log("        memory_map\n");
		log("        opt -full\n");
		log("        techmap\n");
		log("        opt -fast\n");
	#ifdef YOSYS_ENABLE_ABC
		log("        abc -fast\n");
		log("        opt -fast\n");
	#endif
		log("\n");
		log("    check:\n");
		log("        hierarchy -check\n");
		log("        stat\n");
		log("        check\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_module, fsm_opts, memory_opts;
		std::string run_from, run_to;
		bool noalumacc = false;
		bool nofsm = false;
		bool noabc = false;

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

		bool active = run_from.empty();

		log_header("Executing SYNTH pass.\n");
		log_push();

		if (check_label(active, run_from, run_to, "begin"))
		{
			if (top_module.empty())
				Pass::call(design, stringf("hierarchy -check"));
			else
				Pass::call(design, stringf("hierarchy -check -top %s", top_module.c_str()));
		}

		if (check_label(active, run_from, run_to, "coarse"))
		{
			Pass::call(design, "proc");
			Pass::call(design, "opt_clean");
			Pass::call(design, "check");
			Pass::call(design, "opt");
			Pass::call(design, "wreduce");
			if (!noalumacc)
				Pass::call(design, "alumacc");
			Pass::call(design, "share");
			Pass::call(design, "opt");
			if (!nofsm)
				Pass::call(design, "fsm" + fsm_opts);
			Pass::call(design, "opt -fast");
			Pass::call(design, "memory -nomap" + memory_opts);
			Pass::call(design, "opt_clean");
		}

		if (check_label(active, run_from, run_to, "fine"))
		{
			Pass::call(design, "opt -fast -full");
			Pass::call(design, "memory_map");
			Pass::call(design, "opt -full");
			Pass::call(design, "techmap");
			Pass::call(design, "opt -fast");

			if (!noabc) {
		#ifdef YOSYS_ENABLE_ABC
				Pass::call(design, "abc -fast");
				Pass::call(design, "opt -fast");
		#endif
			}
		}

		if (check_label(active, run_from, run_to, "check"))
		{
			Pass::call(design, "hierarchy -check");
			Pass::call(design, "stat");
			Pass::call(design, "check");
		}

		log_pop();
	}
} SynthPass;

PRIVATE_NAMESPACE_END
