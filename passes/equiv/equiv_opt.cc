/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018  whitequark <whitequark@whitequark.org>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EquivOptPass:public ScriptPass
{
	EquivOptPass() : ScriptPass("equiv_opt", "prove equivalence for optimized circuit") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_opt [options] [command]\n");
		log("\n");
		log("This command uses temporal induction to check circuit equivalence before and\n");
		log("after an optimization pass.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to the start of the command list, and empty to\n");
		log("        label is synonymous to the end of the command list.\n");
		log("\n");
		log("    -map <filename>\n");
		log("        expand the modules in this file before proving equivalence. this is\n");
		log("        useful for handling architecture-specific primitives.\n");
		log("\n");
		log("    -blacklist <file>\n");
		log("        Do not match cells or signals that match the names in the file\n");
		log("        (passed to equiv_make).\n");
		log("\n");
		log("    -assert\n");
		log("        produce an error if the circuits are not equivalent.\n");
		log("\n");
		log("    -multiclock\n");
		log("        run clk2fflogic before equivalence checking.\n");
		log("\n");
		log("    -async2sync\n");
		log("        run async2sync before equivalence checking.\n");
		log("\n");
		log("    -undef\n");
		log("        enable modelling of undef states during equiv_induct.\n");
		log("\n");
		log("The following commands are executed by this verification command:\n");
		help_script();
		log("\n");
	}

	std::string command, techmap_opts, make_opts;
	bool assert, undef, multiclock, async2sync;

	void clear_flags() YS_OVERRIDE
	{
		command = "";
		techmap_opts = "";
		make_opts = "";
		assert = false;
		undef = false;
		multiclock = false;
		async2sync = false;
	}

	void execute(std::vector < std::string > args, RTLIL::Design * design) YS_OVERRIDE
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-run" && argidx + 1 < args.size()) {
				size_t pos = args[argidx + 1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos + 1);
				continue;
			}
			if (args[argidx] == "-map" && argidx + 1 < args.size()) {
				techmap_opts += " -map " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-blacklist" && argidx + 1 < args.size()) {
				make_opts += " -blacklist " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-assert") {
				assert = true;
				continue;
			}
			if (args[argidx] == "-undef") {
				undef = true;
				continue;
			}
			if (args[argidx] == "-multiclock") {
				multiclock = true;
				continue;
			}
			if (args[argidx] == "-async2sync") {
				async2sync = true;
				continue;
			}
			break;
		}

		for (; argidx < args.size(); argidx++) {
			if (command.empty()) {
				if (args[argidx].compare(0, 1, "-") == 0)
					cmd_error(args, argidx, "Unknown option.");
			} else {
				command += " ";
			}
			command += args[argidx];
		}

		if (command.empty())
			log_cmd_error("No optimization pass specified!\n");

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (async2sync && multiclock)
			log_cmd_error("The '-async2sync' and '-multiclock' options are mutually exclusive!\n");

		log_header(design, "Executing EQUIV_OPT pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
	{
		if (check_label("run_pass")) {
			run("hierarchy -auto-top");
			run("design -save preopt");
			if (help_mode)
				run("[command]");
			else
				run(command);
			run("design -stash postopt");
		}

		if (check_label("prepare")) {
			run("design -copy-from preopt  -as gold A:top");
			run("design -copy-from postopt -as gate A:top");
		}

		if ((!techmap_opts.empty() || help_mode) && check_label("techmap", "(only with -map)")) {
			string opts;
			if (help_mode)
				opts = " -map <filename> ...";
			else
				opts = techmap_opts;
			run("techmap -wb -D EQUIV -autoproc" + opts);
		}

		if (check_label("prove")) {
			if (multiclock || help_mode)
				run("clk2fflogic", "(only with -multiclock)");
			if (async2sync || help_mode)
				run("async2sync", " (only with -async2sync)");
			string opts;
			if (help_mode)
				opts = " -blacklist <filename> ...";
			else
				opts = make_opts;
			run("equiv_make" + opts + " gold gate equiv");
			if (help_mode)
				run("equiv_induct [-undef] equiv");
			else if (undef)
				run("equiv_induct -undef equiv");
			else
				run("equiv_induct equiv");
			if (help_mode)
				run("equiv_status [-assert] equiv");
			else if (assert)
				run("equiv_status -assert equiv");
			else
				run("equiv_status equiv");
		}

		if (check_label("restore")) {
			run("design -load preopt");
		}
	}
} EquivOptPass;

PRIVATE_NAMESPACE_END
