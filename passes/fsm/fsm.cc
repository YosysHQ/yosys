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
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct FsmPass : public Pass {
	FsmPass() : Pass("fsm", "extract and optimize finite state machines") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm [options] [selection]\n");
		log("\n");
		log("This pass calls all the other fsm_* passes in a useful order. This performs\n");
		log("FSM extraction and optimization. It also calls opt_clean as needed:\n");
		log("\n");
		log("    fsm_detect          unless got option -nodetect\n");
		log("    fsm_extract\n");
		log("\n");
		log("    fsm_opt\n");
		log("    opt_clean\n");
		log("    fsm_opt\n");
		log("\n");
		log("    fsm_expand          if got option -expand\n");
		log("    opt_clean           if got option -expand\n");
		log("    fsm_opt             if got option -expand\n");
		log("\n");
		log("    fsm_recode          unless got option -norecode\n");
		log("\n");
		log("    fsm_info\n");
		log("\n");
		log("    fsm_export          if got option -export\n");
		log("    fsm_map             unless got option -nomap\n");
		log("\n");
		log("Options:\n");
		log("\n");
		log("    -expand, -norecode, -export, -nomap\n");
		log("        enable or disable passes as indicated above\n");
		log("\n");
		log("    -fullexpand\n");
		log("        call expand with -full option\n");
		log("\n");
		log("    -encoding type\n");
		log("    -fm_set_fsm_file file\n");
		log("    -encfile file\n");
		log("        passed through to fsm_recode pass\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool flag_nomap = false;
		bool flag_norecode = false;
		bool flag_nodetect = false;
		bool flag_expand = false;
		bool flag_fullexpand = false;
		bool flag_export = false;
		std::string fm_set_fsm_file_opt;
		std::string encfile_opt;
		std::string encoding_opt;

		log_header(design, "Executing FSM pass (extract and optimize FSM).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-fm_set_fsm_file" && argidx+1 < args.size() && fm_set_fsm_file_opt.empty()) {
				fm_set_fsm_file_opt = " -fm_set_fsm_file " + args[++argidx];
				continue;
			}
			if (arg == "-encfile" && argidx+1 < args.size() && encfile_opt.empty()) {
				encfile_opt = " -encfile " + args[++argidx];
				continue;
			}
			if (arg == "-encoding" && argidx+1 < args.size() && encoding_opt.empty()) {
				encoding_opt = " -encoding " + args[++argidx];
				continue;
			}
			if (arg == "-nodetect") {
				flag_nodetect = true;
				continue;
			}
			if (arg == "-norecode") {
				flag_norecode = true;
				continue;
			}
			if (arg == "-nomap") {
				flag_nomap = true;
				continue;
			}
			if (arg == "-expand") {
				flag_expand = true;
				continue;
			}
			if (arg == "-fullexpand") {
				flag_fullexpand = true;
				continue;
			}
			if (arg == "-export") {
				flag_export = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!flag_nodetect)
			Pass::call(design, "fsm_detect");
		Pass::call(design, "fsm_extract");

		Pass::call(design, "fsm_opt");
		Pass::call(design, "opt_clean");
		Pass::call(design, "fsm_opt");

		if (flag_expand || flag_fullexpand) {
			Pass::call(design, flag_fullexpand ? "fsm_expand -full" : "fsm_expand");
			Pass::call(design, "opt_clean");
			Pass::call(design, "fsm_opt");
		}

		if (!flag_norecode)
			Pass::call(design, "fsm_recode" + fm_set_fsm_file_opt + encfile_opt + encoding_opt);
		Pass::call(design, "fsm_info");

		if (flag_export)
			Pass::call(design, "fsm_export");

		if (!flag_nomap)
			Pass::call(design, "fsm_map");

		log_pop();
	}
} FsmPass;

PRIVATE_NAMESPACE_END
