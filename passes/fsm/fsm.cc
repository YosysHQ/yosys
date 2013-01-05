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

struct FsmPass : public Pass {
	FsmPass() : Pass("fsm") { }
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_nomap = false;
		bool flag_norecode = false;
		bool flag_expand = false;
		bool flag_export = false;
		std::string fm_set_fsm_file_opt;

		log_header("Executing FSM pass (extract and optimize FSM).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-fm_set_fsm_file" && argidx+1 < args.size() && fm_set_fsm_file_opt.empty()) {
				fm_set_fsm_file_opt = " -fm_set_fsm_file " + args[++argidx];
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
			if (arg == "-export") {
				flag_export = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		Pass::call(design, "fsm_detect");
		Pass::call(design, "fsm_extract");

		Pass::call(design, "fsm_opt");
		Pass::call(design, "opt_rmunused");
		Pass::call(design, "fsm_opt");

		if (flag_expand) {
			Pass::call(design, "fsm_expand");
			Pass::call(design, "opt_rmunused");
			Pass::call(design, "fsm_opt");
		}

		if (!flag_norecode)
			Pass::call(design, "fsm_recode" + fm_set_fsm_file_opt);
		Pass::call(design, "fsm_info");

		if (!flag_nomap)
			Pass::call(design, "fsm_map");

		if (flag_export)
			Pass::call(design, "fsm_export");

		log_pop();
	}
} FsmPass;
 
