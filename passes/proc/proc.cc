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

struct ProcPass : public Pass {
	ProcPass() : Pass("proc", "translate processes to netlists") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc [options] [selection]\n");
		log("\n");
		log("This pass calls all the other proc_* passes in the most common order.\n");
		log("\n");
		log("    proc_clean\n");
		log("    proc_rmdead\n");
		log("    proc_init\n");
		log("    proc_arst\n");
		log("    proc_mux\n");
		log("    proc_dlatch\n");
		log("    proc_dff\n");
		log("    proc_clean\n");
		log("\n");
		log("This replaces the processes in the design with multiplexers,\n");
		log("flip-flops and latches.\n");
		log("\n");
		log("The following options are supported:\n");
		log("\n");
		log("    -global_arst [!]<netname>\n");
		log("        This option is passed through to proc_arst.\n");
		log("\n");
		log("    -ifx\n");
		log("        This option is passed through to proc_mux. proc_rmdead is not\n");
		log("        executed in -ifx mode.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string global_arst;
		bool ifxmode = false;

		log_header(design, "Executing PROC pass (convert processes to netlists).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-global_arst" && argidx+1 < args.size()) {
				global_arst = args[++argidx];
				continue;
			}
			if (args[argidx] == "-ifx") {
				ifxmode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		Pass::call(design, "proc_clean");
		if (!ifxmode)
			Pass::call(design, "proc_rmdead");
		Pass::call(design, "proc_init");
		if (global_arst.empty())
			Pass::call(design, "proc_arst");
		else
			Pass::call(design, "proc_arst -global_arst " + global_arst);
		Pass::call(design, ifxmode ? "proc_mux -ifx" : "proc_mux");
		Pass::call(design, "proc_dlatch");
		Pass::call(design, "proc_dff");
		Pass::call(design, "proc_clean");

		log_pop();
	}
} ProcPass;

PRIVATE_NAMESPACE_END
