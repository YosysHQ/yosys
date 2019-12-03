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

struct MemoryPass : public Pass {
	MemoryPass() : Pass("memory", "translate memories to basic cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory [-nomap] [-nordff] [-memx] [-bram <bram_rules>] [selection]\n");
		log("\n");
		log("This pass calls all the other memory_* passes in a useful order:\n");
		log("\n");
		log("    opt_mem\n");
		log("    memory_dff [-nordff]                (-memx implies -nordff)\n");
		log("    opt_clean\n");
		log("    memory_share\n");
		log("    opt_clean\n");
		log("    memory_memx                         (when called with -memx)\n");
		log("    memory_collect\n");
		log("    memory_bram -rules <bram_rules>     (when called with -bram)\n");
		log("    memory_map                          (skipped if called with -nomap)\n");
		log("\n");
		log("This converts memories to word-wide DFFs and address decoders\n");
		log("or multiport memory blocks if called with the -nomap option.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool flag_nomap = false;
		bool flag_nordff = false;
		bool flag_memx = false;
		string memory_bram_opts;

		log_header(design, "Executing MEMORY pass.\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-nomap") {
				flag_nomap = true;
				continue;
			}
			if (args[argidx] == "-nordff") {
				flag_nordff = true;
				continue;
			}
			if (args[argidx] == "-memx") {
				flag_nordff = true;
				flag_memx = true;
				continue;
			}
			if (argidx+1 < args.size() && args[argidx] == "-bram") {
				memory_bram_opts += " -rules " + args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		Pass::call(design, "opt_mem");
		Pass::call(design, flag_nordff ? "memory_dff -nordff" : "memory_dff");
		Pass::call(design, "opt_clean");
		Pass::call(design, "memory_share");
		if (flag_memx)
			Pass::call(design, "memory_memx");
		Pass::call(design, "opt_clean");
		Pass::call(design, "memory_collect");

		if (!memory_bram_opts.empty())
			Pass::call(design, "memory_bram" + memory_bram_opts);

		if (!flag_nomap)
			Pass::call(design, "memory_map");

		log_pop();
	}
} MemoryPass;

PRIVATE_NAMESPACE_END
