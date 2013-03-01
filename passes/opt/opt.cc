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

#include "opt_status.h"
#include "kernel/register.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>

bool OPT_DID_SOMETHING;

struct OptPass : public Pass {
	OptPass() : Pass("opt", "perform simple optimizations") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt [selection]\n");
		log("\n");
		log("This pass calls all the other opt_* passes in a useful order. This performs\n");
		log("a series of trivial optimizations and cleanups. This pass executes the other\n");
		log("passes in the following order:\n");
		log("\n");
		log("    opt_const\n");
		log("    opt_share -nomux\n");
		log("\n");
		log("    do\n");
		log("        opt_muxtree\n");
		log("        opt_reduce\n");
		log("        opt_share\n");
		log("        opt_rmdff\n");
		log("        opt_rmunused\n");
		log("        opt_const\n");
		log("    while [changed design]\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing OPT pass (performing simple optimizations).\n");
		log_push();

		extra_args(args, 1, design);

		log_header("Optimizing in-memory representation of design.\n");
		design->optimize();

		Pass::call(design, "opt_const");
		Pass::call(design, "opt_share -nomux");
		while (1) {
			OPT_DID_SOMETHING = false;
			Pass::call(design, "opt_muxtree");
			Pass::call(design, "opt_reduce");
			Pass::call(design, "opt_share");
			Pass::call(design, "opt_rmdff");
			Pass::call(design, "opt_rmunused");
			Pass::call(design, "opt_const");
			if (OPT_DID_SOMETHING == false)
				break;
			log_header("Rerunning OPT passes. (Maybe there is more to do..)\n");
		}

		log_header("Optimizing in-memory representation of design.\n");
		design->optimize();

		log_header("Finished OPT passes. (There is nothing left to do.)\n");
		log_pop();
	}
} OptPass;
 
