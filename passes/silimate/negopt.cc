/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2026  Abhinav Tondapu   <abhinav@silimate.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool did_something;

#include "passes/silimate/peepopt_negopt.h"

struct NegoptPass : public Pass {
	NegoptPass() : Pass("negopt", "optimize negation patterns in arithmetic") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    negopt [options] [selection]\n");
		log("\n");
		log("This pass optimizes negation patterns in arithmetic expressions.\n");
		log("\n");
		log("    -pre\n");
		log("        Run pre-balancing normalization patterns:\n");
		log("        - sub2neg: a - b -> a + (-b)\n");
		log("        - negexpand: -(a + b) -> (-a) + (-b)\n");
		log("        - negneg: -(-a) -> a\n");
		log("        - negmux: -(s ? a : b) -> s ? (-a) : (-b)\n");
		log("\n");
		log("    -post\n");
		log("        Run post-balancing rebuild patterns:\n");
		log("        - negrebuild: (-a) + (-b) -> -(a + b)\n");
		log("        - muxneg: s ? (-a) : (-b) -> -(s ? a : b)\n");
		log("        - neg2sub: a + (-b) -> a - b\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing NEGOPT pass (optimize negation patterns).\n");

		bool run_pre = false;
		bool run_post = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-pre") {
				run_pre = true;
				continue;
			}
			if (args[argidx] == "-post") {
				run_post = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!run_pre && !run_post)
			log_cmd_error("Must specify -pre or -post\n");

		for (auto module : design->selected_modules()) {
			did_something = true;

			while (did_something) {
				did_something = false;

				peepopt_pm pm(module);
				pm.setup(module->selected_cells());

				if (run_pre) {
					pm.run_sub2neg();
					pm.run_negexpand();
					pm.run_negneg();
					pm.run_negmux();
				}

				if (run_post) {
					pm.run_negrebuild();
					pm.run_muxneg();
					pm.run_neg2sub();
				}
			}
		}
	}
} NegoptPass;

PRIVATE_NAMESPACE_END
