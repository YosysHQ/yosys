/*
 * Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                     Abhinav Tondapu <abhinav@silimate.com>
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
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
		log("        Run pre-optimization transformations:\n"     );
		log("          - manual2sub: a + ~b + 1  => a - b\n"      );
		log("          - sub2neg:    a - b       => a + (-b)\n"   );
		log("          - negexpand:  -(a + b)    => (-a) + (-b)\n");
		log("          - negneg:     -(-a)       => a\n"          );
		log("          - negmux:     -(s?a:b)    => s?(-a):(-b)\n");
		log("\n");
		log("    -post\n");
		log("        Run post-optimization transformations:\n" );
		log("          - negrebuild: (-a)+(-b)   => -(a + b)\n");
		log("          - muxneg:     s?(-a):(-b) => -(s?a:b)\n");
		log("          - neg2sub:    a + (-b)    => a - b\n"   );
		log("\n");
		log("When called without options, both -pre and -post are executed.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool run_pre = false;
		bool run_post = false;

		log_header(design, "Executing NEGOPT pass (optimize negation patterns).\n");

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

		if (!run_pre && !run_post) {
			run_pre = true;
			run_post = true;
		}

		constexpr int max_iterations = 100;

		for (auto module : design->selected_modules()) {
			if (run_pre) {
				did_something = true;
				for (int iter = 0; iter < max_iterations && did_something; iter++) {
					did_something = false;
					peepopt_pm pm(module);
					pm.setup(module->selected_cells());

					pm.run_manual2sub();  // Reduce manual 2's complement to subtraction first
					log_flush();
					pm.run_sub2neg();
					log_flush();
					pm.run_negexpand();
					log_flush();
					pm.run_negneg();
					log_flush();
					pm.run_negmux();
					log_flush();
				}
				if (did_something)
					log_warning("NEGOPT pre reached max iterations (%d) in module %s without convergence.\n", max_iterations, log_id(module));
			}

			if (run_post) {
				did_something = true;
				for (int iter = 0; iter < max_iterations && did_something; iter++) {
					did_something = false;
					peepopt_pm pm(module);
					pm.setup(module->selected_cells());

					pm.run_negrebuild();
					log_flush();
					pm.run_muxneg();
					log_flush();
					pm.run_neg2sub();
					log_flush();
				}
				if (did_something)
					log_warning("NEGOPT post reached max iterations (%d) in module %s without convergence.\n", max_iterations, log_id(module));
			}
		}
	}
} NegoptPass;

PRIVATE_NAMESPACE_END
