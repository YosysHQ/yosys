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

// Normalize top-end sign/zero extension for PMG prefiltering.
// Strips any redundant high bits so that a sign- or zero-extended SigSpec
// and its narrower original compare equal under index lookups.
//   - top == prev:              sign extension (MSB replicated)
//   - top == SigBit(State::S0): zero extension (constant-zero padding)
// Only the prefilter key is stripped; exact legality is re-checked in the
// code block, so false-positive index hits are safe.
static SigSpec strip_ext_for_match(SigSpec sig)
{
	int n = GetSize(sig);
	if (n <= 1)
		return sig;

	while (n > 1) {
		SigBit top = sig[n-1];
		SigBit prev = sig[n-2];
		// Strip sign-extended (repeated MSB) or zero-extended (S0) bits
		if (top == prev || top == SigBit(State::S0)) {
			n--;
			continue;
		}
		break;
	}

	return sig.extract(0, n);
}

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
		log("Specify exactly one of -pre or -post.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
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

		if (run_pre == run_post)
			log_cmd_error("NEGOPT requires exactly one of -pre or -post.\n");

		log_header(design, "Executing NEGOPT %s pass (optimize negation patterns).\n",
			run_pre ? "PRE" : "POST");

		constexpr int max_iterations = 100;

		for (auto module : design->selected_modules()) {
			auto log_module_event = [&](const char *event) {
				log("%s %s\n", event, log_id(module));
				log_flush();
			};

			auto log_pass_event = [&](const char *event, const char *pass_name, int iter = -1) {
				if (iter >= 0)
					log("      %s %s pass (iter=%d)\n", event, pass_name, iter + 1);
				else
					log("      %s %s pass\n", event, pass_name);
				log_flush();
			};

			if (run_pre) {
				log_module_event("Processing Module:");

				// manual2sub and sub2neg only need to run once: no downstream
				// pre-subpass creates the patterns they match
				// separate pm instances so sub2neg sees the $sub cells manual2sub creates.
				{
					peepopt_pm pm(module);
					pm.setup(module->selected_cells());
					log_pass_event("Starting", "manual2sub");
					pm.run_manual2sub();
					log_pass_event("Ending", "manual2sub");
					log_flush();
				}
				{
					peepopt_pm pm(module);
					pm.setup(module->selected_cells());
					log_pass_event("Starting", "sub2neg");
					pm.run_sub2neg();
					log_pass_event("Ending", "sub2neg");
					log_flush();
				}

				// negexpand/negneg/negmux can feed each other.
				did_something = true;
				for (int iter = 0; iter < max_iterations && did_something; iter++) {
					did_something = false;
					peepopt_pm pm(module);
					pm.setup(module->selected_cells());

					log_pass_event("Starting", "negexpand", iter);
					pm.run_negexpand();
					log_pass_event("Ending", "negexpand", iter);
					log_flush();
					log_pass_event("Starting", "negneg", iter);
					pm.run_negneg();
					log_pass_event("Ending", "negneg", iter);
					log_flush();
					log_pass_event("Starting", "negmux", iter);
					pm.run_negmux();
					log_pass_event("Ending", "negmux", iter);
					log_flush();
				}
				if (did_something)
					log_warning("NEGOPT pre reached max iterations (%d) in module %s without convergence.\n", max_iterations, log_id(module));

				log_module_event("Finished Module:");
			}

			if (run_post) {
				log_module_event("Processing Module:");

				did_something = true;
				for (int iter = 0; iter < max_iterations && did_something; iter++) {
					did_something = false;
					peepopt_pm pm(module);
					pm.setup(module->selected_cells());

					log_pass_event("Starting", "negrebuild", iter);
					pm.run_negrebuild();
					log_pass_event("Ending", "negrebuild", iter);
					log_flush();
					log_pass_event("Starting", "muxneg", iter);
					pm.run_muxneg();
					log_pass_event("Ending", "muxneg", iter);
					log_flush();
					log_pass_event("Starting", "neg2sub", iter);
					pm.run_neg2sub();
					log_pass_event("Ending", "neg2sub", iter);
					log_flush();
				}
				if (did_something)
					log_warning("NEGOPT post reached max iterations (%d) in module %s without convergence.\n", max_iterations, log_id(module));

				log_module_event("Finished Module:");
			}
		}
	}
} NegoptPass;

PRIVATE_NAMESPACE_END
