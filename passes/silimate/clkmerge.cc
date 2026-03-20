/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.
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
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ClkMergePass : public Pass {
	ClkMergePass() : Pass("clkmerge", "merge multiple clock domains into one") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clkmerge [-target <signal>] [selection]\n");
		log("\n");
		log("This command rewrites all flip-flop clock ports in the selected modules to\n");
		log("use a single clock signal, effectively merging all clock domains into one.\n");
		log("\n");
		log("This is useful for miter-based equivalence checking where gold and gate\n");
		log("copies may use different clock signal names for what is logically the same\n");
		log("clock. Without merging, ABC's -dff mode will partition them into separate\n");
		log("clock domains, creating spurious cross-domain ports that degrade SAT\n");
		log("performance.\n");
		log("\n");
		log("    -target <signal>\n");
		log("        use the specified signal as the merged clock. if not given, the\n");
		log("        clock signal of the first FF encountered is used.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string target_clk_name;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-target" && argidx + 1 < args.size()) {
				target_clk_name = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);

			dict<SigBit, int> clk_domain_count;
			std::vector<std::pair<Cell*, SigSpec>> ff_clk_pairs;

			for (auto cell : module->selected_cells())
			{
				if (!cell->is_builtin_ff())
					continue;

				FfData ff(nullptr, cell);
				if (!ff.has_clk)
					continue;

				SigSpec clk = sigmap(ff.sig_clk);
				ff_clk_pairs.push_back({cell, clk});

				for (auto bit : clk)
					clk_domain_count[bit]++;
			}

			if (ff_clk_pairs.empty())
				continue;

			// Determine target clock
			SigSpec target_clk;
			if (!target_clk_name.empty()) {
				RTLIL::SigSpec sig;
				if (!SigSpec::parse_sel(sig, design, module, target_clk_name))
					log_cmd_error("Failed to parse target clock expression '%s'.\n", target_clk_name.c_str());
				target_clk = sigmap(sig);
			} else {
				target_clk = ff_clk_pairs[0].second;
			}

			// Collect distinct clocks
			pool<SigSpec> all_clks;
			for (auto &pair : ff_clk_pairs)
				all_clks.insert(pair.second);

			if (all_clks.size() <= 1) {
				log("Module %s: only one clock domain found, nothing to merge.\n", log_id(module));
				continue;
			}

			log("Module %s: merging %d clock domains into %s\n",
				log_id(module), GetSize(all_clks), log_signal(target_clk));

			int rewritten = 0;
			for (auto &pair : ff_clk_pairs)
			{
				Cell *cell = pair.first;
				SigSpec old_clk = pair.second;

				if (old_clk == target_clk)
					continue;

				// Fine-grain cells use ID::C, coarse-grain use ID::CLK
				if (cell->hasPort(ID::C))
					cell->setPort(ID::C, target_clk);
				else if (cell->hasPort(ID::CLK))
					cell->setPort(ID::CLK, target_clk);

				rewritten++;
			}

			log("  Rewrote clock on %d flip-flops.\n", rewritten);
		}
	}
} ClkMergePass;

PRIVATE_NAMESPACE_END
