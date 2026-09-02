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
		log("This command rewrites all flip-flop clock ports and polarities in the\n");
		log("selected modules to use a single clock domain, merging both different\n");
		log("clock signals and different clock polarities (posedge vs negedge).\n");
		log("\n");
		log("This is useful for miter-based equivalence checking where gold and gate\n");
		log("copies may use different clock signal names or opposite edges for what\n");
		log("is logically the same clock. Without merging, ABC's -dff mode will\n");
		log("partition them into separate clock domains, creating spurious cross-domain\n");
		log("ports that degrade SAT performance.\n");
		log("\n");
		log("    -target <signal>\n");
		log("        use the specified signal as the merged clock. if not given, the\n");
		log("        clock signal of the first FF encountered is used. all FFs will\n");
		log("        be set to positive-edge triggered on this signal.\n");
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

			struct FfInfo {
				Cell *cell;
				SigSpec clk;
				bool pol_clk;
			};

			std::vector<FfInfo> ff_list;

			for (auto cell : module->selected_cells())
			{
				if (!cell->is_builtin_ff())
					continue;

				FfData ff(nullptr, cell);
				if (!ff.has_clk)
					continue;

				ff_list.push_back({cell, sigmap(ff.sig_clk), ff.pol_clk});
			}

			if (ff_list.empty())
				continue;

			// Determine target clock signal and polarity
			SigSpec target_clk;
			bool target_pol = true; // default to posedge

			if (!target_clk_name.empty()) {
				RTLIL::SigSpec sig;
				if (!SigSpec::parse_sel(sig, design, module, target_clk_name))
					log_cmd_error("Failed to parse target clock expression '%s'.\n", target_clk_name.c_str());
				target_clk = sigmap(sig);
			} else {
				target_clk = ff_list[0].clk;
				target_pol = ff_list[0].pol_clk;
			}

			// Collect distinct (signal, polarity) pairs
			pool<std::pair<SigSpec, bool>> all_domains;
			for (auto &info : ff_list)
				all_domains.insert({info.clk, info.pol_clk});

			if (all_domains.size() <= 1) {
				log("Module %s: only one clock domain found, nothing to merge.\n", log_id(module));
				continue;
			}

			log("Module %s: merging %d clock domains into %s%s\n",
				log_id(module), GetSize(all_domains),
				target_pol ? "" : "!", log_signal(target_clk));

			for (auto &dom : all_domains)
				log("  found domain: %s%s\n",
					dom.second ? "" : "!", log_signal(dom.first));

			int clk_rewritten = 0, pol_rewritten = 0;
			for (auto &info : ff_list)
			{
				Cell *cell = info.cell;
				bool needs_clk_change = (info.clk != target_clk);
				bool needs_pol_change = (info.pol_clk != target_pol);

				if (!needs_clk_change && !needs_pol_change)
					continue;

				if (needs_clk_change) {
					if (cell->hasPort(ID::C))
						cell->setPort(ID::C, target_clk);
					else if (cell->hasPort(ID::CLK))
						cell->setPort(ID::CLK, target_clk);
					clk_rewritten++;
				}

				if (needs_pol_change) {
					// Coarse-grain FFs ($dff, $dffe, etc.) use CLK_POLARITY param
					if (cell->hasParam(ID::CLK_POLARITY)) {
						cell->setParam(ID::CLK_POLARITY, target_pol ? State::S1 : State::S0);
						pol_rewritten++;
					}
					// Fine-grain FFs encode polarity in the type name, so the swap is a
					// cell retype (e.g. $_DFF_N_ -> $_DFF_P_). Every such type is
					// $_<family>_<polarities>_ with the clock polarity leading the
					// polarity group, so it is the character after the second
					// underscore: $_DFF_[P]_, $_DFFE_[P]P_, $_SDFFCE_[N]P0P_. Keying off
					// "_DFF_" instead would miss every family but $_DFF_ itself, and
					// silently leave the flop on the wrong edge.
					else {
						std::string type = cell->type.str();
						size_t pos = type.find('_', type.find('_') + 1);
						if (pos != std::string::npos)
							pos++;
						if (pos != std::string::npos && pos < type.size() &&
						    (type[pos] == 'P' || type[pos] == 'N')) {
							type[pos] = target_pol ? 'P' : 'N';
							cell->type = RTLIL::IdString(type);
							pol_rewritten++;
						} else {
							// Never silently merge a clock while leaving the edge alone
							log_warning("Cannot retype %s (%s) to %s edge; it stays on "
								    "the opposite edge of the merged clock.\n",
								    log_id(cell->name), log_id(cell->type),
								    target_pol ? "positive" : "negative");
						}
					}
				}
			}

			log("  Rewrote clock signal on %d FFs, polarity on %d FFs.\n",
				clk_rewritten, pol_rewritten);
		}
	}
} ClkMergePass;

PRIVATE_NAMESPACE_END
