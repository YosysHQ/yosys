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

struct FfNormPolPass : public Pass {
	FfNormPolPass() : Pass("ffnormpol", "normalize FF/latch control polarities to positive") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ffnormpol [selection]\n");
		log("\n");
		log("This pass normalizes built-in FF and latch control polarities to\n");
		log("positive polarity.  Negative-edge clocks and active-low enables,\n");
		log("resets, sets, clears, and latch enables are rewritten by inserting\n");
		log("inverters on the corresponding control signals and re-emitting the\n");
		log("cell with positive polarity.\n");
		log("\n");
		log("Both coarse-grain cells with polarity parameters and fine-grain cells\n");
		log("with polarity encoded in the cell type are handled through FfData.\n");
		log("\n");
	}

	struct Worker {
		Module *module;
		SigMap sigmap;
		FfInitVals initvals;
		dict<SigSpec, SigSpec> inverted_signals;
		int normalized_cells = 0;
		int normalized_controls = 0;

		Worker(Module *module) : module(module), sigmap(module), initvals(&sigmap, module) { }

		SigSpec invert(SigSpec sig, const char *suffix, const std::string &src)
		{
			sig = sigmap(sig);
			if (inverted_signals.count(sig))
				return inverted_signals.at(sig);

			SigSpec inv = module->Not(NEW_ID_SUFFIX(suffix), sig, false, src);
			inverted_signals[sig] = inv;
			return inv;
		}

		bool normalize(FfData &ff, SigSpec &sig, bool &pol, const char *suffix)
		{
			if (pol)
				return false;

			sig = invert(sig, suffix, ff.attributes[ID::src].decode_string());
			pol = true;
			normalized_controls++;
			return true;
		}

		void run()
		{
			std::vector<Cell *> cells;
			for (auto cell : module->selected_cells())
				if (cell->is_builtin_ff())
					cells.push_back(cell);

			for (auto cell : cells) {
				FfData ff(&initvals, cell);
				bool changed = false;

				if (ff.has_clk)
					changed |= normalize(ff, ff.sig_clk, ff.pol_clk, "ffnormpol_clk");
				if (ff.has_ce)
					changed |= normalize(ff, ff.sig_ce, ff.pol_ce, "ffnormpol_ce");
				if (ff.has_aload)
					changed |= normalize(ff, ff.sig_aload, ff.pol_aload, "ffnormpol_aload");
				if (ff.has_arst)
					changed |= normalize(ff, ff.sig_arst, ff.pol_arst, "ffnormpol_arst");
				if (ff.has_srst)
					changed |= normalize(ff, ff.sig_srst, ff.pol_srst, "ffnormpol_srst");
				if (ff.has_sr) {
					changed |= normalize(ff, ff.sig_clr, ff.pol_clr, "ffnormpol_clr");
					changed |= normalize(ff, ff.sig_set, ff.pol_set, "ffnormpol_set");
				}

				if (changed) {
					ff.emit();
					normalized_cells++;
				}
			}
		}
	};

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing FFNORMPOL pass (normalize FF/latch control polarities).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
			break;
		extra_args(args, argidx, design);

		int total_cells = 0;
		int total_controls = 0;
		for (auto module : design->selected_modules()) {
			Worker worker(module);
			worker.run();
			total_cells += worker.normalized_cells;
			total_controls += worker.normalized_controls;
		}

		log("Normalized %d controls on %d FF/latch cells.\n", total_controls, total_cells);
	}
} FfNormPolPass;

PRIVATE_NAMESPACE_END
