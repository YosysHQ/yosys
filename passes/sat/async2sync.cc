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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Async2syncPass : public Pass {
	Async2syncPass() : Pass("async2sync", "convert async FF inputs to sync circuits") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    async2sync [options] [selection]\n");
		log("\n");
		log("This command replaces async FF inputs with sync circuits emulating the same\n");
		log("behavior for when the async signals are actually synchronized to the clock.\n");
		log("\n");
		log("This pass assumes negative hold time for the async FF inputs. For example when\n");
		log("a reset deasserts with the clock edge, then the FF output will still drive the\n");
		log("reset value in the next cycle regardless of the data-in value at the time of\n");
		log("the clock edge.\n");
		log("\n");
		log("Currently only $adff, $dffsr, and $dlatch cells are supported by this pass.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		// bool flag_noinit = false;

		log_header(design, "Executing ASYNC2SYNC pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-noinit") {
			// 	flag_noinit = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			FfInitVals initvals(&sigmap, module);

			for (auto cell : vector<Cell*>(module->selected_cells()))
			{
				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(&initvals, cell);

				// Skip for $_FF_ and $ff cells.
				if (ff.has_d && !ff.has_clk && !ff.has_en)
					continue;

				if (ff.has_clk)
				{
					if (!ff.has_sr && !ff.has_arst)
						continue;

					if (ff.has_sr) {
						ff.unmap_ce_srst(module);

						log("Replacing %s.%s (%s): SET=%s, CLR=%s, D=%s, Q=%s\n",
								log_id(module), log_id(cell), log_id(cell->type),
								log_signal(ff.sig_set), log_signal(ff.sig_clr), log_signal(ff.sig_d), log_signal(ff.sig_q));

						initvals.remove_init(ff.sig_q);

						Wire *new_d = module->addWire(NEW_ID, ff.width);
						Wire *new_q = module->addWire(NEW_ID, ff.width);

						SigSpec sig_set = ff.sig_set;
						SigSpec sig_clr = ff.sig_clr;

						if (!ff.pol_set) {
							if (!ff.is_fine)
								sig_set = module->Not(NEW_ID, sig_set);
							else
								sig_set = module->NotGate(NEW_ID, sig_set);
						}

						if (ff.pol_clr) {
							if (!ff.is_fine)
								sig_clr = module->Not(NEW_ID, sig_clr);
							else
								sig_clr = module->NotGate(NEW_ID, sig_clr);
						}

						if (!ff.is_fine) {
							SigSpec tmp = module->Or(NEW_ID, ff.sig_d, sig_set);
							module->addAnd(NEW_ID, tmp, sig_clr, new_d);

							tmp = module->Or(NEW_ID, new_q, sig_set);
							module->addAnd(NEW_ID, tmp, sig_clr, ff.sig_q);
						} else {
							SigSpec tmp = module->OrGate(NEW_ID, ff.sig_d, sig_set);
							module->addAndGate(NEW_ID, tmp, sig_clr, new_d);

							tmp = module->OrGate(NEW_ID, new_q, sig_set);
							module->addAndGate(NEW_ID, tmp, sig_clr, ff.sig_q);
						}

						ff.sig_d = new_d;
						ff.sig_q = new_q;
						ff.has_sr = false;
					} else if (ff.has_arst) {
						ff.unmap_srst(module);

						log("Replacing %s.%s (%s): ARST=%s, D=%s, Q=%s\n",
								log_id(module), log_id(cell), log_id(cell->type),
								log_signal(ff.sig_arst), log_signal(ff.sig_d), log_signal(ff.sig_q));

						initvals.remove_init(ff.sig_q);

						Wire *new_q = module->addWire(NEW_ID, ff.width);

						if (ff.pol_arst) {
							if (!ff.is_fine)
								module->addMux(NEW_ID, new_q, ff.val_arst, ff.sig_arst, ff.sig_q);
							else
								module->addMuxGate(NEW_ID, new_q, ff.val_arst[0], ff.sig_arst, ff.sig_q);
						} else {
							if (!ff.is_fine)
								module->addMux(NEW_ID, ff.val_arst, new_q, ff.sig_arst, ff.sig_q);
							else
								module->addMuxGate(NEW_ID, ff.val_arst[0], new_q, ff.sig_arst, ff.sig_q);
						}

						ff.sig_q = new_q;
						ff.has_arst = false;
						ff.has_srst = true;
						ff.val_srst = ff.val_arst;
						ff.sig_srst = ff.sig_arst;
						ff.pol_srst = ff.pol_arst;
					}
				}
				else
				{
					// Latch.
					log("Replacing %s.%s (%s): EN=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(ff.sig_en), log_signal(ff.sig_d), log_signal(ff.sig_q));

					initvals.remove_init(ff.sig_q);

					Wire *new_q = module->addWire(NEW_ID, ff.width);
					Wire *new_d;

					if (ff.has_d) {
						new_d = module->addWire(NEW_ID, ff.width);
						if (ff.pol_en) {
							if (!ff.is_fine)
								module->addMux(NEW_ID, new_q, ff.sig_d, ff.sig_en, new_d);
							else
								module->addMuxGate(NEW_ID, new_q, ff.sig_d, ff.sig_en, new_d);
						} else {
							if (!ff.is_fine)
								module->addMux(NEW_ID, ff.sig_d, new_q, ff.sig_en, new_d);
							else
								module->addMuxGate(NEW_ID, ff.sig_d, new_q, ff.sig_en, new_d);
						}
					} else {
						new_d = new_q;
					}

					if (ff.has_sr) {
						SigSpec sig_set = ff.sig_set;
						SigSpec sig_clr = ff.sig_clr;

						if (!ff.pol_set) {
							if (!ff.is_fine)
								sig_set = module->Not(NEW_ID, sig_set);
							else
								sig_set = module->NotGate(NEW_ID, sig_set);
						}

						if (ff.pol_clr) {
							if (!ff.is_fine)
								sig_clr = module->Not(NEW_ID, sig_clr);
							else
								sig_clr = module->NotGate(NEW_ID, sig_clr);
						}

						if (!ff.is_fine) {
							SigSpec tmp = module->Or(NEW_ID, new_d, sig_set);
							module->addAnd(NEW_ID, tmp, sig_clr, ff.sig_q);
						} else {
							SigSpec tmp = module->OrGate(NEW_ID, new_d, sig_set);
							module->addAndGate(NEW_ID, tmp, sig_clr, ff.sig_q);
						}
					} else if (ff.has_arst) {
						if (ff.pol_arst) {
							if (!ff.is_fine)
								module->addMux(NEW_ID, new_d, ff.val_arst, ff.sig_arst, ff.sig_q);
							else
								module->addMuxGate(NEW_ID, new_d, ff.val_arst[0], ff.sig_arst, ff.sig_q);
						} else {
							if (!ff.is_fine)
								module->addMux(NEW_ID, ff.val_arst, new_d, ff.sig_arst, ff.sig_q);
							else
								module->addMuxGate(NEW_ID, ff.val_arst[0], new_d, ff.sig_arst, ff.sig_q);
						}
					} else {
						module->connect(ff.sig_q, new_d);
					}

					ff.sig_d = new_d;
					ff.sig_q = new_q;
					ff.has_en = false;
					ff.has_arst = false;
					ff.has_sr = false;
					ff.has_d = true;
				}

				IdString name = cell->name;
				module->remove(cell);
				ff.emit(module, name);
			}
		}
	}
} Async2syncPass;

PRIVATE_NAMESPACE_END
