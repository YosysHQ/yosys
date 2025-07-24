/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
		log("    -nolower\n");
		log("        Do not automatically run 'chformal -lower' to lower $check cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool flag_nolower = false;

		log_header(design, "Executing ASYNC2SYNC pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-nolower") {
				flag_nolower = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		bool have_check_cells = false;

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			FfInitVals initvals(&sigmap, module);

			SigBit initstate;

			for (auto cell : vector<Cell*>(module->selected_cells()))
			{
				if (cell->type.in(ID($print), ID($check)))
				{
					if (cell->type == ID($check))
						have_check_cells = true;

					bool trg_enable = cell->getParam(ID(TRG_ENABLE)).as_bool();
					if (!trg_enable)
						continue;

					int trg_width = cell->getParam(ID(TRG_WIDTH)).as_int();

					if (trg_width > 1)
						log_error("$check cell %s with TRG_WIDTH > 1 is not support by async2sync, use clk2fflogic.\n", log_id(cell));

					if (trg_width == 0) {
						if (initstate == State::S0)
							initstate = module->Initstate(NEW_ID);

						SigBit sig_en = cell->getPort(ID::EN);
						cell->setPort(ID::EN, module->And(NEW_ID, sig_en, initstate));
					} else {
						SigBit sig_en = cell->getPort(ID::EN);
						SigSpec sig_args = cell->getPort(ID::ARGS);
						bool trg_polarity = cell->getParam(ID(TRG_POLARITY)).as_bool();
						SigBit sig_trg = cell->getPort(ID::TRG);
						Wire *sig_en_q = module->addWire(NEW_ID);
						Wire *sig_args_q = module->addWire(NEW_ID, GetSize(sig_args));
						sig_en_q->attributes.emplace(ID::init, State::S0);
						module->addDff(NEW_ID, sig_trg, sig_en, sig_en_q, trg_polarity, cell->get_src_attribute());
						module->addDff(NEW_ID, sig_trg, sig_args, sig_args_q, trg_polarity, cell->get_src_attribute());
						cell->setPort(ID::EN, sig_en_q);
						cell->setPort(ID::ARGS, sig_args_q);
						if (cell->type == ID($check)) {
							SigBit sig_a = cell->getPort(ID::A);
							Wire *sig_a_q = module->addWire(NEW_ID);
							sig_a_q->attributes.emplace(ID::init, State::S1);
							module->addDff(NEW_ID, sig_trg, sig_a, sig_a_q, trg_polarity, cell->get_src_attribute());
							cell->setPort(ID::A, sig_a_q);
						}
					}

					cell->setPort(ID::TRG, SigSpec());

					cell->setParam(ID::TRG_ENABLE, false);
					cell->setParam(ID::TRG_WIDTH, 0);
					cell->setParam(ID::TRG_POLARITY, false);
					cell->set_bool_attribute(ID(trg_on_gclk));
					continue;
				}

				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(&initvals, cell);

				// Skip for $_FF_ and $ff cells.
				if (ff.has_gclk)
					continue;

				if (ff.has_clk && ff.sig_clk.is_fully_const())
					ff.has_ce = ff.has_clk = ff.has_srst = false;

				if (ff.has_clk)
				{
					if (ff.has_sr) {
						ff.unmap_ce_srst();

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
					} else if (ff.has_aload) {
						ff.unmap_ce_srst();

						log("Replacing %s.%s (%s): ALOAD=%s, AD=%s, D=%s, Q=%s\n",
								log_id(module), log_id(cell), log_id(cell->type),
								log_signal(ff.sig_aload), log_signal(ff.sig_ad), log_signal(ff.sig_d), log_signal(ff.sig_q));

						initvals.remove_init(ff.sig_q);

						Wire *new_d = module->addWire(NEW_ID, ff.width);
						Wire *new_q = module->addWire(NEW_ID, ff.width);

						if (ff.pol_aload) {
							if (!ff.is_fine) {
								module->addMux(NEW_ID, new_q, ff.sig_ad, ff.sig_aload, ff.sig_q);
								module->addMux(NEW_ID, ff.sig_d, ff.sig_ad, ff.sig_aload, new_d);
							} else {
								module->addMuxGate(NEW_ID, new_q, ff.sig_ad, ff.sig_aload, ff.sig_q);
								module->addMuxGate(NEW_ID, ff.sig_d, ff.sig_ad, ff.sig_aload, new_d);
							}
						} else {
							if (!ff.is_fine) {
								module->addMux(NEW_ID, ff.sig_ad, new_q, ff.sig_aload, ff.sig_q);
								module->addMux(NEW_ID, ff.sig_ad, ff.sig_d, ff.sig_aload, new_d);
							} else {
								module->addMuxGate(NEW_ID, ff.sig_ad, new_q, ff.sig_aload, ff.sig_q);
								module->addMuxGate(NEW_ID, ff.sig_ad, ff.sig_d, ff.sig_aload, new_d);
							}
						}

						ff.sig_d = new_d;
						ff.sig_q = new_q;
						ff.has_aload = false;
					} else if (ff.has_arst) {
						ff.unmap_srst();

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
						ff.ce_over_srst = false;
						ff.val_srst = ff.val_arst;
						ff.sig_srst = ff.sig_arst;
						ff.pol_srst = ff.pol_arst;
					} else {
						continue;
					}
				}
				else
				{
					// Latch.
					log("Replacing %s.%s (%s): EN=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(ff.sig_aload), log_signal(ff.sig_ad), log_signal(ff.sig_q));

					initvals.remove_init(ff.sig_q);

					Wire *new_q = module->addWire(NEW_ID, ff.width);
					Wire *new_d;

					if (ff.has_aload) {
						new_d = module->addWire(NEW_ID, ff.width);
						if (ff.pol_aload) {
							if (!ff.is_fine)
								module->addMux(NEW_ID, new_q, ff.sig_ad, ff.sig_aload, new_d);
							else
								module->addMuxGate(NEW_ID, new_q, ff.sig_ad, ff.sig_aload, new_d);
						} else {
							if (!ff.is_fine)
								module->addMux(NEW_ID, ff.sig_ad, new_q, ff.sig_aload, new_d);
							else
								module->addMuxGate(NEW_ID, ff.sig_ad, new_q, ff.sig_aload, new_d);
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
					ff.has_aload = false;
					ff.has_arst = false;
					ff.has_sr = false;
					ff.has_gclk = true;
				}
				ff.emit();
			}
		}

		if (have_check_cells && !flag_nolower) {
			log_push();
			Pass::call(design, "chformal -lower");
			log_pop();
		}
	}
} Async2syncPass;

PRIVATE_NAMESPACE_END
