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
				if (cell->type.in(ID($adff)))
				{
					// bool clk_pol = cell->parameters[ID::CLK_POLARITY].as_bool();
					bool arst_pol = cell->parameters[ID::ARST_POLARITY].as_bool();
					Const arst_val = cell->parameters[ID::ARST_VALUE];

					// SigSpec sig_clk = cell->getPort(ID::CLK);
					SigSpec sig_arst = cell->getPort(ID::ARST);
					SigSpec sig_d = cell->getPort(ID::D);
					SigSpec sig_q = cell->getPort(ID::Q);

					log("Replacing %s.%s (%s): ARST=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(sig_arst), log_signal(sig_d), log_signal(sig_q));

					Const init_val = initvals(sig_q);
					initvals.remove_init(sig_q);

					Wire *new_d = module->addWire(NEW_ID, GetSize(sig_d));
					Wire *new_q = module->addWire(NEW_ID, GetSize(sig_q));
					initvals.set_init(new_q, init_val);

					if (arst_pol) {
						module->addMux(NEW_ID, sig_d, arst_val, sig_arst, new_d);
						module->addMux(NEW_ID, new_q, arst_val, sig_arst, sig_q);
					} else {
						module->addMux(NEW_ID, arst_val, sig_d, sig_arst, new_d);
						module->addMux(NEW_ID, arst_val, new_q, sig_arst, sig_q);
					}

					cell->setPort(ID::D, new_d);
					cell->setPort(ID::Q, new_q);
					cell->unsetPort(ID::ARST);
					cell->unsetParam(ID::ARST_POLARITY);
					cell->unsetParam(ID::ARST_VALUE);
					cell->type = ID($dff);
					continue;
				}

				if (cell->type.in(ID($dffsr)))
				{
					// bool clk_pol = cell->parameters[ID::CLK_POLARITY].as_bool();
					bool set_pol = cell->parameters[ID::SET_POLARITY].as_bool();
					bool clr_pol = cell->parameters[ID::CLR_POLARITY].as_bool();

					// SigSpec sig_clk = cell->getPort(ID::CLK);
					SigSpec sig_set = cell->getPort(ID::SET);
					SigSpec sig_clr = cell->getPort(ID::CLR);
					SigSpec sig_d = cell->getPort(ID::D);
					SigSpec sig_q = cell->getPort(ID::Q);

					log("Replacing %s.%s (%s): SET=%s, CLR=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(sig_set), log_signal(sig_clr), log_signal(sig_d), log_signal(sig_q));

					Const init_val = initvals(sig_q);
					initvals.remove_init(sig_q);

					Wire *new_d = module->addWire(NEW_ID, GetSize(sig_d));
					Wire *new_q = module->addWire(NEW_ID, GetSize(sig_q));
					initvals.set_init(new_q, init_val);

					if (!set_pol)
						sig_set = module->Not(NEW_ID, sig_set);

					if (clr_pol)
						sig_clr = module->Not(NEW_ID, sig_clr);

					SigSpec tmp = module->Or(NEW_ID, sig_d, sig_set);
					module->addAnd(NEW_ID, tmp, sig_clr, new_d);

					tmp = module->Or(NEW_ID, new_q, sig_set);
					module->addAnd(NEW_ID, tmp, sig_clr, sig_q);

					cell->setPort(ID::D, new_d);
					cell->setPort(ID::Q, new_q);
					cell->unsetPort(ID::SET);
					cell->unsetPort(ID::CLR);
					cell->unsetParam(ID::SET_POLARITY);
					cell->unsetParam(ID::CLR_POLARITY);
					cell->type = ID($dff);
					continue;
				}

				if (cell->type.in(ID($dlatch)))
				{
					bool en_pol = cell->parameters[ID::EN_POLARITY].as_bool();

					SigSpec sig_en = cell->getPort(ID::EN);
					SigSpec sig_d = cell->getPort(ID::D);
					SigSpec sig_q = cell->getPort(ID::Q);

					log("Replacing %s.%s (%s): EN=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(sig_en), log_signal(sig_d), log_signal(sig_q));

					Const init_val = initvals(sig_q);
					initvals.remove_init(sig_q);

					Wire *new_q = module->addWire(NEW_ID, GetSize(sig_q));
					initvals.set_init(new_q, init_val);

					if (en_pol) {
						module->addMux(NEW_ID, new_q, sig_d, sig_en, sig_q);
					} else {
						module->addMux(NEW_ID, sig_d, new_q, sig_en, sig_q);
					}

					cell->setPort(ID::D, sig_q);
					cell->setPort(ID::Q, new_q);
					cell->unsetPort(ID::EN);
					cell->unsetParam(ID::EN_POLARITY);
					cell->type = ID($ff);
					continue;
				}
			}
		}
	}
} Async2syncPass;

PRIVATE_NAMESPACE_END
