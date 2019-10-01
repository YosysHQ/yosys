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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Async2syncPass : public Pass {
	Async2syncPass() : Pass("async2sync", "convert async FF inputs to sync circuits") { }
	void help() YS_OVERRIDE
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
			dict<SigBit, State> initbits;
			pool<SigBit> del_initbits;

			for (auto wire : module->wires())
				if (wire->attributes.count("\\init") > 0)
				{
					Const initval = wire->attributes.at("\\init");
					SigSpec initsig = sigmap(wire);

					for (int i = 0; i < GetSize(initval) && i < GetSize(initsig); i++)
						if (initval[i] == State::S0 || initval[i] == State::S1)
							initbits[initsig[i]] = initval[i];
				}

			for (auto cell : vector<Cell*>(module->selected_cells()))
			{
				if (cell->type.in("$adff"))
				{
					// bool clk_pol = cell->parameters["\\CLK_POLARITY"].as_bool();
					bool arst_pol = cell->parameters["\\ARST_POLARITY"].as_bool();
					Const arst_val = cell->parameters["\\ARST_VALUE"];

					// SigSpec sig_clk = cell->getPort("\\CLK");
					SigSpec sig_arst = cell->getPort("\\ARST");
					SigSpec sig_d = cell->getPort("\\D");
					SigSpec sig_q = cell->getPort("\\Q");

					log("Replacing %s.%s (%s): ARST=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(sig_arst), log_signal(sig_d), log_signal(sig_q));

					Const init_val;
					for (int i = 0; i < GetSize(sig_q); i++) {
						SigBit bit = sigmap(sig_q[i]);
						init_val.bits.push_back(initbits.count(bit) ? initbits.at(bit) : State::Sx);
						del_initbits.insert(bit);
					}

					Wire *new_d = module->addWire(NEW_ID, GetSize(sig_d));
					Wire *new_q = module->addWire(NEW_ID, GetSize(sig_q));
					new_q->attributes["\\init"] = init_val;

					if (arst_pol) {
						module->addMux(NEW_ID, sig_d, arst_val, sig_arst, new_d);
						module->addMux(NEW_ID, new_q, arst_val, sig_arst, sig_q);
					} else {
						module->addMux(NEW_ID, arst_val, sig_d, sig_arst, new_d);
						module->addMux(NEW_ID, arst_val, new_q, sig_arst, sig_q);
					}

					cell->setPort("\\D", new_d);
					cell->setPort("\\Q", new_q);
					cell->unsetPort("\\ARST");
					cell->unsetParam("\\ARST_POLARITY");
					cell->unsetParam("\\ARST_VALUE");
					cell->type = "$dff";
					continue;
				}

				if (cell->type.in("$dffsr"))
				{
					// bool clk_pol = cell->parameters["\\CLK_POLARITY"].as_bool();
					bool set_pol = cell->parameters["\\SET_POLARITY"].as_bool();
					bool clr_pol = cell->parameters["\\CLR_POLARITY"].as_bool();

					// SigSpec sig_clk = cell->getPort("\\CLK");
					SigSpec sig_set = cell->getPort("\\SET");
					SigSpec sig_clr = cell->getPort("\\CLR");
					SigSpec sig_d = cell->getPort("\\D");
					SigSpec sig_q = cell->getPort("\\Q");

					log("Replacing %s.%s (%s): SET=%s, CLR=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(sig_set), log_signal(sig_clr), log_signal(sig_d), log_signal(sig_q));

					Const init_val;
					for (int i = 0; i < GetSize(sig_q); i++) {
						SigBit bit = sigmap(sig_q[i]);
						init_val.bits.push_back(initbits.count(bit) ? initbits.at(bit) : State::Sx);
						del_initbits.insert(bit);
					}

					Wire *new_d = module->addWire(NEW_ID, GetSize(sig_d));
					Wire *new_q = module->addWire(NEW_ID, GetSize(sig_q));
					new_q->attributes["\\init"] = init_val;

					if (!set_pol)
						sig_set = module->Not(NEW_ID, sig_set);

					if (clr_pol)
						sig_clr = module->Not(NEW_ID, sig_clr);

					SigSpec tmp = module->Or(NEW_ID, sig_d, sig_set);
					module->addAnd(NEW_ID, tmp, sig_clr, new_d);

					tmp = module->Or(NEW_ID, new_q, sig_set);
					module->addAnd(NEW_ID, tmp, sig_clr, sig_q);

					cell->setPort("\\D", new_d);
					cell->setPort("\\Q", new_q);
					cell->unsetPort("\\SET");
					cell->unsetPort("\\CLR");
					cell->unsetParam("\\SET_POLARITY");
					cell->unsetParam("\\CLR_POLARITY");
					cell->type = "$dff";
					continue;
				}

				if (cell->type.in("$dlatch"))
				{
					bool en_pol = cell->parameters["\\EN_POLARITY"].as_bool();

					SigSpec sig_en = cell->getPort("\\EN");
					SigSpec sig_d = cell->getPort("\\D");
					SigSpec sig_q = cell->getPort("\\Q");

					log("Replacing %s.%s (%s): EN=%s, D=%s, Q=%s\n",
							log_id(module), log_id(cell), log_id(cell->type),
							log_signal(sig_en), log_signal(sig_d), log_signal(sig_q));

					Const init_val;
					for (int i = 0; i < GetSize(sig_q); i++) {
						SigBit bit = sigmap(sig_q[i]);
						init_val.bits.push_back(initbits.count(bit) ? initbits.at(bit) : State::Sx);
						del_initbits.insert(bit);
					}

					Wire *new_q = module->addWire(NEW_ID, GetSize(sig_q));
					new_q->attributes["\\init"] = init_val;

					if (en_pol) {
						module->addMux(NEW_ID, new_q, sig_d, sig_en, sig_q);
					} else {
						module->addMux(NEW_ID, sig_d, new_q, sig_en, sig_q);
					}

					cell->setPort("\\D", sig_q);
					cell->setPort("\\Q", new_q);
					cell->unsetPort("\\EN");
					cell->unsetParam("\\EN_POLARITY");
					cell->type = "$ff";
					continue;
				}
			}

			for (auto wire : module->wires())
				if (wire->attributes.count("\\init") > 0)
				{
					bool delete_initattr = true;
					Const initval = wire->attributes.at("\\init");
					SigSpec initsig = sigmap(wire);

					for (int i = 0; i < GetSize(initval) && i < GetSize(initsig); i++)
						if (del_initbits.count(initsig[i]) > 0)
							initval[i] = State::Sx;
						else if (initval[i] != State::Sx)
							delete_initattr = false;

					if (delete_initattr)
						wire->attributes.erase("\\init");
					else
						wire->attributes.at("\\init") = initval;
				}
		}
	}
} Async2syncPass;

PRIVATE_NAMESPACE_END
