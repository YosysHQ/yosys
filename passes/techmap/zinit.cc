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

struct ZinitPass : public Pass {
	ZinitPass() : Pass("zinit", "add inverters so all FF are zero-initialized") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    zinit [options] [selection]\n");
		log("\n");
		log("Add inverters as needed to make all FFs zero-initialized.\n");
		log("\n");
		log("    -all\n");
		log("        also add zero initialization to uninitialized FFs\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool all_mode = false;

		log_header(design, "Executing ZINIT pass (make all FFs zero-initialized).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-all") {
				all_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			FfInitVals initvals(&sigmap, module);

			pool<IdString> dff_types = {
								// FIXME: It would appear that supporting
								//    $dffsr/$_DFFSR_* would require a new
								//    cell type where S has priority over R
				ID($ff), ID($dff), ID($dffe), /*ID($dffsr),*/ ID($adff), ID($adffe),
				ID($sdff), ID($sdffe), ID($sdffce),
				ID($_FF_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_),
				/*ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
				ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_),*/
				ID($_DFF_N_), ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
				ID($_DFF_P_), ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_),
				// Async set/reset
				ID($_DFFE_NN0P_), ID($_DFFE_NN1P_), ID($_DFFE_NP0P_), ID($_DFFE_NP1P_),
				ID($_DFFE_PN0P_), ID($_DFFE_PN1P_), ID($_DFFE_PP0P_), ID($_DFFE_PP1P_),
				ID($_DFFE_NN0N_), ID($_DFFE_NN1N_), ID($_DFFE_NP0N_), ID($_DFFE_NP1N_),
				ID($_DFFE_PN0N_), ID($_DFFE_PN1N_), ID($_DFFE_PP0N_), ID($_DFFE_PP1N_),
				// Sync set/reset
				ID($_SDFF_NN0_), ID($_SDFF_NN1_), ID($_SDFF_NP0_), ID($_SDFF_NP1_),
				ID($_SDFF_PN0_), ID($_SDFF_PN1_), ID($_SDFF_PP0_), ID($_SDFF_PP1_),
				ID($_SDFFE_NN0P_), ID($_SDFFE_NN1P_), ID($_SDFFE_NP0P_), ID($_SDFFE_NP1P_),
				ID($_SDFFE_PN0P_), ID($_SDFFE_PN1P_), ID($_SDFFE_PP0P_), ID($_SDFFE_PP1P_),
				ID($_SDFFE_NN0N_), ID($_SDFFE_NN1N_), ID($_SDFFE_NP0N_), ID($_SDFFE_NP1N_),
				ID($_SDFFE_PN0N_), ID($_SDFFE_PN1N_), ID($_SDFFE_PP0N_), ID($_SDFFE_PP1N_),
				ID($_SDFFCE_NN0P_), ID($_SDFFCE_NN1P_), ID($_SDFFCE_NP0P_), ID($_SDFFCE_NP1P_),
				ID($_SDFFCE_PN0P_), ID($_SDFFCE_PN1P_), ID($_SDFFCE_PP0P_), ID($_SDFFCE_PP1P_),
				ID($_SDFFCE_NN0N_), ID($_SDFFCE_NN1N_), ID($_SDFFCE_NP0N_), ID($_SDFFCE_NP1N_),
				ID($_SDFFCE_PN0N_), ID($_SDFFCE_PN1N_), ID($_SDFFCE_PP0N_), ID($_SDFFCE_PP1N_)
			};

			for (auto cell : module->selected_cells())
			{
				if (!dff_types.count(cell->type))
					continue;

				SigSpec sig_d = sigmap(cell->getPort(ID::D));
				SigSpec sig_q = sigmap(cell->getPort(ID::Q));

				if (GetSize(sig_d) < 1 || GetSize(sig_q) < 1)
					continue;

				Const initval = initvals(sig_q);
				Const newval = initval;
				initvals.remove_init(sig_q);

				Wire *initwire = module->addWire(NEW_ID, GetSize(sig_q));

				for (int i = 0; i < GetSize(initwire); i++)
					if (initval[i] == State::S1)
					{
						sig_d[i] = module->NotGate(NEW_ID, sig_d[i]);
						module->addNotGate(NEW_ID, SigSpec(initwire, i), sig_q[i]);
						newval[i] = State::S0;
					}
					else
					{
						module->connect(sig_q[i], SigSpec(initwire, i));
						if (all_mode)
							newval[i] = State::S0;
					}

				initvals.set_init(initwire, newval);

				log("FF init value for cell %s (%s): %s = %s\n", log_id(cell), log_id(cell->type),
						log_signal(sig_q), log_signal(initval));

				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, initwire);

				if (cell->type.in(ID($adff), ID($adffe))) {
					auto val = cell->getParam(ID::ARST_VALUE);
					for (int i = 0; i < GetSize(initwire); i++)
						if (initval[i] == State::S1)
							val[i] = (val[i] == State::S1 ? State::S0 : State::S1);
					cell->setParam(ID::ARST_VALUE, std::move(val));
				}
				else if (cell->type.in(ID($sdff), ID($sdffe), ID($sdffce))) {
					auto val = cell->getParam(ID::SRST_VALUE);
					for (int i = 0; i < GetSize(initwire); i++)
						if (initval[i] == State::S1)
							val[i] = (val[i] == State::S1 ? State::S0 : State::S1);
					cell->setParam(ID::SRST_VALUE, std::move(val));
				}
				else if (initval == State::S1) {
					std::string t = cell->type.str();
					if (cell->type.in(ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
								ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_)))
					{
						t[8] = (t[8] == '0' ? '1' : '0');
					}
					else if (cell->type.in(ID($_SDFF_NN0_), ID($_SDFF_NN1_), ID($_SDFF_NP0_), ID($_SDFF_NP1_),
								ID($_SDFF_PN0_), ID($_SDFF_PN1_), ID($_SDFF_PP0_), ID($_SDFF_PP1_)))
					{
						t[9] = (t[9] == '0' ? '1' : '0');
					}
					else if (cell->type.in(ID($_DFFE_NN0P_), ID($_DFFE_NN1P_), ID($_DFFE_NP0P_), ID($_DFFE_NP1P_),
								ID($_DFFE_PN0P_), ID($_DFFE_PN1P_), ID($_DFFE_PP0P_), ID($_DFFE_PP1P_),
								ID($_DFFE_NN0N_), ID($_DFFE_NN1N_), ID($_DFFE_NP0N_), ID($_DFFE_NP1N_),
								ID($_DFFE_PN0N_), ID($_DFFE_PN1N_), ID($_DFFE_PP0N_), ID($_DFFE_PP1N_)))
					{
						t[9] = (t[9] == '0' ? '1' : '0');
					}
					else if (cell->type.in(ID($_SDFFE_NN0P_), ID($_SDFFE_NN1P_), ID($_SDFFE_NP0P_), ID($_SDFFE_NP1P_),
								ID($_SDFFE_PN0P_), ID($_SDFFE_PN1P_), ID($_SDFFE_PP0P_), ID($_SDFFE_PP1P_),
								ID($_SDFFE_NN0N_), ID($_SDFFE_NN1N_), ID($_SDFFE_NP0N_), ID($_SDFFE_NP1N_),
								ID($_SDFFE_PN0N_), ID($_SDFFE_PN1N_), ID($_SDFFE_PP0N_), ID($_SDFFE_PP1N_)))
					{
						t[10] = (t[10] == '0' ? '1' : '0');
					}
					else if (cell->type.in(ID($_SDFFCE_NN0P_), ID($_SDFFCE_NN1P_), ID($_SDFFCE_NP0P_), ID($_SDFFCE_NP1P_),
								ID($_SDFFCE_PN0P_), ID($_SDFFCE_PN1P_), ID($_SDFFCE_PP0P_), ID($_SDFFCE_PP1P_),
								ID($_SDFFCE_NN0N_), ID($_SDFFCE_NN1N_), ID($_SDFFCE_NP0N_), ID($_SDFFCE_NP1N_),
								ID($_SDFFCE_PN0N_), ID($_SDFFCE_PN1N_), ID($_SDFFCE_PP0N_), ID($_SDFFCE_PP1N_)))
					{
						t[11] = (t[11] == '0' ? '1' : '0');
					}
					cell->type = t;
				}
			}
		}
	}
} ZinitPass;

PRIVATE_NAMESPACE_END
