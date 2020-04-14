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

struct ZinitPass : public Pass {
	ZinitPass() : Pass("zinit", "add inverters so all FF are zero-initialized") { }
	void help() YS_OVERRIDE
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
			dict<SigBit, std::pair<State,SigBit>> initbits;

			for (auto wire : module->selected_wires())
			{
				if (wire->attributes.count(ID::init) == 0)
					continue;

				SigSpec wirebits = sigmap(wire);
				Const initval = wire->attributes.at(ID::init);

				for (int i = 0; i < GetSize(wirebits) && i < GetSize(initval); i++)
				{
					SigBit bit = wirebits[i];
					State val = initval[i];

					if (val != State::S0 && val != State::S1 && bit.wire != nullptr)
						continue;

					if (initbits.count(bit)) {
						if (initbits.at(bit).first != val)
							log_error("Conflicting init values for signal %s (%s = %s != %s).\n",
									log_signal(bit), log_signal(SigBit(wire, i)),
									log_signal(val), log_signal(initbits.at(bit).first));
						continue;
					}

					initbits[bit] = std::make_pair(val,SigBit(wire,i));
				}
			}

			pool<IdString> dff_types = {
								// FIXME: It would appear that supporting
								//    $dffsr/$_DFFSR_* would require a new
								//    cell type where S has priority over R
				ID($ff), ID($dff), ID($dffe), /*ID($dffsr),*/ ID($adff),
				ID($_FF_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_),
				/*ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
				ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_),*/
				ID($_DFF_N_), ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
				ID($_DFF_P_), ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_),
				// Async set/reset
				ID($__DFFE_NN0), ID($__DFFE_NN1), ID($__DFFE_NP0), ID($__DFFE_NP1),
				ID($__DFFE_PN0), ID($__DFFE_PN1), ID($__DFFE_PP0), ID($__DFFE_PP1),
				// Sync set/reset
				ID($__DFFS_NN0_), ID($__DFFS_NN1_), ID($__DFFS_NP0_), ID($__DFFS_NP1_),
				ID($__DFFS_PN0_), ID($__DFFS_PN1_), ID($__DFFS_PP0_), ID($__DFFS_PP1_),
				ID($__DFFSE_NN0), ID($__DFFSE_NN1), ID($__DFFSE_NP0), ID($__DFFSE_NP1),
				ID($__DFFSE_PN0), ID($__DFFSE_PN1), ID($__DFFSE_PP0), ID($__DFFSE_PP1)
			};

			for (auto cell : module->selected_cells())
			{
				if (!dff_types.count(cell->type))
					continue;

				SigSpec sig_d = sigmap(cell->getPort(ID::D));
				SigSpec sig_q = sigmap(cell->getPort(ID::Q));

				if (GetSize(sig_d) < 1 || GetSize(sig_q) < 1)
					continue;

				Const initval;

				for (int i = 0; i < GetSize(sig_q); i++) {
					if (initbits.count(sig_q[i])) {
						const auto &d = initbits.at(sig_q[i]);
						initval.bits.push_back(d.first);
						const auto &b = d.second;
						b.wire->attributes.at(ID::init)[b.offset] = State::Sx;
					} else
						initval.bits.push_back(all_mode ? State::S0 : State::Sx);
				}

				Wire *initwire = module->addWire(NEW_ID, GetSize(initval));
				initwire->attributes[ID::init] = initval;

				for (int i = 0; i < GetSize(initwire); i++)
					if (initval[i] == State::S1)
					{
						sig_d[i] = module->NotGate(NEW_ID, sig_d[i]);
						module->addNotGate(NEW_ID, SigSpec(initwire, i), sig_q[i]);
						initwire->attributes[ID::init][i] = State::S0;
					}
					else
					{
						module->connect(sig_q[i], SigSpec(initwire, i));
					}

				log("FF init value for cell %s (%s): %s = %s\n", log_id(cell), log_id(cell->type),
						log_signal(sig_q), log_signal(initval));

				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, initwire);

				if (cell->type == ID($adff)) {
					auto val = cell->getParam(ID::ARST_VALUE);
					for (int i = 0; i < GetSize(initwire); i++)
						if (initval[i] == State::S1)
							val[i] = (val[i] == State::S1 ? State::S0 : State::S1);
					cell->setParam(ID::ARST_VALUE, std::move(val));
				}
				else if (initval == State::S1) {
					std::string t = cell->type.str();
					if (cell->type.in(ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
								ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_)))
					{
						t[8] = (t[8] == '0' ? '1' : '0');
					}
					else if (cell->type.in(ID($__DFFE_NN0), ID($__DFFE_NN1), ID($__DFFE_NP0), ID($__DFFE_NP1),
								ID($__DFFE_PN0), ID($__DFFE_PN1), ID($__DFFE_PP0), ID($__DFFE_PP1),
								ID($__DFFS_NN0_), ID($__DFFS_NN1_), ID($__DFFS_NP0_), ID($__DFFS_NP1_),
								ID($__DFFS_PN0_), ID($__DFFS_PN1_), ID($__DFFS_PP0_), ID($__DFFS_PP1_)))
					{
						t[10] = (t[10] == '0' ? '1' : '0');
					}
					else if (cell->type.in(ID($__DFFSE_NN0), ID($__DFFSE_NN1), ID($__DFFSE_NP0), ID($__DFFSE_NP1),
								ID($__DFFSE_PN0), ID($__DFFSE_PN1), ID($__DFFSE_PP0), ID($__DFFSE_PP1)))
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
