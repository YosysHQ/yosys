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
			dict<SigBit, State> initbits;
			pool<SigBit> donebits;

			for (auto wire : module->selected_wires())
			{
				if (wire->attributes.count(ID(init)) == 0)
					continue;

				SigSpec wirebits = sigmap(wire);
				Const initval = wire->attributes.at(ID(init));
				wire->attributes.erase(ID(init));

				for (int i = 0; i < GetSize(wirebits) && i < GetSize(initval); i++)
				{
					SigBit bit = wirebits[i];
					State val = initval[i];

					if (val != State::S0 && val != State::S1 && bit.wire != nullptr)
						continue;

					if (initbits.count(bit)) {
						if (initbits.at(bit) != val)
							log_error("Conflicting init values for signal %s (%s = %s != %s).\n",
									log_signal(bit), log_signal(SigBit(wire, i)),
									log_signal(val), log_signal(initbits.at(bit)));
						continue;
					}

					initbits[bit] = val;
				}
			}

			pool<IdString> dff_types = {
				ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($adff),
				ID($_FF_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_),
				ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
				ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_),
				ID($_DFF_N_), ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
				ID($_DFF_P_), ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_)
			};

			for (auto cell : module->selected_cells())
			{
				if (!dff_types.count(cell->type))
					continue;

				SigSpec sig_d = sigmap(cell->getPort(ID(D)));
				SigSpec sig_q = sigmap(cell->getPort(ID(Q)));

				if (GetSize(sig_d) < 1 || GetSize(sig_q) < 1)
					continue;

				Const initval;

				for (int i = 0; i < GetSize(sig_q); i++) {
					if (initbits.count(sig_q[i])) {
						initval.bits.push_back(initbits.at(sig_q[i]));
						donebits.insert(sig_q[i]);
					} else
						initval.bits.push_back(all_mode ? State::S0 : State::Sx);
				}

				Wire *initwire = module->addWire(NEW_ID, GetSize(initval));
				initwire->attributes[ID(init)] = initval;

				for (int i = 0; i < GetSize(initwire); i++)
					if (initval.bits.at(i) == State::S1)
					{
						sig_d[i] = module->NotGate(NEW_ID, sig_d[i]);
						module->addNotGate(NEW_ID, SigSpec(initwire, i), sig_q[i]);
						initwire->attributes[ID(init)].bits.at(i) = State::S0;
					}
					else
					{
						module->connect(sig_q[i], SigSpec(initwire, i));
					}

				log("FF init value for cell %s (%s): %s = %s\n", log_id(cell), log_id(cell->type),
						log_signal(sig_q), log_signal(initval));

				cell->setPort(ID(D), sig_d);
				cell->setPort(ID(Q), initwire);
			}

			for (auto &it : initbits)
				if (donebits.count(it.first) == 0)
					log_error("Failed to handle init bit %s = %s.\n", log_signal(it.first), log_signal(it.second));
		}
	}
} ZinitPass;

PRIVATE_NAMESPACE_END
