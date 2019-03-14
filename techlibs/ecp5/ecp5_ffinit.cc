/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2018-19  David Shah <david@symbioticeda.com>
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

struct Ecp5FfinitPass : public Pass {
	Ecp5FfinitPass() : Pass("ecp5_ffinit", "ECP5: handle FF init values") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ecp5_ffinit [options] [selection]\n");
		log("\n");
		log("Remove init values for FF output signals when equal to reset value.\n");
		log("If reset is not used, set the reset value to the init value, otherwise\n");
		log("unmap out the reset (if not an async reset).\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ECP5_FFINIT pass (implement FF init values).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			log("Handling FF init values in %s.\n", log_id(module));

			SigMap sigmap(module);
			pool<Wire*> init_wires;
			dict<SigBit, State> initbits;
			dict<SigBit, SigBit> initbit_to_wire;
			pool<SigBit> handled_initbits;

			for (auto wire : module->selected_wires())
			{
				if (wire->attributes.count("\\init") == 0)
					continue;

				SigSpec wirebits = sigmap(wire);
				Const initval = wire->attributes.at("\\init");
				init_wires.insert(wire);

				for (int i = 0; i < GetSize(wirebits) && i < GetSize(initval); i++)
				{
					SigBit bit = wirebits[i];
					State val = initval[i];

					if (val != State::S0 && val != State::S1)
						continue;

					if (initbits.count(bit)) {
						if (initbits.at(bit) != val) {
							log_warning("Conflicting init values for signal %s (%s = %s, %s = %s).\n",
									log_signal(bit), log_signal(SigBit(wire, i)), log_signal(val),
									log_signal(initbit_to_wire[bit]), log_signal(initbits.at(bit)));
							initbits.at(bit) = State::Sx;
						}
						continue;
					}

					initbits[bit] = val;
					initbit_to_wire[bit] = SigBit(wire, i);
				}
			}
			for (auto cell : module->selected_cells())
			{
				if (cell->type != "\\TRELLIS_FF")
					continue;
				SigSpec sig_d = cell->getPort("\\DI");
				SigSpec sig_q = cell->getPort("\\Q");
				SigSpec sig_lsr = cell->getPort("\\LSR");

				if (GetSize(sig_d) < 1 || GetSize(sig_q) < 1)
					continue;

				SigBit bit_d = sigmap(sig_d[0]);
				SigBit bit_q = sigmap(sig_q[0]);

				std::string regset = "RESET";
				if (cell->hasParam("\\REGSET"))
					regset = cell->getParam("\\REGSET").decode_string();
				State resetState;
				if (regset == "SET")
					resetState = State::S1;
				else if (regset == "RESET")
					resetState = State::S0;
				else
					log_error("FF cell %s has illegal REGSET value %s.\n",
						log_id(cell), regset.c_str());

				if (!initbits.count(bit_q))
					continue;

				State val = initbits.at(bit_q);

				if (val == State::Sx)
					continue;

				log("FF init value for cell %s (%s): %s = %c\n", log_id(cell), log_id(cell->type),
						log_signal(bit_q), val != State::S0 ? '1' : '0');
				// Initval is the same as the reset state. Matches hardware, nowt more to do
				if (val == resetState) {
					handled_initbits.insert(bit_q);
					continue;
				}

				if (GetSize(sig_lsr) >= 1 && sig_lsr[0] != State::S0) {
					std::string srmode = "LSR_OVER_CE";
					if (cell->hasParam("\\SRMODE"))
						srmode = cell->getParam("\\SRMODE").decode_string();
					if (srmode == "ASYNC") {
						log("Async reset value %c for FF cell %s inconsistent with init value %c.\n",
							resetState != State::S0 ? '1' : '0', log_id(cell), val != State::S0 ? '1' : '0');
					} else {
						SigBit bit_lsr = sigmap(sig_lsr[0]);
						Wire *new_bit_d = module->addWire(NEW_ID);
						if (resetState == State::S0) {
							module->addAndnotGate(NEW_ID, bit_d, bit_lsr, new_bit_d);
						} else {
							module->addOrGate(NEW_ID, bit_d, bit_lsr, new_bit_d);
						}

						cell->setPort("\\DI", new_bit_d);
						cell->setPort("\\LSR", State::S0);

						if(cell->hasPort("\\CE")) {
							std::string cemux = "CE";
							if (cell->hasParam("\\CEMUX"))
								cemux = cell->getParam("\\CEMUX").decode_string();
							SigSpec sig_ce = cell->getPort("\\CE");
							if (GetSize(sig_ce) >= 1) {
								SigBit bit_ce = sigmap(sig_ce[0]);
								Wire *new_bit_ce = module->addWire(NEW_ID);
								if (cemux == "INV")
									module->addAndnotGate(NEW_ID, bit_ce, bit_lsr, new_bit_ce);
								else
									module->addOrGate(NEW_ID, bit_ce, bit_lsr, new_bit_ce);
								cell->setPort("\\CE", new_bit_ce);
							}
						}
						cell->setParam("\\REGSET", val != State::S0 ? Const("SET") : Const("RESET"));
						handled_initbits.insert(bit_q);
					}
				} else {
					cell->setParam("\\REGSET", val != State::S0 ? Const("SET") : Const("RESET"));
					handled_initbits.insert(bit_q);
				}
			}

			for (auto wire : init_wires)
			{
				if (wire->attributes.count("\\init") == 0)
					continue;

				SigSpec wirebits = sigmap(wire);
				Const &initval = wire->attributes.at("\\init");
				bool remove_attribute = true;

				for (int i = 0; i < GetSize(wirebits) && i < GetSize(initval); i++) {
					if (handled_initbits.count(wirebits[i]))
						initval[i] = State::Sx;
					else if (initval[i] != State::Sx)
						remove_attribute = false;
				}

				if (remove_attribute)
					wire->attributes.erase("\\init");
			}
		}
	}
} Ecp5FfinitPass;

PRIVATE_NAMESPACE_END
