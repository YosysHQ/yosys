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

struct Ice40FfinitPass : public Pass {
	Ice40FfinitPass() : Pass("ice40_ffinit", "iCE40: handle FF init values") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ice40_ffinit [options] [selection]\n");
		log("\n");
		log("Remove zero init values for FF output signals. Add inverters to implement\n");
		log("nonzero init values.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing ICE40_FFINIT pass (implement FF init values).\n");

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
						if (initbits.at(bit) != val)
							log_error("Conflicting init values for signal %s (%s = %s, %s = %s).\n",
									log_signal(bit), log_signal(SigBit(wire, i)), log_signal(val),
									log_signal(initbit_to_wire[bit]), log_signal(initbits.at(bit)));
						continue;
					}

					initbits[bit] = val;
					initbit_to_wire[bit] = SigBit(wire, i);
				}
			}

			pool<IdString> sb_dff_types = {
				"\\SB_DFF",    "\\SB_DFFE",   "\\SB_DFFSR",   "\\SB_DFFR",   "\\SB_DFFSS",   "\\SB_DFFS",   "\\SB_DFFESR",
				"\\SB_DFFER",  "\\SB_DFFESS", "\\SB_DFFES",   "\\SB_DFFN",   "\\SB_DFFNE",   "\\SB_DFFNSR", "\\SB_DFFNR",
				"\\SB_DFFNSS", "\\SB_DFFNS",  "\\SB_DFFNESR", "\\SB_DFFNER", "\\SB_DFFNESS", "\\SB_DFFNES"
			};

			for (auto cell : module->selected_cells())
			{
				if (!sb_dff_types.count(cell->type))
					continue;

				SigSpec sig_d = cell->getPort("\\D");
				SigSpec sig_q = cell->getPort("\\Q");

				if (GetSize(sig_d) < 1 || GetSize(sig_q) < 1)
					continue;

				SigBit bit_d = sigmap(sig_d[0]);
				SigBit bit_q = sigmap(sig_q[0]);

				if (!initbits.count(bit_q))
					continue;

				State val = initbits.at(bit_q);
				handled_initbits.insert(bit_q);

				log("FF init value for cell %s (%s): %s = %c\n", log_id(cell), log_id(cell->type),
						log_signal(bit_q), val != State::S0 ? '1' : '0');

				if (val == State::S0)
					continue;

				string type_str = cell->type.str();

				if (type_str.back() == 'S') {
					type_str.back() = 'R';
					cell->type = type_str;
					cell->setPort("\\R", cell->getPort("\\S"));
					cell->unsetPort("\\S");
				} else
				if (type_str.back() == 'R') {
					type_str.back() = 'S';
					cell->type = type_str;
					cell->setPort("\\S", cell->getPort("\\R"));
					cell->unsetPort("\\R");
				}

				Wire *new_bit_d = module->addWire(NEW_ID);
				Wire *new_bit_q = module->addWire(NEW_ID);

				module->addNotGate(NEW_ID, bit_d, new_bit_d);
				module->addNotGate(NEW_ID, new_bit_q, bit_q);

				cell->setPort("\\D", new_bit_d);
				cell->setPort("\\Q", new_bit_q);
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
} Ice40FfinitPass;

PRIVATE_NAMESPACE_END
