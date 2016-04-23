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

struct DffinitPass : public Pass {
	DffinitPass() : Pass("dffinit", "set INIT param on FF cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dffinit [options] [selection]\n");
		log("\n");
		log("This pass sets an FF cell parameter to the the initial value of the net it\n");
		log("drives. (This is primarily used in FPGA flows.)\n");
		log("\n");
		log("    -ff <cell_name> <output_port> <init_param>\n");
		log("        operate on the specified cell type. this option can be used\n");
		log("        multiple times.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing DFFINIT pass (set INIT param on FF cells).\n");

		dict<IdString, dict<IdString, IdString>> ff_types;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-ff" && argidx+3 < args.size()) {
				IdString cell_name = RTLIL::escape_id(args[++argidx]);
				IdString output_port = RTLIL::escape_id(args[++argidx]);
				IdString init_param = RTLIL::escape_id(args[++argidx]);
				ff_types[cell_name][output_port] = init_param;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			dict<SigBit, State> init_bits;
			pool<SigBit> cleanup_bits;
			pool<SigBit> used_bits;

			for (auto wire : module->selected_wires()) {
				if (wire->attributes.count("\\init")) {
					Const value = wire->attributes.at("\\init");
					for (int i = 0; i < min(GetSize(value), GetSize(wire)); i++)
						init_bits[sigmap(SigBit(wire, i))] = value[i];
				}
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						used_bits.insert(bit);
			}

			for (auto cell : module->selected_cells())
			{
				for (auto it : cell->connections())
					if (!cell->known() || cell->input(it.first))
						for (auto bit : sigmap(it.second))
							used_bits.insert(bit);

				if (ff_types.count(cell->type) == 0)
					continue;

				for (auto &it : ff_types[cell->type])
				{
					if (!cell->hasPort(it.first))
						continue;

					SigSpec sig = sigmap(cell->getPort(it.first));
					Const value;

					if (cell->hasParam(it.second))
						value = cell->getParam(it.second);

					for (int i = 0; i < GetSize(sig); i++) {
						if (init_bits.count(sig[i]) == 0)
							continue;
						while (GetSize(value.bits) <= i)
							value.bits.push_back(State::S0);
						value.bits[i] = init_bits.at(sig[i]);
						cleanup_bits.insert(sig[i]);
					}

					log("Setting %s.%s.%s (port=%s, net=%s) to %s.\n", log_id(module), log_id(cell), log_id(it.second),
							log_id(it.first), log_signal(sig), log_signal(value));
					cell->setParam(it.second, value);
				}
			}

			for (auto wire : module->selected_wires())
				if (wire->attributes.count("\\init")) {
					Const &value = wire->attributes.at("\\init");
					bool do_cleanup = true;
					for (int i = 0; i < min(GetSize(value), GetSize(wire)); i++) {
						SigBit bit = sigmap(SigBit(wire, i));
						if (cleanup_bits.count(bit) || !used_bits.count(bit))
							value[i] = State::Sx;
						else if (value[i] != State::Sx)
							do_cleanup = false;
					}
					if (do_cleanup) {
						log("Removing init attribute from wire %s.%s.\n", log_id(module), log_id(wire));
						wire->attributes.erase("\\init");
					}
				}
		}
	}
} DffinitPass;

PRIVATE_NAMESPACE_END
