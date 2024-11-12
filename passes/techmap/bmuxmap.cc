/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Marcelina Kościelnicka <mwk@0x04.net>
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

struct BmuxmapPass : public Pass {
	BmuxmapPass() : Pass("bmuxmap", "transform $bmux cells to trees of $mux cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    bmuxmap [selection]\n");
		log("\n");
		log("This pass transforms $bmux cells to trees of $mux cells.\n");
		log("\n");
		log("    -pmux\n");
		log("        transform to $pmux instead of $mux cells.\n");
		log("\n");
		log("    -fewunq\n");
		log("        only transform $bmux cells that have few unique A bits.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool pmux_mode = false;
		bool fewunq_mode = false;

		log_header(design, "Executing BMUXMAP pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-pmux") {
				pmux_mode = true;
				continue;
			}
			if (args[argidx] == "-fewunq") {
				fewunq_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : module->selected_cells())
		{
			if (cell->type != ID($bmux))
				continue;
			
			if (fewunq_mode) {
				SigSpec data = cell->getPort(ID::A);
				SigMap sigmap(module);
				pool<SigBit> unqbits;
				for (auto bit : data)
					if (bit.wire != nullptr)
						unqbits.insert(sigmap(bit));
				if (GetSize(unqbits) > GetSize(data)/2)
					continue;
			}

			SigSpec sel = cell->getPort(ID::S);
			SigSpec data = cell->getPort(ID::A);
			int width = GetSize(cell->getPort(ID::Y));
			int s_width = GetSize(cell->getPort(ID::S));

			if(pmux_mode)
			{
				int num_cases = 1 << s_width;
				SigSpec new_a = SigSpec(State::Sx, width);
				SigSpec new_s = module->addWire(NEW_ID2_SUFFIX("sel"), num_cases); // SILIMATE: Improve the naming
				SigSpec new_data = module->addWire(NEW_ID2_SUFFIX("data"), width); // SILIMATE: Improve the naming
				for (int val = 0; val < num_cases; val++) {
					RTLIL::Cell *eq = module->addEq(NEW_ID2_SUFFIX("eq"), sel, SigSpec(val, GetSize(sel)), new_s[val]); // SILIMATE: Improve the naming
					for (auto attr : cell->attributes) // SILIMATE: Copy all attributes from original cell to new cell
						eq->attributes[attr.first] = attr.second;
				}
				IdString cell_name = cell->name; // SILIMATE: Save the original cell name
				module->rename(cell_name, NEW_ID); // SILIMATE: Rename the original cell, which will be deleted
				RTLIL::Cell *pmux = module->addPmux(cell_name, new_a, data, new_s, new_data); // SILIMATE: Improve the naming
				for (auto attr : cell->attributes) // SILIMATE: Copy all attributes from original cell to new cell
					pmux->attributes[attr.first] = attr.second;
				pmux->set_bool_attribute("\\bmuxmap"); // SILIMATE: Mark the cell as created by bmuxmap
				data = new_data;
			}
			else
			{
				for (int idx = 0; idx < GetSize(sel); idx++) {
					SigSpec new_data = module->addWire(NEW_ID2_SUFFIX("data"), GetSize(data)/2); // SILIMATE: Improve the naming
					for (int i = 0; i < GetSize(new_data); i += width) {
						RTLIL::Cell *mux = module->addMux(NEW_ID2, // SILIMATE: Improve the naming
							data.extract(i*2, width),
							data.extract(i*2+width, width),
							sel[idx],
							new_data.extract(i, width));
						for (auto attr : cell->attributes) // SILIMATE: Copy all attributes from original cell to new cell
							mux->attributes[attr.first] = attr.second;
						mux->set_bool_attribute("\\bmuxmap"); // SILIMATE: Mark the cell as created by bmuxmap
					}
					data = new_data;
				}
			}

			module->connect(cell->getPort(ID::Y), data);
			module->remove(cell);
		}
	}
} BmuxmapPass;

PRIVATE_NAMESPACE_END
