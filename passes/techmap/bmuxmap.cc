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
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool pmux_mode = false;

		log_header(design, "Executing BMUXMAP pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-pmux") {
				pmux_mode = true;
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

			SigSpec sel = cell->getPort(ID::S);
			SigSpec data = cell->getPort(ID::A);
			int width = GetSize(cell->getPort(ID::Y));
			int s_width = GetSize(cell->getPort(ID::S));

			if(pmux_mode)
			{
				int num_cases = 1 << s_width;
				SigSpec new_a = SigSpec(State::Sx, width);
				SigSpec new_s = module->addWire(NEW_ID, num_cases);
				SigSpec new_data = module->addWire(NEW_ID, width);
				for (int val = 0; val < num_cases; val++)
				{
					module->addEq(NEW_ID, sel, SigSpec(val, GetSize(sel)), new_s[val]);
				}
				RTLIL::Cell *pmux = module->addPmux(NEW_ID, new_a, data, new_s, new_data);
				pmux->add_strpool_attribute(ID::src, cell->get_strpool_attribute(ID::src));
				data = new_data;
			}
			else
			{
				for (int idx = 0; idx < GetSize(sel); idx++) {
					SigSpec new_data = module->addWire(NEW_ID, GetSize(data)/2);
					for (int i = 0; i < GetSize(new_data); i += width) {
						RTLIL::Cell *mux = module->addMux(NEW_ID,
							data.extract(i*2, width),
							data.extract(i*2+width, width),
							sel[idx],
							new_data.extract(i, width));
						mux->add_strpool_attribute(ID::src, cell->get_strpool_attribute(ID::src));
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
