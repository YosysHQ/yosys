/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018 Icenowy Zheng <icenowy@aosc.io>
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

struct EfinixDetermineInitPass : public Pass {
	EfinixDetermineInitPass() : Pass("efinix_determine_init", "Efinix: Determine the init value of cells") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    efinix_determine_init [selection]\n");
		log("\n");
		log("Determine the init value of cells that doesn't allow unknown init value.\n");
		log("\n");
	}

	Const determine_init(Const init)
	{
		for (int i = 0; i < GetSize(init); i++) {
			if (init[i] != State::S0 && init[i] != State::S1)
				init[i] = State::S0;
		}

		return init;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing EFINIX_DETERMINE_INIT pass (determine init value for cells).\n");

		extra_args(args, args.size(), design);

		int cnt = 0;
		for (auto module : design->selected_modules())
		{
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\EFX_RAM_5K")
				{
					cell->setParam("\\INIT_0", determine_init(cell->getParam("\\INIT_0")));					
					cell->setParam("\\INIT_1", determine_init(cell->getParam("\\INIT_1")));
					cell->setParam("\\INIT_2", determine_init(cell->getParam("\\INIT_2")));
					cell->setParam("\\INIT_3", determine_init(cell->getParam("\\INIT_3")));
					cell->setParam("\\INIT_4", determine_init(cell->getParam("\\INIT_4")));
					cell->setParam("\\INIT_5", determine_init(cell->getParam("\\INIT_5")));
					cell->setParam("\\INIT_6", determine_init(cell->getParam("\\INIT_6")));
					cell->setParam("\\INIT_7", determine_init(cell->getParam("\\INIT_7")));
					cell->setParam("\\INIT_8", determine_init(cell->getParam("\\INIT_8")));
					cell->setParam("\\INIT_9", determine_init(cell->getParam("\\INIT_9")));
					cell->setParam("\\INIT_A", determine_init(cell->getParam("\\INIT_A")));
					cell->setParam("\\INIT_B", determine_init(cell->getParam("\\INIT_B")));
					cell->setParam("\\INIT_C", determine_init(cell->getParam("\\INIT_C")));
					cell->setParam("\\INIT_D", determine_init(cell->getParam("\\INIT_D")));
					cell->setParam("\\INIT_E", determine_init(cell->getParam("\\INIT_E")));
					cell->setParam("\\INIT_F", determine_init(cell->getParam("\\INIT_F")));
					cell->setParam("\\INIT_10", determine_init(cell->getParam("\\INIT_10")));
					cell->setParam("\\INIT_11", determine_init(cell->getParam("\\INIT_11")));
					cell->setParam("\\INIT_12", determine_init(cell->getParam("\\INIT_12")));
					cell->setParam("\\INIT_13", determine_init(cell->getParam("\\INIT_13")));

					cnt++;
				}
			}
		}
		log_header(design, "Updated %d cells with determined init value.\n", cnt);
	}
} EfinixDetermineInitPass;

PRIVATE_NAMESPACE_END
