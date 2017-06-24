/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2017 Robert Ou <rqou@robertou.com>
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

struct Coolrunner2SopPass : public Pass {
	Coolrunner2SopPass() : Pass("coolrunner2_sop", "break $sop cells into ANDTERM/ORTERM cells") { }
	virtual void help()
	{
		log("\n");
		log("    coolrunner2_sop [options] [selection]\n");
		log("\n");
		log("Break $sop cells into ANDTERM/ORTERM cells.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing COOLRUNNER2_SOP pass (break $sop cells into ANDTERM/ORTERM cells).\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "$sop")
				{
					// Read the inputs/outputs/parameters of the $sop cell
					auto sop_inputs = sigmap(cell->getPort("\\A"));
					auto sop_output = sigmap(cell->getPort("\\Y"))[0];
					auto sop_depth = cell->getParam("\\DEPTH").as_int();
					auto sop_width = cell->getParam("\\WIDTH").as_int();
					auto sop_table = cell->getParam("\\TABLE");

					// Construct AND cells
					pool<SigBit> intermed_wires;
					for (int i = 0; i < sop_depth; i++) {
						// Wire for the output
						auto and_out = module->addWire(NEW_ID);
						intermed_wires.insert(and_out);

						// Signals for the inputs
						pool<SigBit> and_in_true;
						pool<SigBit> and_in_comp;
						for (int j = 0; j < sop_width; j++)
						{
							if (sop_table[2 * (i * sop_width + j) + 0])
							{
								and_in_comp.insert(sop_inputs[j]);
							}
							if (sop_table[2 * (i * sop_width + j) + 1])
							{
								and_in_true.insert(sop_inputs[j]);
							}
						}

						// Construct the cell
						auto and_cell = module->addCell(NEW_ID, "\\ANDTERM");
						and_cell->setParam("\\TRUE_INP", GetSize(and_in_true));
						and_cell->setParam("\\COMP_INP", GetSize(and_in_comp));
						and_cell->setPort("\\OUT", and_out);
						and_cell->setPort("\\IN", and_in_true);
						and_cell->setPort("\\IN_B", and_in_comp);
					}

					// If there is only one term, don't construct an OR cell
					if (sop_depth == 1)
					{
						yosys_xtrace = 1;
						module->connect(sop_output, *intermed_wires.begin());
						log("one\n");
					}
					else
					{
						log("more\n");
						// Construct the cell
						auto or_cell = module->addCell(NEW_ID, "\\ORTERM");
						or_cell->setParam("\\WIDTH", sop_depth);
						or_cell->setPort("\\IN", intermed_wires);
						or_cell->setPort("\\OUT", sop_output);
					}

					// Finally, remove the $sop cell
					module->remove(cell);
				}
			}
		}
	}
} Coolrunner2SopPass;

PRIVATE_NAMESPACE_END
