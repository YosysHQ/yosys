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

struct BreakSopPass : public Pass {
	BreakSopPass() : Pass("breaksop", "break $sop cells into $reduce_and/$reduce_or cells") { }
	void help() override
	{
		log("\n");
		log("    breaksop [selection]\n");
		log("\n");
		log("Break $sop cells into $reduce_and/$reduce_or cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing BREAKSOP pass (break $sop cells into $reduce_and/$reduce_or cells).\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules())
		{
			// Data structures
			pool<Cell*> cells_to_remove;
			SigMap sigmap(module);

			// Process $sop cells
			for (auto cell : module->selected_cells())
			{
				if (cell->type == ID($sop))
				{
					// Read the inputs/outputs/parameters of the $sop cell
					auto sop_inputs = sigmap(cell->getPort(ID::A));
					auto sop_output = sigmap(cell->getPort(ID::Y))[0];
					auto sop_depth = cell->getParam(ID::DEPTH).as_int();
					auto sop_width = cell->getParam(ID::WIDTH).as_int();
					auto sop_table = cell->getParam(ID::TABLE);

					// Get $sop output wire name
					module->rename(cell->name, module->uniquify(sop_output.wire->name.str() + "_sop"));

					// Construct $reduce_and cells
					pool<SigBit> intermed_wires;
					for (int i = 0; i < sop_depth; i++) {
						// Wire for the output
						auto and_out = module->addWire(NEW_ID2_SUFFIX("andterm_out"));
						intermed_wires.insert(and_out);

						// Signals for the inputs
						pool<SigBit> and_in;
						for (int j = 0; j < sop_width; j++)
							if (sop_table[2 * (i * sop_width + j) + 0])
								and_in.insert(module->Not(NEW_ID2_SUFFIX(stringf("sop_in_%d_comp", j)), sop_inputs[j], false, cell->get_src_attribute()));
							else if (sop_table[2 * (i * sop_width + j) + 1])
								and_in.insert(sop_inputs[j]);

						// Construct the cell
						module->addReduceAnd(NEW_ID2_SUFFIX("andterm"), and_in, and_out, false, cell->get_src_attribute());
					}

					// Construct the $reduce_or cell
					module->addReduceOr(NEW_ID2_SUFFIX("orterm"), intermed_wires, sop_output, false, cell->get_src_attribute());

					// Mark the $sop cell for removal
					cells_to_remove.insert(cell);
				}
			}

			// Perform removal of $sop cells
			for (auto cell : cells_to_remove)
				module->remove(cell);
		}
	}
} BreakSopPass;

PRIVATE_NAMESPACE_END
