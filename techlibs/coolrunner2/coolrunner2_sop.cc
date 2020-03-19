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
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    coolrunner2_sop [options] [selection]\n");
		log("\n");
		log("Break $sop cells into ANDTERM/ORTERM cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing COOLRUNNER2_SOP pass (break $sop cells into ANDTERM/ORTERM cells).\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules())
		{
			pool<Cell*> cells_to_remove;
			SigMap sigmap(module);

			// Find all the $_NOT_ cells
			dict<SigBit, tuple<SigBit, Cell*>> not_cells;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "$_NOT_")
				{
					auto not_input = sigmap(cell->getPort("\\A")[0]);
					auto not_output = sigmap(cell->getPort("\\Y")[0]);
					not_cells[not_input] = tuple<SigBit, Cell*>(not_output, cell);
				}
			}

			// Find wires that need to become special product terms
			dict<SigBit, pool<tuple<Cell*, std::string>>> special_pterms_no_inv;
			dict<SigBit, pool<tuple<Cell*, std::string>>> special_pterms_inv;
			for (auto cell : module->selected_cells())
			{
				if (cell->type.in("\\FDCP", "\\FDCP_N", "\\FDDCP", "\\FTCP", "\\FTCP_N", "\\FTDCP",
							"\\FDCPE", "\\FDCPE_N", "\\FDDCPE", "\\LDCP", "\\LDCP_N"))
				{
					if (cell->hasPort("\\PRE"))
						special_pterms_no_inv[sigmap(cell->getPort("\\PRE")[0])].insert(
							tuple<Cell*, const char *>(cell, "\\PRE"));
					if (cell->hasPort("\\CLR"))
						special_pterms_no_inv[sigmap(cell->getPort("\\CLR")[0])].insert(
							tuple<Cell*, const char *>(cell, "\\CLR"));
					if (cell->hasPort("\\CE"))
						special_pterms_no_inv[sigmap(cell->getPort("\\CE")[0])].insert(
							tuple<Cell*, const char *>(cell, "\\CE"));

					if (cell->hasPort("\\C"))
						special_pterms_inv[sigmap(cell->getPort("\\C")[0])].insert(
							tuple<Cell*, const char *>(cell, "\\C"));
					if (cell->hasPort("\\G"))
						special_pterms_inv[sigmap(cell->getPort("\\G")[0])].insert(
							tuple<Cell*, const char *>(cell, "\\G"));
				}
			}

			// Process $sop cells
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

					auto sop_output_wire_name = sop_output.wire->name.c_str();

					// Check for a $_NOT_ at the output
					bool has_invert = false;
					if (not_cells.count(sop_output))
					{
						auto not_cell = not_cells.at(sop_output);

						has_invert = true;
						sop_output = std::get<0>(not_cell);

						// remove the $_NOT_ cell because it gets folded into the xor
						cells_to_remove.insert(std::get<1>(not_cell));
					}

					// Check for special P-term usage
					bool is_special_pterm =
						special_pterms_no_inv.count(sop_output) || special_pterms_inv.count(sop_output);

					// Construct AND cells
					pool<SigBit> intermed_wires;
					for (int i = 0; i < sop_depth; i++) {
						// Wire for the output
						auto and_out = module->addWire(
							module->uniquify(stringf("$xc2sop$%s_AND%d_OUT", sop_output_wire_name, i)));
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
						auto and_cell = module->addCell(
							module->uniquify(stringf("$xc2sop$%s_AND%d", sop_output_wire_name, i)),
							"\\ANDTERM");
						and_cell->setParam("\\TRUE_INP", GetSize(and_in_true));
						and_cell->setParam("\\COMP_INP", GetSize(and_in_comp));
						and_cell->setPort("\\OUT", and_out);
						and_cell->setPort("\\IN", and_in_true);
						and_cell->setPort("\\IN_B", and_in_comp);
					}

					if (sop_depth == 1)
					{
						// If there is only one term, don't construct an OR cell. Directly construct the XOR gate
						auto xor_cell = module->addCell(
							module->uniquify(stringf("$xc2sop$%s_XOR", sop_output_wire_name)),
							"\\MACROCELL_XOR");
						xor_cell->setParam("\\INVERT_OUT", has_invert);
						xor_cell->setPort("\\IN_PTC", *intermed_wires.begin());
						xor_cell->setPort("\\OUT", sop_output);

						// Special P-term handling
						if (is_special_pterm)
						{
							// Can always connect the P-term directly if it's going
							// into something invert-capable
							for (auto x : special_pterms_inv[sop_output])
							{
								std::get<0>(x)->setPort(std::get<1>(x), *intermed_wires.begin());

								// If this signal is indeed inverted, flip the cell polarity
								if (has_invert)
								{
									auto cell = std::get<0>(x);
									if (cell->type == "\\FDCP") cell->type = "\\FDCP_N";
									else if (cell->type == "\\FDCP_N") cell->type = "\\FDCP";
									else if (cell->type == "\\FTCP") cell->type = "\\FTCP_N";
									else if (cell->type == "\\FTCP_N") cell->type = "\\FTCP";
									else if (cell->type == "\\FDCPE") cell->type = "\\FDCPE_N";
									else if (cell->type == "\\FDCPE_N") cell->type = "\\FDCPE";
									else if (cell->type == "\\LDCP") cell->type = "\\LDCP_N";
									else if (cell->type == "\\LDCP_N") cell->type = "\\LDCP";
									else log_assert(!"Internal error! Bad cell type!");
								}
							}

							// If it's going into something that's not invert-capable,
							// connect it directly only if this signal isn't inverted
							if (!has_invert)
							{
								for (auto x : special_pterms_no_inv[sop_output])
									std::get<0>(x)->setPort(std::get<1>(x), *intermed_wires.begin());
							}

							// Otherwise, a feedthrough P-term has to be created. Leave that to happen
							// in the coolrunner2_fixup pass.
						}
					}
					else
					{
						// Wire from OR to XOR
						auto or_to_xor_wire = module->addWire(
							module->uniquify(stringf("$xc2sop$%s_OR_OUT", sop_output_wire_name)));

						// Construct the OR cell
						auto or_cell = module->addCell(
							module->uniquify(stringf("$xc2sop$%s_OR", sop_output_wire_name)),
							"\\ORTERM");
						or_cell->setParam("\\WIDTH", sop_depth);
						or_cell->setPort("\\IN", intermed_wires);
						or_cell->setPort("\\OUT", or_to_xor_wire);

						// Construct the XOR cell
						auto xor_cell = module->addCell(
							module->uniquify(stringf("$xc2sop$%s_XOR", sop_output_wire_name)),
							"\\MACROCELL_XOR");
						xor_cell->setParam("\\INVERT_OUT", has_invert);
						xor_cell->setPort("\\IN_ORTERM", or_to_xor_wire);
						xor_cell->setPort("\\OUT", sop_output);
					}

					// Finally, remove the $sop cell
					cells_to_remove.insert(cell);
				}
			}

			// Actually do the removal now that we aren't iterating
			for (auto cell : cells_to_remove)
			{
				module->remove(cell);
			}
		}
	}
} Coolrunner2SopPass;

PRIVATE_NAMESPACE_END
