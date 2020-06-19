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
	void help() override
	{
		log("\n");
		log("    coolrunner2_sop [options] [selection]\n");
		log("\n");
		log("Break $sop cells into ANDTERM/ORTERM cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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
				if (cell->type == ID($_NOT_))
				{
					auto not_input = sigmap(cell->getPort(ID::A)[0]);
					auto not_output = sigmap(cell->getPort(ID::Y)[0]);
					not_cells[not_input] = tuple<SigBit, Cell*>(not_output, cell);
				}
			}

			// Find wires that need to become special product terms
			dict<SigBit, pool<tuple<Cell*, IdString>>> special_pterms_no_inv;
			dict<SigBit, pool<tuple<Cell*, IdString>>> special_pterms_inv;
			for (auto cell : module->selected_cells())
			{
				if (cell->type.in(ID(FDCP), ID(FDCP_N), ID(FDDCP), ID(FTCP), ID(FTCP_N), ID(FTDCP),
							ID(FDCPE), ID(FDCPE_N), ID(FDDCPE), ID(LDCP), ID(LDCP_N)))
				{
					if (cell->hasPort(ID(PRE)))
						special_pterms_no_inv[sigmap(cell->getPort(ID(PRE))[0])].insert(
							make_tuple(cell, ID(PRE)));
					if (cell->hasPort(ID::CLR))
						special_pterms_no_inv[sigmap(cell->getPort(ID::CLR)[0])].insert(
							make_tuple(cell, ID::CLR));
					if (cell->hasPort(ID(CE)))
						special_pterms_no_inv[sigmap(cell->getPort(ID(CE))[0])].insert(
							make_tuple(cell, ID(CE)));

					if (cell->hasPort(ID::C))
						special_pterms_inv[sigmap(cell->getPort(ID::C)[0])].insert(
							make_tuple(cell, ID::C));
					if (cell->hasPort(ID::G))
						special_pterms_inv[sigmap(cell->getPort(ID::G)[0])].insert(
							make_tuple(cell, ID::G));
				}
			}

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
							ID(ANDTERM));
						and_cell->setParam(ID(TRUE_INP), GetSize(and_in_true));
						and_cell->setParam(ID(COMP_INP), GetSize(and_in_comp));
						and_cell->setPort(ID(OUT), and_out);
						and_cell->setPort(ID(IN), and_in_true);
						and_cell->setPort(ID(IN_B), and_in_comp);
					}

					if (sop_depth == 1)
					{
						// If there is only one term, don't construct an OR cell. Directly construct the XOR gate
						auto xor_cell = module->addCell(
							module->uniquify(stringf("$xc2sop$%s_XOR", sop_output_wire_name)),
							ID(MACROCELL_XOR));
						xor_cell->setParam(ID(INVERT_OUT), has_invert);
						xor_cell->setPort(ID(IN_PTC), *intermed_wires.begin());
						xor_cell->setPort(ID(OUT), sop_output);

						// Special P-term handling
						if (is_special_pterm)
						{
							// Can always connect the P-term directly if it's going
							// into something invert-capable
							for (const auto &x : special_pterms_inv[sop_output])
							{
								std::get<0>(x)->setPort(std::get<1>(x), *intermed_wires.begin());

								// If this signal is indeed inverted, flip the cell polarity
								if (has_invert)
								{
									auto cell = std::get<0>(x);
									if (cell->type == ID(FDCP)) cell->type = ID(FDCP_N);
									else if (cell->type == ID(FDCP_N)) cell->type = ID(FDCP);
									else if (cell->type == ID(FTCP)) cell->type = ID(FTCP_N);
									else if (cell->type == ID(FTCP_N)) cell->type = ID(FTCP);
									else if (cell->type == ID(FDCPE)) cell->type = ID(FDCPE_N);
									else if (cell->type == ID(FDCPE_N)) cell->type = ID(FDCPE);
									else if (cell->type == ID(LDCP)) cell->type = ID(LDCP_N);
									else if (cell->type == ID(LDCP_N)) cell->type = ID(LDCP);
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
							ID(ORTERM));
						or_cell->setParam(ID::WIDTH, sop_depth);
						or_cell->setPort(ID(IN), intermed_wires);
						or_cell->setPort(ID(OUT), or_to_xor_wire);

						// Construct the XOR cell
						auto xor_cell = module->addCell(
							module->uniquify(stringf("$xc2sop$%s_XOR", sop_output_wire_name)),
							ID(MACROCELL_XOR));
						xor_cell->setParam(ID(INVERT_OUT), has_invert);
						xor_cell->setPort(ID(IN_ORTERM), or_to_xor_wire);
						xor_cell->setPort(ID(OUT), sop_output);
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
