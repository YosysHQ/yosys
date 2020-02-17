/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020 R. Ou <rqou@robertou.com>
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

struct Coolrunner2FixupPass : public Pass {
	Coolrunner2FixupPass() : Pass("coolrunner2_fixup", "insert necessary buffer cells for CoolRunner-II architecture") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    coolrunner2_fixup [options] [selection]\n");
		log("\n");
		log("Insert necessary buffer cells for CoolRunner-II architecture.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing COOLRUNNER2_FIXUP pass (insert necessary buffer cells for CoolRunner-II architecture).\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);

			// Find all the FF outputs
			pool<SigBit> sig_fed_by_ff;
			for (auto cell : module->selected_cells())
			{
				if (cell->type.in("\\FDCP", "\\FDCP_N", "\\FDDCP", "\\LDCP", "\\LDCP_N",
							"\\FTCP", "\\FTCP_N", "\\FTDCP", "\\FDCPE", "\\FDCPE_N", "\\FDDCPE"))
				{
					auto output = sigmap(cell->getPort("\\Q")[0]);
					sig_fed_by_ff.insert(output);
				}
			}

			// Find all the XOR outputs
			pool<SigBit> sig_fed_by_xor;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\MACROCELL_XOR")
				{
					auto output = sigmap(cell->getPort("\\OUT")[0]);
					sig_fed_by_xor.insert(output);
				}
			}

			// Find all the input/inout outputs
			pool<SigBit> sig_fed_by_io;
			for (auto cell : module->selected_cells())
			{
				if (cell->type.in("\\IBUF", "\\IOBUFE"))
				{
					if (cell->hasPort("\\O")) {
						auto output = sigmap(cell->getPort("\\O")[0]);
						sig_fed_by_io.insert(output);
					}
				}
			}

			// Start by buffering FF inputs. FF inputs can only come from either
			// an IO pin or from an XOR. Otherwise AND/XOR cells need to be inserted.
			for (auto cell : module->selected_cells())
			{
				if (cell->type.in("\\FDCP", "\\FDCP_N", "\\FDDCP", "\\LDCP", "\\LDCP_N",
							"\\FTCP", "\\FTCP_N", "\\FTDCP", "\\FDCPE", "\\FDCPE_N", "\\FDDCPE"))
				{
					SigBit input;
					if (cell->type.in("\\FTCP", "\\FTCP_N", "\\FTDCP"))
						input = sigmap(cell->getPort("\\T")[0]);
					else
						input = sigmap(cell->getPort("\\D")[0]);

					if (!sig_fed_by_xor[input] && !sig_fed_by_io[input])
					{
						log("Buffering input to \"%s\"\n", cell->name.c_str());

						auto and_to_xor_wire = module->addWire(NEW_ID);
						auto xor_to_ff_wire = module->addWire(NEW_ID);

						auto and_cell = module->addCell(NEW_ID, "\\ANDTERM");
						and_cell->setParam("\\TRUE_INP", 1);
						and_cell->setParam("\\COMP_INP", 0);
						and_cell->setPort("\\OUT", and_to_xor_wire);
						and_cell->setPort("\\IN", input);
						and_cell->setPort("\\IN_B", SigSpec());

						auto xor_cell = module->addCell(NEW_ID, "\\MACROCELL_XOR");
						xor_cell->setParam("\\INVERT_OUT", false);
						xor_cell->setPort("\\IN_PTC", and_to_xor_wire);
						xor_cell->setPort("\\OUT", xor_to_ff_wire);

						if (cell->type.in("\\FTCP", "\\FTCP_N", "\\FTDCP"))
							cell->setPort("\\T", xor_to_ff_wire);
						else
							cell->setPort("\\D", xor_to_ff_wire);
					}
				}
			}

			// Buffer IOBUFE inputs. This can only be fed from an XOR or FF.
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\IOBUFE")
				{
					SigBit input = sigmap(cell->getPort("\\I")[0]);

					// Special case: constant 0 and 1 are handled by xc2par
					if (input == SigBit(true) || input == SigBit(false)) {
						log("Not buffering constant IO to \"%s\"\n", cell->name.c_str());
						continue;
					}

					if (!sig_fed_by_xor[input] && !sig_fed_by_ff[input])
					{
						log("Buffering input to \"%s\"\n", cell->name.c_str());

						auto and_to_xor_wire = module->addWire(NEW_ID);
						auto xor_to_io_wire = module->addWire(NEW_ID);

						auto and_cell = module->addCell(NEW_ID, "\\ANDTERM");
						and_cell->setParam("\\TRUE_INP", 1);
						and_cell->setParam("\\COMP_INP", 0);
						and_cell->setPort("\\OUT", and_to_xor_wire);
						and_cell->setPort("\\IN", input);
						and_cell->setPort("\\IN_B", SigSpec());

						auto xor_cell = module->addCell(NEW_ID, "\\MACROCELL_XOR");
						xor_cell->setParam("\\INVERT_OUT", false);
						xor_cell->setPort("\\IN_PTC", and_to_xor_wire);
						xor_cell->setPort("\\OUT", xor_to_io_wire);

						cell->setPort("\\I", xor_to_io_wire);
					}
				}
			}
		}
	}
} Coolrunner2FixupPass;

PRIVATE_NAMESPACE_END
