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

RTLIL::Wire *makexorbuffer(RTLIL::Module *module, SigBit inwire)
{
	auto outwire = module->addWire(NEW_ID);

	if (inwire == SigBit(true))
	{
		// Constant 1
		auto xor_cell = module->addCell(NEW_ID, "\\MACROCELL_XOR");
		xor_cell->setParam("\\INVERT_OUT", true);
		xor_cell->setPort("\\OUT", outwire);
	}
	else if (inwire == SigBit(false))
	{
		// Constant 0
		auto xor_cell = module->addCell(NEW_ID, "\\MACROCELL_XOR");
		xor_cell->setParam("\\INVERT_OUT", false);
		xor_cell->setPort("\\OUT", outwire);
	}
	else
	{
		auto and_to_xor_wire = module->addWire(NEW_ID);

		auto and_cell = module->addCell(NEW_ID, "\\ANDTERM");
		and_cell->setParam("\\TRUE_INP", 1);
		and_cell->setParam("\\COMP_INP", 0);
		and_cell->setPort("\\OUT", and_to_xor_wire);
		and_cell->setPort("\\IN", inwire);
		and_cell->setPort("\\IN_B", SigSpec());

		auto xor_cell = module->addCell(NEW_ID, "\\MACROCELL_XOR");
		xor_cell->setParam("\\INVERT_OUT", false);
		xor_cell->setPort("\\IN_PTC", and_to_xor_wire);
		xor_cell->setPort("\\OUT", outwire);
	}

	return outwire;
}

RTLIL::Wire *makeptermbuffer(RTLIL::Module *module, SigBit inwire)
{
	auto outwire = module->addWire(NEW_ID);

	auto and_cell = module->addCell(NEW_ID, "\\ANDTERM");
	and_cell->setParam("\\TRUE_INP", 1);
	and_cell->setParam("\\COMP_INP", 0);
	and_cell->setPort("\\OUT", outwire);
	and_cell->setPort("\\IN", inwire);
	and_cell->setPort("\\IN_B", SigSpec());

	return outwire;
}

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

			// Find all the pterm outputs
			pool<SigBit> sig_fed_by_pterm;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\ANDTERM")
				{
					auto output = sigmap(cell->getPort("\\OUT")[0]);
					sig_fed_by_pterm.insert(output);
				}
			}

			// Find all the bufg outputs
			pool<SigBit> sig_fed_by_bufg;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\BUFG")
				{
					auto output = sigmap(cell->getPort("\\O")[0]);
					sig_fed_by_bufg.insert(output);
				}
			}

			// Find all the bufgsr outputs
			pool<SigBit> sig_fed_by_bufgsr;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\BUFGSR")
				{
					auto output = sigmap(cell->getPort("\\O")[0]);
					sig_fed_by_bufgsr.insert(output);
				}
			}

			// Find all the bufgts outputs
			pool<SigBit> sig_fed_by_bufgts;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\BUFGTS")
				{
					auto output = sigmap(cell->getPort("\\O")[0]);
					sig_fed_by_bufgts.insert(output);
				}
			}

			for (auto cell : module->selected_cells())
			{
				if (cell->type.in("\\FDCP", "\\FDCP_N", "\\FDDCP", "\\LDCP", "\\LDCP_N",
							"\\FTCP", "\\FTCP_N", "\\FTDCP", "\\FDCPE", "\\FDCPE_N", "\\FDDCPE"))
				{
					// Buffering FF inputs. FF inputs can only come from either
					// an IO pin or from an XOR. Otherwise AND/XOR cells need
					// to be inserted.
					SigBit input;
					if (cell->type.in("\\FTCP", "\\FTCP_N", "\\FTDCP"))
						input = sigmap(cell->getPort("\\T")[0]);
					else
						input = sigmap(cell->getPort("\\D")[0]);

					if (!sig_fed_by_xor[input] && !sig_fed_by_io[input])
					{
						log("Buffering input to \"%s\"\n", cell->name.c_str());

						auto xor_to_ff_wire = makexorbuffer(module, input);

						if (cell->type.in("\\FTCP", "\\FTCP_N", "\\FTDCP"))
							cell->setPort("\\T", xor_to_ff_wire);
						else
							cell->setPort("\\D", xor_to_ff_wire);
					}

					// Buffering FF clocks. FF clocks can only come from either
					// a pterm or a bufg. In some cases this will be handled
					// in coolrunner2_sop (e.g. if clock is generated from
					// AND-ing two signals) but not in all cases.
					SigBit clock;
					if (cell->type.in("\\LDCP", "\\LDCP_N"))
						clock = sigmap(cell->getPort("\\G")[0]);
					else
						clock = sigmap(cell->getPort("\\C")[0]);

					if (!sig_fed_by_pterm[clock] && !sig_fed_by_bufg[clock])
					{
						log("Buffering clock to \"%s\"\n", cell->name.c_str());

						auto pterm_to_ff_wire = makeptermbuffer(module, clock);

						if (cell->type.in("\\LDCP", "\\LDCP_N"))
							cell->setPort("\\G", pterm_to_ff_wire);
						else
							cell->setPort("\\C", pterm_to_ff_wire);
					}

					// Buffering FF set/reset. This can only come from either
					// a pterm or a bufgsr.
					SigBit set;
					set = sigmap(cell->getPort("\\PRE")[0]);
					if (set != SigBit(false))
					{
						if (!sig_fed_by_pterm[set] && !sig_fed_by_bufgsr[set])
						{
							log("Buffering set to \"%s\"\n", cell->name.c_str());

							auto pterm_to_ff_wire = makeptermbuffer(module, set);

							cell->setPort("\\PRE", pterm_to_ff_wire);
						}
					}

					SigBit reset;
					reset = sigmap(cell->getPort("\\CLR")[0]);
					if (reset != SigBit(false))
					{
						if (!sig_fed_by_pterm[reset] && !sig_fed_by_bufgsr[reset])
						{
							log("Buffering reset to \"%s\"\n", cell->name.c_str());

							auto pterm_to_ff_wire = makeptermbuffer(module, reset);

							cell->setPort("\\CLR", pterm_to_ff_wire);
						}
					}

					// Buffering FF clock enable
					// FIXME: This doesn't fully fix PTC conflicts
					// FIXME: Need to ensure constant enables are optimized out
					if (cell->type.in("\\FDCPE", "\\FDCPE_N", "\\FDDCPE"))
					{
						SigBit ce;
						ce = sigmap(cell->getPort("\\CE")[0]);
						if (!sig_fed_by_pterm[ce])
						{
							log("Buffering clock enable to \"%s\"\n", cell->name.c_str());

							auto pterm_to_ff_wire = makeptermbuffer(module, ce);

							cell->setPort("\\CE", pterm_to_ff_wire);
						}
					}
				}
			}

			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\IOBUFE")
				{
					// Buffer IOBUFE inputs. This can only be fed from an XOR or FF.
					SigBit input = sigmap(cell->getPort("\\I")[0]);

					if (!sig_fed_by_xor[input] && !sig_fed_by_ff[input])
					{
						log("Buffering input to \"%s\"\n", cell->name.c_str());

						auto xor_to_io_wire = makexorbuffer(module, input);

						cell->setPort("\\I", xor_to_io_wire);
					}

					// Buffer IOBUFE enables. This can only be fed from a pterm
					// or a bufgts.
					if (cell->hasPort("\\E"))
					{
						SigBit oe;
						oe = sigmap(cell->getPort("\\E")[0]);
						if (!sig_fed_by_pterm[oe] && !sig_fed_by_bufgts[oe])
						{
							log("Buffering output enable to \"%s\"\n", cell->name.c_str());

							auto pterm_to_oe_wire = makeptermbuffer(module, oe);

							cell->setPort("\\E", pterm_to_oe_wire);
						}
					}
				}
			}
		}
	}
} Coolrunner2FixupPass;

PRIVATE_NAMESPACE_END
