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

RTLIL::Wire *makexorbuffer(RTLIL::Module *module, SigBit inwire, const char *cellname)
{
	RTLIL::Wire *outwire = nullptr;

	if (inwire == SigBit(true))
	{
		// Constant 1
		outwire = module->addWire(
			module->uniquify(stringf("$xc2fix$%s_BUF1_XOR_OUT", cellname)));
		auto xor_cell = module->addCell(
			module->uniquify(stringf("$xc2fix$%s_BUF1_XOR", cellname)),
			"\\MACROCELL_XOR");
		xor_cell->setParam("\\INVERT_OUT", true);
		xor_cell->setPort("\\OUT", outwire);
	}
	else if (inwire == SigBit(false))
	{
		// Constant 0
		outwire = module->addWire(
			module->uniquify(stringf("$xc2fix$%s_BUF0_XOR_OUT", cellname)));
		auto xor_cell = module->addCell(
			module->uniquify(stringf("$xc2fix$%s_BUF0_XOR", cellname)),
			"\\MACROCELL_XOR");
		xor_cell->setParam("\\INVERT_OUT", false);
		xor_cell->setPort("\\OUT", outwire);
	}
	else if (inwire == SigBit(RTLIL::State::Sx))
	{
		// x; treat as 0
		log_warning("While buffering, changing x to 0 into cell %s\n", cellname);
		outwire = module->addWire(
			module->uniquify(stringf("$xc2fix$%s_BUF0_XOR_OUT", cellname)));
		auto xor_cell = module->addCell(
			module->uniquify(stringf("$xc2fix$%s_BUF0_XOR", cellname)),
			"\\MACROCELL_XOR");
		xor_cell->setParam("\\INVERT_OUT", false);
		xor_cell->setPort("\\OUT", outwire);
	}
	else
	{
		auto inwire_name = inwire.wire->name.c_str();

		outwire = module->addWire(
			module->uniquify(stringf("$xc2fix$%s_BUF_XOR_OUT", inwire_name)));

		auto and_to_xor_wire = module->addWire(
			module->uniquify(stringf("$xc2fix$%s_BUF_AND_OUT", inwire_name)));

		auto and_cell = module->addCell(
			module->uniquify(stringf("$xc2fix$%s_BUF_AND", inwire_name)),
			"\\ANDTERM");
		and_cell->setParam("\\TRUE_INP", 1);
		and_cell->setParam("\\COMP_INP", 0);
		and_cell->setPort("\\OUT", and_to_xor_wire);
		and_cell->setPort("\\IN", inwire);
		and_cell->setPort("\\IN_B", SigSpec());

		auto xor_cell = module->addCell(
			module->uniquify(stringf("$xc2fix$%s_BUF_XOR", inwire_name)),
			"\\MACROCELL_XOR");
		xor_cell->setParam("\\INVERT_OUT", false);
		xor_cell->setPort("\\IN_PTC", and_to_xor_wire);
		xor_cell->setPort("\\OUT", outwire);
	}

	return outwire;
}

RTLIL::Wire *makeptermbuffer(RTLIL::Module *module, SigBit inwire)
{
	auto inwire_name = inwire.wire->name.c_str();

	auto outwire = module->addWire(
		module->uniquify(stringf("$xc2fix$%s_BUF_AND_OUT", inwire_name)));

	auto and_cell = module->addCell(
		module->uniquify(stringf("$xc2fix$%s_BUF_AND", inwire_name)),
		"\\ANDTERM");
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

			// This is used to fix the input -> FF -> output scenario
			pool<SigBit> sig_fed_by_ibuf;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\IBUF")
				{
					auto output = sigmap(cell->getPort("\\O")[0]);
					sig_fed_by_ibuf.insert(output);
				}
			}

			// Find all of the sinks for each output from an IBUF
			dict<SigBit, std::pair<int, RTLIL::Cell *>> ibuf_fanouts;
			for (auto cell : module->selected_cells())
			{
				for (auto &conn : cell->connections())
				{
					if (cell->input(conn.first))
					{
						for (auto wire_in : sigmap(conn.second))
						{
							if (sig_fed_by_ibuf[wire_in])
							{
								auto existing_count = ibuf_fanouts[wire_in].first;
								ibuf_fanouts[wire_in] =
									std::pair<int, RTLIL::Cell *>(existing_count + 1, cell);
							}
						}
					}
				}
			}

			dict<SigBit, RTLIL::Cell *> ibuf_out_to_packed_reg_cell;
			pool<SigBit> packed_reg_out;
			for (auto x : ibuf_fanouts)
			{
				auto ibuf_out_wire = x.first;
				auto fanout_count = x.second.first;
				auto maybe_ff_cell = x.second.second;

				// The register can be packed with the IBUF only if it's
				// actually a register and it's the only fanout. Otherwise,
				// the pad-to-zia path has to be used up and the register
				// can't be packed with the ibuf.
				if (fanout_count == 1 && maybe_ff_cell->type.in(
					"\\FDCP", "\\FDCP_N", "\\FDDCP", "\\LDCP", "\\LDCP_N",
					"\\FTCP", "\\FTCP_N", "\\FTDCP", "\\FDCPE", "\\FDCPE_N", "\\FDDCPE"))
				{
					SigBit input;
					if (maybe_ff_cell->type.in("\\FTCP", "\\FTCP_N", "\\FTDCP"))
						input = sigmap(maybe_ff_cell->getPort("\\T")[0]);
					else
						input = sigmap(maybe_ff_cell->getPort("\\D")[0]);
					SigBit output = sigmap(maybe_ff_cell->getPort("\\Q")[0]);

					if (input == ibuf_out_wire)
					{
						log("Found IBUF %s that can be packed with FF %s (type %s)\n",
							ibuf_out_wire.wire->name.c_str(),
							maybe_ff_cell->name.c_str(),
							maybe_ff_cell->type.c_str());

						ibuf_out_to_packed_reg_cell[ibuf_out_wire] = maybe_ff_cell;
						packed_reg_out.insert(output);
					}
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

					// If the input wasn't an XOR nor an IO, then a buffer
					// definitely needs to be added.
					// Otherwise, if it is an IO, only leave unbuffered
					// if we're being packed with the IO.
					if ((!sig_fed_by_xor[input] && !sig_fed_by_io[input]) ||
						(sig_fed_by_io[input] && ibuf_out_to_packed_reg_cell[input] != cell))
					{
						log("Buffering input to \"%s\"\n", cell->name.c_str());

						auto xor_to_ff_wire = makexorbuffer(module, input, cell->name.c_str());

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

					if ((!sig_fed_by_xor[input] && !sig_fed_by_ff[input]) ||
						packed_reg_out[input])
					{
						log("Buffering input to \"%s\"\n", cell->name.c_str());

						auto xor_to_io_wire = makexorbuffer(module, input, cell->name.c_str());

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

			// Now we have to fix up some cases where shared logic can
			// cause XORs to have multiple fanouts to something other than
			// pterms (which is not ok)

			// Find all the XOR outputs
			dict<SigBit, RTLIL::Cell *> xor_out_to_xor_cell;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\MACROCELL_XOR")
				{
					auto output = sigmap(cell->getPort("\\OUT")[0]);
					xor_out_to_xor_cell[output] = cell;
				}
			}

			// Find all of the sinks for each output from an XOR
			pool<SigBit> xor_fanout_once;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\ANDTERM")
					continue;

				for (auto &conn : cell->connections())
				{
					if (cell->input(conn.first))
					{
						for (auto wire_in : sigmap(conn.second))
						{
							auto xor_cell = xor_out_to_xor_cell[wire_in];
							if (xor_cell)
							{
								if (xor_fanout_once[wire_in])
								{
									log("Additional fanout found for %s into %s (type %s), duplicating\n",
										xor_cell->name.c_str(),
										cell->name.c_str(),
										cell->type.c_str());

									auto new_xor_cell = module->addCell(
										module->uniquify(xor_cell->name), xor_cell);
									auto new_wire = module->addWire(
										module->uniquify(wire_in.wire->name));
									new_xor_cell->setPort("\\OUT", new_wire);
									cell->setPort(conn.first, new_wire);
								}
								xor_fanout_once.insert(wire_in);
							}
						}
					}
				}
			}

			// Do the same fanout fixing for OR terms. By doing this
			// after doing XORs, both pieces will be duplicated when necessary.

			// Find all the OR outputs
			dict<SigBit, RTLIL::Cell *> or_out_to_or_cell;
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\ORTERM")
				{
					auto output = sigmap(cell->getPort("\\OUT")[0]);
					or_out_to_or_cell[output] = cell;
				}
			}

			// Find all of the sinks for each output from an OR
			pool<SigBit> or_fanout_once;
			for (auto cell : module->selected_cells())
			{
				for (auto &conn : cell->connections())
				{
					if (cell->input(conn.first))
					{
						for (auto wire_in : sigmap(conn.second))
						{
							auto or_cell = or_out_to_or_cell[wire_in];
							if (or_cell)
							{
								if (or_fanout_once[wire_in])
								{
									log("Additional fanout found for %s into %s (type %s), duplicating\n",
										or_cell->name.c_str(),
										cell->name.c_str(),
										cell->type.c_str());

									auto new_or_cell = module->addCell(
										module->uniquify(or_cell->name), or_cell);
									auto new_wire = module->addWire(
										module->uniquify(wire_in.wire->name));
									new_or_cell->setPort("\\OUT", new_wire);
									cell->setPort(conn.first, new_wire);
								}
								or_fanout_once.insert(wire_in);
							}
						}
					}
				}
			}
		}
	}
} Coolrunner2FixupPass;

PRIVATE_NAMESPACE_END
