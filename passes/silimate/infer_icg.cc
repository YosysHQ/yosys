/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.
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

struct InferIcgPass : public Pass {
	InferIcgPass() : Pass("infer_icg", "infer $icg cells from latch-based clock gates") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    infer_icg [selection]\n");
		log("\n");
		log("This pass recognizes latch-based integrated clock gate structures and\n");
		log("replaces the gated-clock output with an internal $icg cell.\n");
		log("\n");
		log("The recognized positive-edge pattern is a one-bit $dlatch that is\n");
		log("transparent while the clock is low, feeding a one-bit $and or $logic_and\n");
		log("with the same clock. The latch can be active-low on the clock or\n");
		log("active-high on an inverted copy of the clock.\n");
		log("\n");
		log("The complementary high-idle pattern is also recognized: a latch that is\n");
		log("transparent while the clock is high, feeding a one-bit $or or $logic_or\n");
		log("with the same clock and an inverted latched enable. This is rewritten as\n");
		log("a $icg on the inverted clock plus an output inverter.\n");
		log("\n");
		log("The scan-enable leg is optional. If the effective latch data is driven\n");
		log("by a one-bit $or or $logic_or, its inputs are used as the $icg EN and\n");
		log("SE ports; otherwise the data is used as EN and SE is tied low.\n");
		log("\n");
	}

	static bool is_one_bit_binary(Cell *cell)
	{
		return cell->getParam(ID::A_WIDTH).as_int() == 1 &&
		       cell->getParam(ID::B_WIDTH).as_int() == 1 &&
		       cell->getParam(ID::Y_WIDTH).as_int() == 1;
	}

	static bool is_and(Cell *cell)
	{
		return cell->type.in(ID($and), ID($logic_and)) && is_one_bit_binary(cell);
	}

	static bool is_or(Cell *cell)
	{
		return cell->type.in(ID($or), ID($logic_or)) && is_one_bit_binary(cell);
	}

	static bool is_not(Cell *cell)
	{
		if (cell->type == ID($_NOT_))
			return true;
		return cell->type.in(ID($not), ID($logic_not)) &&
		       cell->getParam(ID::A_WIDTH).as_int() == 1 &&
		       cell->getParam(ID::Y_WIDTH).as_int() == 1;
	}

	static void add_driver(dict<SigBit, Cell *> &drivers, pool<SigBit> &multi_driver_bits, SigMap &sigmap, Cell *cell)
	{
		for (auto &conn : cell->connections()) {
			if (!cell->output(conn.first))
				continue;
			for (auto bit : sigmap(conn.second)) {
				if (bit.is_wire()) {
					if (drivers.count(bit) && drivers.at(bit) != cell)
						multi_driver_bits.insert(bit);
					else
						drivers[bit] = cell;
				}
			}
		}
	}

	static bool get_driver(dict<SigBit, Cell *> &drivers, pool<SigBit> &multi_driver_bits, SigMap &sigmap, SigSpec sig, Cell *&driver)
	{
		sig = sigmap(sig);
		if (GetSize(sig) != 1 || !sig[0].is_wire() || multi_driver_bits.count(sig[0]) || !drivers.count(sig[0]))
			return false;
		driver = drivers.at(sig[0]);
		return true;
	}

	static bool same_sig(SigMap &sigmap, SigSpec a, SigSpec b)
	{
		return sigmap(a) == sigmap(b);
	}

	static bool get_not_input(dict<SigBit, Cell *> &drivers, pool<SigBit> &multi_driver_bits, SigMap &sigmap,
			SigSpec sig, SigSpec &input, Cell *&not_cell)
	{
		Cell *driver = nullptr;
		if (!get_driver(drivers, multi_driver_bits, sigmap, sig, driver) || !is_not(driver))
			return false;

		not_cell = driver;
		input = sigmap(driver->getPort(ID::A));
		return true;
	}

	static bool latch_transparent_when(Cell *latch, SigSpec clk, bool high_when_transparent,
			dict<SigBit, Cell *> &drivers, pool<SigBit> &multi_driver_bits, SigMap &sigmap)
	{
		SigSpec latch_en = sigmap(latch->getPort(ID::EN));
		bool latch_en_pol = latch->getParam(ID::EN_POLARITY).as_bool();

		if (same_sig(sigmap, latch_en, clk))
			return latch_en_pol == high_when_transparent;

		SigSpec inv_input;
		Cell *not_cell = nullptr;
		if (get_not_input(drivers, multi_driver_bits, sigmap, latch_en, inv_input, not_cell) &&
		    same_sig(sigmap, inv_input, clk))
			return latch_en_pol != high_when_transparent;

		return false;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing INFER_ICG pass (infer $icg cells from latch-based clock gates).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
			break;
		extra_args(args, argidx, design);

		int total_count = 0;

		for (auto module : design->selected_modules()) {
			SigMap sigmap(module);
			dict<SigBit, Cell *> drivers;
			pool<SigBit> multi_driver_bits;
			dict<SigBit, int> users;
			pool<Cell *> selected_cells;

			for (auto wire : module->wires())
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						if (bit.is_wire())
							users[bit]++;

			for (auto cell : module->cells()) {
				if (design->selected(module, cell))
					selected_cells.insert(cell);

				add_driver(drivers, multi_driver_bits, sigmap, cell);

				for (auto &conn : cell->connections()) {
					if (!cell->input(conn.first))
						continue;
					for (auto bit : sigmap(conn.second))
						if (bit.is_wire())
							users[bit]++;
				}
			}

			struct Match {
				Cell *gate_cell;
				Cell *latch;
				Cell *enable_or_cell;
				SigSpec clk;
				SigSpec en;
				SigSpec se;
				SigSpec gclk;
				SigSpec latched_en;
				bool invert_clk_and_gclk;
			};
			std::vector<Match> matches;
			pool<Cell *> consumed_gate_cells;

			for (auto gate_cell : module->selected_cells()) {
				if (consumed_gate_cells.count(gate_cell) || (!is_and(gate_cell) && !is_or(gate_cell)))
					continue;

				bool gate_is_and = is_and(gate_cell);
				SigSpec gate_a = sigmap(gate_cell->getPort(ID::A));
				SigSpec gate_b = sigmap(gate_cell->getPort(ID::B));
				SigSpec gclk = gate_cell->getPort(ID::Y);

				for (int clk_port = 0; clk_port < 2; clk_port++) {
					SigSpec clk = clk_port == 0 ? gate_a : gate_b;
					SigSpec latched_en = clk_port == 0 ? gate_b : gate_a;
					Cell *latch = nullptr;
					bool invert_clk_and_gclk = false;

					if (!gate_is_and) {
						SigSpec not_input;
						Cell *not_cell = nullptr;
						if (!get_not_input(drivers, multi_driver_bits, sigmap, latched_en, not_input, not_cell))
							continue;
						latched_en = not_input;
						invert_clk_and_gclk = true;
					}

					if (!get_driver(drivers, multi_driver_bits, sigmap, latched_en, latch))
						continue;
					if (!selected_cells.count(latch) || latch->type != ID($dlatch))
						continue;
					if (latch->getParam(ID::WIDTH).as_int() != 1)
						continue;

					if (!latch_transparent_when(latch, clk, !gate_is_and, drivers, multi_driver_bits, sigmap))
						continue;

					SigSpec latch_d = sigmap(latch->getPort(ID::D));
					SigSpec en = latch_d, se = State::S0;
					Cell *enable_or_cell = nullptr;

					if (get_driver(drivers, multi_driver_bits, sigmap, latch_d, enable_or_cell) &&
					    selected_cells.count(enable_or_cell) && is_or(enable_or_cell)) {
						en = sigmap(enable_or_cell->getPort(ID::A));
						se = sigmap(enable_or_cell->getPort(ID::B));
					} else {
						enable_or_cell = nullptr;
					}

					matches.push_back({gate_cell, latch, enable_or_cell, clk, en, se, gclk, latched_en, invert_clk_and_gclk});
					consumed_gate_cells.insert(gate_cell);
					break;
				}
			}

			for (auto &match : matches) {
				Cell *cell = match.gate_cell;
				Cell *icg = module->addCell(NEW_ID2_SUFFIX("icg"), ID($icg));
				SigSpec icg_clk = match.clk;
				SigSpec icg_gclk = match.gclk;

				if (match.invert_clk_and_gclk) {
					icg_clk = module->Not(NEW_ID2_SUFFIX("icg_clk_n"), match.clk);
					icg_gclk = module->addWire(NEW_ID2_SUFFIX("icg_gclk"));
				}

				icg->setPort(ID::CLK, icg_clk);
				icg->setPort(ID::EN, match.en);
				icg->setPort(ID::SE, match.se);
				icg->setPort(ID::GCLK, icg_gclk);
				icg->add_strpool_attribute(ID::src, match.gate_cell->get_strpool_attribute(ID::src));
				icg->add_strpool_attribute(ID::src, match.latch->get_strpool_attribute(ID::src));
				if (match.enable_or_cell)
					icg->add_strpool_attribute(ID::src, match.enable_or_cell->get_strpool_attribute(ID::src));

				if (match.invert_clk_and_gclk)
					module->addNot(NEW_ID2_SUFFIX("icg_gclk_n"), icg_gclk, match.gclk, false, match.gate_cell->get_src_attribute());

				log("Inferred $icg cell %s.%s from latch %s and gate %s.\n",
				    log_id(module), log_id(icg), log_id(match.latch), log_id(match.gate_cell));

				module->remove(match.gate_cell);

				SigSpec latched_en = sigmap(match.latched_en);
				if (GetSize(latched_en) == 1 && latched_en[0].is_wire() && users[latched_en[0]] == 1) {
					module->remove(match.latch);

					if (match.enable_or_cell) {
						SigSpec or_y = sigmap(match.enable_or_cell->getPort(ID::Y));
						if (GetSize(or_y) == 1 && or_y[0].is_wire() && users[or_y[0]] == 1)
							module->remove(match.enable_or_cell);
					}
				}

				total_count++;
			}
		}

		log("Inferred %d $icg cells.\n", total_count);
	}
} InferIcgPass;

PRIVATE_NAMESPACE_END
