/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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
#include "kernel/satgen.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EquivSimpleWorker
{
	Module *module;
	Cell *equiv_cell;

	SigMap &sigmap;
	dict<SigBit, Cell*> &bit2driver;

	ezDefaultSAT ez;
	SatGen satgen;

	EquivSimpleWorker(Cell *equiv_cell, SigMap &sigmap, dict<SigBit, Cell*> &bit2driver) :
			module(equiv_cell->module), equiv_cell(equiv_cell), sigmap(sigmap),
			bit2driver(bit2driver), satgen(&ez, &sigmap)
	{
	}

	void find_input_cone(pool<Cell*> &cells_cone, pool<SigBit> &bits_cone, const pool<Cell*> &cells_stop, const pool<SigBit> &bits_stop, Cell *cell)
	{
		if (cells_cone.count(cell))
			return;

		cells_cone.insert(cell);

		if (cells_stop.count(cell))
			return;

		for (auto &conn : cell->connections())
			if (yosys_celltypes.cell_input(cell->type, conn.first))
				for (auto bit : sigmap(conn.second))
					find_input_cone(cells_cone, bits_cone, cells_stop, bits_stop, bit);
	}

	void find_input_cone(pool<Cell*> &cells_cone, pool<SigBit> &bits_cone, const pool<Cell*> &cells_stop, const pool<SigBit> &bits_stop, SigBit bit)
	{
		if (bits_cone.count(bit))
			return;

		bits_cone.insert(bit);

		if (bits_stop.count(bit))
			return;

		if (!bit2driver.count(bit))
			return;

		find_input_cone(cells_cone, bits_cone, cells_stop, bits_stop, bit2driver.at(bit));
	}

	bool run()
	{
		SigBit bit_a = sigmap(equiv_cell->getPort("\\A")).to_single_sigbit();
		SigBit bit_b = sigmap(equiv_cell->getPort("\\B")).to_single_sigbit();

		log("  Trying to prove $equiv cell %s:\n", log_id(equiv_cell));
		log("    A = %s, B = %s, Y = %s\n", log_signal(bit_a), log_signal(bit_b), log_signal(equiv_cell->getPort("\\Y")));

		pool<Cell*> no_stop_cells;
		pool<SigBit> no_stop_bits;

		pool<Cell*> full_cells_cone_a, full_cells_cone_b;
		pool<SigBit> full_bits_cone_a, full_bits_cone_b;

		find_input_cone(full_cells_cone_a, full_bits_cone_a, no_stop_cells, no_stop_bits, bit_a);
		find_input_cone(full_cells_cone_b, full_bits_cone_b, no_stop_cells, no_stop_bits, bit_b);

		pool<Cell*> short_cells_cone_a, short_cells_cone_b;
		pool<SigBit> short_bits_cone_a, short_bits_cone_b;

		find_input_cone(short_cells_cone_a, short_bits_cone_a, full_cells_cone_b, full_bits_cone_b, bit_a);
		find_input_cone(short_cells_cone_b, short_bits_cone_b, full_cells_cone_a, full_bits_cone_a, bit_b);

		pool<Cell*> problem_cells;
		problem_cells.insert(short_cells_cone_a.begin(), short_cells_cone_a.end());
		problem_cells.insert(short_cells_cone_b.begin(), short_cells_cone_b.end());
		for (auto cell : problem_cells) satgen.importCell(cell);

		int ez_a = satgen.importSigBit(bit_a);
		int ez_b = satgen.importSigBit(bit_b);
		ez.assume(ez.XOR(ez_a, ez_b));

		log("    Created SAT problem from %d cells.\n", GetSize(problem_cells));

		if (!ez.solve()) {
			log("    Proved equivalence! Marking $equiv cell as proven.\n");
			equiv_cell->setPort("\\B", equiv_cell->getPort("\\A"));
			return true;
		}

		log("    Failed to prove equivalence.\n");
		return false;
	}
};

struct EquivSimplePass : public Pass {
	EquivSimplePass() : Pass("equiv_simple", "try proving simple $equiv instances") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_simple [options] [selection]\n");
		log("\n");
		log("This command tries to prove $equiv cells using a simple direct SAT approach.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		int success_counter = 0;

		log_header("Executing EQUIV_SIMPLE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-assert") {
			// 	assert_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();

		for (auto module : design->selected_modules())
		{
			vector<Cell*> unproven_equiv_cells;

			for (auto cell : module->selected_cells())
				if (cell->type == "$equiv" && cell->getPort("\\A") != cell->getPort("\\B"))
						unproven_equiv_cells.push_back(cell);

			if (unproven_equiv_cells.empty())
				continue;

			log("Found %d unproven $equiv cells in %s:\n", GetSize(unproven_equiv_cells), log_id(module));

			SigMap sigmap(module);
			dict<SigBit, Cell*> bit2driver;

			for (auto cell : module->selected_cells()) {
				if (!ct.cell_known(cell->type))
					continue;
				for (auto &conn : cell->connections())
					if (ct.cell_output(cell->type, conn.first))
						for (auto bit : sigmap(conn.second))
							bit2driver[bit] = cell;
			}

			for (auto cell : unproven_equiv_cells) {
				EquivSimpleWorker worker(cell, sigmap, bit2driver);
				if (worker.run())
					success_counter++;
			}
		}

		log("Successfully proved %d previously unproven $equiv cells.\n", success_counter);
	}
} EquivSimplePass;

PRIVATE_NAMESPACE_END
