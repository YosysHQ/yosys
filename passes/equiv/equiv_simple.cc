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
	int max_seq;
	bool verbose;

	EquivSimpleWorker(Cell *equiv_cell, SigMap &sigmap, dict<SigBit, Cell*> &bit2driver, int max_seq, bool verbose, bool model_undef) :
			module(equiv_cell->module), equiv_cell(equiv_cell), sigmap(sigmap),
			bit2driver(bit2driver), satgen(&ez, &sigmap), max_seq(max_seq), verbose(verbose)
	{
		satgen.model_undef = model_undef;
	}

	bool find_input_cone(pool<SigBit> &next_seed, pool<Cell*> &cells_cone, pool<SigBit> &bits_cone, const pool<Cell*> &cells_stop, const pool<SigBit> &bits_stop, pool<SigBit> *input_bits, Cell *cell)
	{
		if (cells_cone.count(cell))
			return false;

		cells_cone.insert(cell);

		if (cells_stop.count(cell))
			return true;

		for (auto &conn : cell->connections())
			if (yosys_celltypes.cell_input(cell->type, conn.first))
				for (auto bit : sigmap(conn.second)) {
					if (cell->type.in("$dff", "$_DFF_P_", "$_DFF_N_")) {
						if (!conn.first.in("\\CLK", "\\C"))
							next_seed.insert(bit);
					} else
						find_input_cone(next_seed, cells_cone, bits_cone, cells_stop, bits_stop, input_bits, bit);
				}
		return false;
	}

	void find_input_cone(pool<SigBit> &next_seed, pool<Cell*> &cells_cone, pool<SigBit> &bits_cone, const pool<Cell*> &cells_stop, const pool<SigBit> &bits_stop, pool<SigBit> *input_bits, SigBit bit)
	{
		if (bits_cone.count(bit))
			return;

		bits_cone.insert(bit);

		if (bits_stop.count(bit)) {
			if (input_bits != nullptr) input_bits->insert(bit);
			return;
		}

		if (!bit2driver.count(bit))
			return;

		if (find_input_cone(next_seed, cells_cone, bits_cone, cells_stop, bits_stop, input_bits, bit2driver.at(bit)))
			if (input_bits != nullptr) input_bits->insert(bit);
	}

	bool run()
	{
		SigBit bit_a = sigmap(equiv_cell->getPort("\\A")).to_single_sigbit();
		SigBit bit_b = sigmap(equiv_cell->getPort("\\B")).to_single_sigbit();

		if (satgen.model_undef)
		{
			int ez_a = satgen.importSigBit(bit_a, max_seq+1);
			int ez_b = satgen.importDefSigBit(bit_b, max_seq+1);
			int ez_undef_a = satgen.importUndefSigBit(bit_a, max_seq+1);

			ez.assume(ez.XOR(ez_a, ez_b));
			ez.assume(ez.NOT(ez_undef_a));
		}
		else
		{
			int ez_a = satgen.importSigBit(bit_a, max_seq+1);
			int ez_b = satgen.importSigBit(bit_b, max_seq+1);
			ez.assume(ez.XOR(ez_a, ez_b));
		}

		pool<SigBit> seed_a = { bit_a };
		pool<SigBit> seed_b = { bit_b };

		if (verbose) {
			log("  Trying to prove $equiv cell %s:\n", log_id(equiv_cell));
			log("    A = %s, B = %s, Y = %s\n", log_signal(bit_a), log_signal(bit_b), log_signal(equiv_cell->getPort("\\Y")));
		} else {
			log("  Trying to prove $equiv for %s:", log_signal(equiv_cell->getPort("\\Y")));
		}

		int step = max_seq;
		while (1)
		{
			pool<Cell*> no_stop_cells;
			pool<SigBit> no_stop_bits;

			pool<Cell*> full_cells_cone_a, full_cells_cone_b;
			pool<SigBit> full_bits_cone_a, full_bits_cone_b;

			pool<SigBit> next_seed_a, next_seed_b;

			for (auto bit_a : seed_a)
				find_input_cone(next_seed_a, full_cells_cone_a, full_bits_cone_a, no_stop_cells, no_stop_bits, nullptr, bit_a);
			next_seed_a.clear();

			for (auto bit_b : seed_b)
				find_input_cone(next_seed_b, full_cells_cone_b, full_bits_cone_b, no_stop_cells, no_stop_bits, nullptr, bit_b);
			next_seed_b.clear();

			pool<Cell*> short_cells_cone_a, short_cells_cone_b;
			pool<SigBit> short_bits_cone_a, short_bits_cone_b;
			pool<SigBit> input_bits;

			for (auto bit_a : seed_a)
				find_input_cone(next_seed_a, short_cells_cone_a, short_bits_cone_a, full_cells_cone_b, full_bits_cone_b, &input_bits, bit_a);
			next_seed_a.swap(seed_a);

			for (auto bit_b : seed_b)
				find_input_cone(next_seed_b, short_cells_cone_b, short_bits_cone_b, full_cells_cone_a, full_bits_cone_a, &input_bits, bit_b);
			next_seed_b.swap(seed_b);

			pool<Cell*> problem_cells;
			problem_cells.insert(short_cells_cone_a.begin(), short_cells_cone_a.end());
			problem_cells.insert(short_cells_cone_b.begin(), short_cells_cone_b.end());

			if (verbose)
				log("    Adding %d new cells to the problem (%d A, %d B, %d shared).\n",
						GetSize(problem_cells), GetSize(short_cells_cone_a), GetSize(short_cells_cone_b),
						(GetSize(short_cells_cone_a) + GetSize(short_cells_cone_b)) - GetSize(problem_cells));

			for (auto cell : problem_cells)
				if (!satgen.importCell(cell, step+1))
					log_cmd_error("No SAT model available for cell %s (%s).\n", log_id(cell), log_id(cell->type));

			if (satgen.model_undef) {
				for (auto bit : input_bits)
					ez.assume(ez.NOT(satgen.importUndefSigBit(bit, step+1)));
			}

			if (verbose)
				log("    Problem size at t=%d: %d literals, %d clauses\n", step, ez.numCnfVariables(), ez.numCnfClauses());

			if (!ez.solve()) {
				log(verbose ? "    Proved equivalence! Marking $equiv cell as proven.\n" : " success!\n");
				equiv_cell->setPort("\\B", equiv_cell->getPort("\\A"));
				return true;
			}

			if (verbose)
				log("    Failed to prove equivalence with sequence length %d.\n", max_seq - step);

			if (--step < 0) {
				if (verbose)
					log("    Reached sequence limit.\n");
				break;
			}

			if (seed_a.empty() && seed_b.empty()) {
				if (verbose)
					log("    No nets to continue in previous time step.\n");
				break;
			}

			if (seed_a.empty()) {
				if (verbose)
					log("    No nets on A-side to continue in previous time step.\n");
				break;
			}

			if (seed_b.empty()) {
				if (verbose)
					log("    No nets on B-side to continue in previous time step.\n");
				break;
			}

			if (verbose) {
			#if 0
				log("    Continuing analysis in previous time step with the following nets:\n");
				for (auto bit : seed_a)
					log("      A: %s\n", log_signal(bit));
				for (auto bit : seed_b)
					log("      B: %s\n", log_signal(bit));
			#else
				log("    Continuing analysis in previous time step with %d A- and %d B-nets.\n", GetSize(seed_a), GetSize(seed_b));
			#endif
			}
		}

		if (!verbose)
			log(" failed.\n");
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
		log("    -v\n");
		log("        verbose output\n");
		log("\n");
		log("    -undef\n");
		log("        enable modelling of undef states\n");
		log("\n");
		log("    -seq <N>\n");
		log("        the max. number of time steps to be considered (default = 1)\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		bool verbose = false, model_undef = false;
		int success_counter = 0;
		int max_seq = 1;

		log_header("Executing EQUIV_SIMPLE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-v") {
				verbose = true;
				continue;
			}
			if (args[argidx] == "-undef") {
				model_undef = true;
				continue;
			}
			if (args[argidx] == "-seq" && argidx+1 < args.size()) {
				max_seq = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();

		for (auto module : design->selected_modules())
		{
			vector<pair<SigBit, Cell*>> unproven_equiv_cells;

			for (auto cell : module->selected_cells())
				if (cell->type == "$equiv" && cell->getPort("\\A") != cell->getPort("\\B"))
						unproven_equiv_cells.push_back(pair<SigBit, Cell*>(cell->getPort("\\Y").to_single_sigbit(), cell));

			if (unproven_equiv_cells.empty())
				continue;

			log("Found %d unproven $equiv cells in %s:\n", GetSize(unproven_equiv_cells), log_id(module));

			SigMap sigmap(module);
			dict<SigBit, Cell*> bit2driver;

			for (auto cell : module->cells()) {
				if (!ct.cell_known(cell->type) && !cell->type.in("$dff", "$_DFF_P_", "$_DFF_N_"))
					continue;
				for (auto &conn : cell->connections())
					if (yosys_celltypes.cell_output(cell->type, conn.first))
						for (auto bit : sigmap(conn.second))
							bit2driver[bit] = cell;
			}

			std::sort(unproven_equiv_cells.begin(), unproven_equiv_cells.end());
			for (auto it : unproven_equiv_cells) {
				EquivSimpleWorker worker(it.second, sigmap, bit2driver, max_seq, verbose, model_undef);
				if (worker.run())
					success_counter++;
			}
		}

		log("Proved %d previously unproven $equiv cells.\n", success_counter);
	}
} EquivSimplePass;

PRIVATE_NAMESPACE_END
