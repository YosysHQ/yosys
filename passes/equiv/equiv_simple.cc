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
	const vector<Cell*> &equiv_cells;
	Cell *equiv_cell;

	SigMap &sigmap;
	dict<SigBit, Cell*> &bit2driver;

	ezSatPtr ez;
	SatGen satgen;
	int max_seq;
	bool short_cones;
	bool verbose;

	pool<pair<Cell*, int>> imported_cells_cache;

	EquivSimpleWorker(const vector<Cell*> &equiv_cells, SigMap &sigmap, dict<SigBit, Cell*> &bit2driver, int max_seq, bool short_cones, bool verbose, bool model_undef) :
			module(equiv_cells.front()->module), equiv_cells(equiv_cells), equiv_cell(nullptr),
			sigmap(sigmap), bit2driver(bit2driver), satgen(ez.get(), &sigmap), max_seq(max_seq), short_cones(short_cones), verbose(verbose)
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
					if (cell->type.in("$dff", "$_DFF_P_", "$_DFF_N_", "$ff", "$_FF_")) {
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

	bool run_cell()
	{
		SigBit bit_a = sigmap(equiv_cell->getPort("\\A")).as_bit();
		SigBit bit_b = sigmap(equiv_cell->getPort("\\B")).as_bit();
		int ez_context = ez->frozen_literal();

		if (satgen.model_undef)
		{
			int ez_a = satgen.importSigBit(bit_a, max_seq+1);
			int ez_b = satgen.importDefSigBit(bit_b, max_seq+1);
			int ez_undef_a = satgen.importUndefSigBit(bit_a, max_seq+1);

			ez->assume(ez->XOR(ez_a, ez_b), ez_context);
			ez->assume(ez->NOT(ez_undef_a), ez_context);
		}
		else
		{
			int ez_a = satgen.importSigBit(bit_a, max_seq+1);
			int ez_b = satgen.importSigBit(bit_b, max_seq+1);
			ez->assume(ez->XOR(ez_a, ez_b), ez_context);
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

			if (short_cones)
			{
				for (auto bit_a : seed_a)
					find_input_cone(next_seed_a, short_cells_cone_a, short_bits_cone_a, full_cells_cone_b, full_bits_cone_b, &input_bits, bit_a);
				next_seed_a.swap(seed_a);

				for (auto bit_b : seed_b)
					find_input_cone(next_seed_b, short_cells_cone_b, short_bits_cone_b, full_cells_cone_a, full_bits_cone_a, &input_bits, bit_b);
				next_seed_b.swap(seed_b);
			}
			else
			{
				short_cells_cone_a = full_cells_cone_a;
				short_bits_cone_a = full_bits_cone_a;
				next_seed_a.swap(seed_a);

				short_cells_cone_b = full_cells_cone_b;
				short_bits_cone_b = full_bits_cone_b;
				next_seed_b.swap(seed_b);
			}

			pool<Cell*> problem_cells;
			problem_cells.insert(short_cells_cone_a.begin(), short_cells_cone_a.end());
			problem_cells.insert(short_cells_cone_b.begin(), short_cells_cone_b.end());

			if (verbose)
			{
				log("    Adding %d new cells to the problem (%d A, %d B, %d shared).\n",
						GetSize(problem_cells), GetSize(short_cells_cone_a), GetSize(short_cells_cone_b),
						(GetSize(short_cells_cone_a) + GetSize(short_cells_cone_b)) - GetSize(problem_cells));
			#if 0
				for (auto cell : short_cells_cone_a)
					log("      A-side cell: %s\n", log_id(cell));

				for (auto cell : short_cells_cone_b)
					log("      B-side cell: %s\n", log_id(cell));
			#endif
			}

			for (auto cell : problem_cells) {
				auto key = pair<Cell*, int>(cell, step+1);
				if (!imported_cells_cache.count(key) && !satgen.importCell(cell, step+1))
					log_cmd_error("No SAT model available for cell %s (%s).\n", log_id(cell), log_id(cell->type));
				imported_cells_cache.insert(key);
			}

			if (satgen.model_undef) {
				for (auto bit : input_bits)
					ez->assume(ez->NOT(satgen.importUndefSigBit(bit, step+1)));
			}

			if (verbose)
				log("    Problem size at t=%d: %d literals, %d clauses\n", step, ez->numCnfVariables(), ez->numCnfClauses());

			if (!ez->solve(ez_context)) {
				log(verbose ? "    Proved equivalence! Marking $equiv cell as proven.\n" : " success!\n");
				equiv_cell->setPort("\\B", equiv_cell->getPort("\\A"));
				ez->assume(ez->NOT(ez_context));
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

		ez->assume(ez->NOT(ez_context));
		return false;
	}

	int run()
	{
		if (GetSize(equiv_cells) > 1) {
			SigSpec sig;
			for (auto c : equiv_cells)
				sig.append(sigmap(c->getPort("\\Y")));
			log(" Grouping SAT models for %s:\n", log_signal(sig));
		}

		int counter = 0;
		for (auto c : equiv_cells) {
			equiv_cell = c;
			if (run_cell())
				counter++;
		}
		return counter;
	}

};

struct EquivSimplePass : public Pass {
	EquivSimplePass() : Pass("equiv_simple", "try proving simple $equiv instances") { }
	void help() YS_OVERRIDE
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
		log("    -short\n");
		log("        create shorter input cones that stop at shared nodes. This yields\n");
		log("        simpler SAT problems but sometimes fails to prove equivalence.\n");
		log("\n");
		log("    -nogroup\n");
		log("        disabling grouping of $equiv cells by output wire\n");
		log("\n");
		log("    -seq <N>\n");
		log("        the max. number of time steps to be considered (default = 1)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, Design *design) YS_OVERRIDE
	{
		bool verbose = false, short_cones = false, model_undef = false, nogroup = false;
		int success_counter = 0;
		int max_seq = 1;

		log_header(design, "Executing EQUIV_SIMPLE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-v") {
				verbose = true;
				continue;
			}
			if (args[argidx] == "-short") {
				short_cones = true;
				continue;
			}
			if (args[argidx] == "-undef") {
				model_undef = true;
				continue;
			}
			if (args[argidx] == "-nogroup") {
				nogroup = true;
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
			SigMap sigmap(module);
			dict<SigBit, Cell*> bit2driver;
			dict<SigBit, dict<SigBit, Cell*>> unproven_equiv_cells;
			int unproven_cells_counter = 0;

			for (auto cell : module->selected_cells())
				if (cell->type == "$equiv" && cell->getPort("\\A") != cell->getPort("\\B")) {
					auto bit = sigmap(cell->getPort("\\Y").as_bit());
					auto bit_group = bit;
					if (!nogroup && bit_group.wire)
						bit_group.offset = 0;
					unproven_equiv_cells[bit_group][bit] = cell;
					unproven_cells_counter++;
				}

			if (unproven_equiv_cells.empty())
				continue;

			log("Found %d unproven $equiv cells (%d groups) in %s:\n",
					unproven_cells_counter, GetSize(unproven_equiv_cells), log_id(module));

			for (auto cell : module->cells()) {
				if (!ct.cell_known(cell->type) && !cell->type.in("$dff", "$_DFF_P_", "$_DFF_N_", "$ff", "$_FF_"))
					continue;
				for (auto &conn : cell->connections())
					if (yosys_celltypes.cell_output(cell->type, conn.first))
						for (auto bit : sigmap(conn.second))
							bit2driver[bit] = cell;
			}

			unproven_equiv_cells.sort();
			for (auto it : unproven_equiv_cells)
			{
				it.second.sort();

				vector<Cell*> cells;
				for (auto it2 : it.second)
					cells.push_back(it2.second);

				EquivSimpleWorker worker(cells, sigmap, bit2driver, max_seq, short_cones, verbose, model_undef);
				success_counter += worker.run();
			}
		}

		log("Proved %d previously unproven $equiv cells.\n", success_counter);
	}
} EquivSimplePass;

PRIVATE_NAMESPACE_END
