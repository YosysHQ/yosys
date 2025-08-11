/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
	const vector<Cell*> &assume_cells;
	struct Cone {
		pool<Cell*> cells;
		pool<SigBit> bits;
		void clear() {
			cells.clear();
			bits.clear();
		}
	};

	struct DesignModel {
		const SigMap &sigmap;
		dict<SigBit, Cell*> &bit2driver;
	};
	DesignModel model;

	ezSatPtr ez;
	SatGen satgen;

	struct Config {
		bool verbose = false;
		bool short_cones = false;
		bool model_undef = false;
		bool nogroup = false;
		bool set_assumes = false;
		int max_seq = 1;
	};
	Config cfg;

	pool<pair<Cell*, int>> imported_cells_cache;

	EquivSimpleWorker(const vector<Cell*> &equiv_cells, const vector<Cell*> &assume_cells, DesignModel model, Config cfg) :
			module(equiv_cells.front()->module), equiv_cells(equiv_cells), assume_cells(assume_cells),
			model(model), satgen(ez.get(), &model.sigmap), cfg(cfg)
	{
		satgen.model_undef = cfg.model_undef;
	}

	struct ConeFinder {
		DesignModel model;
		// Bits we should also analyze in a later iteration (flop inputs)
		pool<SigBit> &next_seed;
		// Cells and bits we've seen so far while traversing
		Cone& cone;
		// We're not allowed to traverse past cells and bits in `stop`
		const Cone& stop;
		// Input bits are bits that no longer can be traversed
		// Tracking these is optional
		pool<SigBit>* input_bits;

		// Recursively traverses backwards from a cell to find all cells in its input cone
		// Adds cell to cone.cells, stops at cells in 'stop' set
		// Returns true if stopped on a stop cell
		bool find_input_cone(Cell *cell)
		{
			if (cone.cells.count(cell))
				return false;

			cone.cells.insert(cell);

			if (stop.cells.count(cell))
				return true;

			for (auto &conn : cell->connections())
				if (yosys_celltypes.cell_input(cell->type, conn.first))
					for (auto bit : model.sigmap(conn.second)) {
						if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
							if (!conn.first.in(ID::CLK, ID::C))
								next_seed.insert(bit);
						} else
							find_input_cone(bit);
					}
			return false;
		}
		void find_input_cone(SigBit bit)
		{
			if (cone.bits.count(bit))
				return;

			cone.bits.insert(bit);

			if (stop.bits.count(bit)) {
				if (input_bits != nullptr) input_bits->insert(bit);
				return;
			}

			if (!model.bit2driver.count(bit))
				return;

			// If the input cone of the driver cell reaches a stop bit,
			// then `bit` is an "input bit"
			if (find_input_cone(model.bit2driver.at(bit)))
				if (input_bits != nullptr) input_bits->insert(bit);
		}
		void find_input_cone(pool<SigBit> bits)
		{
			for (auto bit : bits)
				find_input_cone(bit);
		}
	};

	// Builds (full or short) input cones from the seeds
	// Creates full cones (no stops) and optionally short cones (stop at other side's cone)
	// Updates seed_a/seed_b with next iteration's FF inputs
	// Returns input bits and cone structures for SAT problem construction
	std::tuple<pool<SigBit>, Cone, Cone> init_iter(pool<SigBit>& seed_a, pool<SigBit>& seed_b) const
	{
		// Empty, never inserted to, to traverse full cones
		const Cone no_stop;
		Cone full_cone_a, full_cone_b;

		// Values of seed_* for the next iteration
		pool<SigBit> next_seed_a, next_seed_b;

		{
			ConeFinder finder_a {model, next_seed_a, full_cone_a, no_stop, nullptr};
			finder_a.find_input_cone(seed_a);

			ConeFinder finder_b {model, next_seed_b, full_cone_b, no_stop, nullptr};
			finder_b.find_input_cone(seed_b);
		}

		Cone short_cone_a, short_cone_b;
		pool<SigBit> input_bits;

		if (cfg.short_cones)
		{
			// Rebuild cones with the knowledge of the full cones.
			// Avoids stuffing overlaps in input cones into the solver
			// e.g. for A by using the full B cone as stops
			next_seed_a.clear();
			ConeFinder short_finder_a = {model, next_seed_a, short_cone_a, short_cone_b, &input_bits};
			short_finder_a.find_input_cone(seed_a);
			next_seed_a.swap(seed_a);

			next_seed_b.clear();
			ConeFinder short_finder_b = {model, next_seed_b, short_cone_b, short_cone_a, &input_bits};
			short_finder_b.find_input_cone(seed_b);
			next_seed_b.swap(seed_b);
		}
		else
		{
			short_cone_a = full_cone_a;
			next_seed_a.swap(seed_a);

			short_cone_b = full_cone_b;
			next_seed_b.swap(seed_b);
		}
		return std::make_tuple(input_bits, short_cone_a, short_cone_b);
	}

	void report_new_cells(const pool<Cell*>& cells, const Cone& cone_a, const Cone& cone_b) const
	{
		log("    Adding %d new cells to the problem (%d A, %d B, %d shared).\n",
					GetSize(cells), GetSize(cone_a.cells), GetSize(cone_b.cells),
					(GetSize(cone_a.cells) + GetSize(cone_b.cells)) - GetSize(cells));
		#if 0
			for (auto cell : short_cells_cone_a)
				log("      A-side cell: %s\n", log_id(cell));

			for (auto cell : short_cells_cone_b)
				log("      B-side cell: %s\n", log_id(cell));
		#endif
	}
	void report_new_assume_cells(const pool<Cell*>& extra_problem_cells, int old_size, const pool<Cell*>& problem_cells) const
	{
		if (cfg.verbose) {
			log("    Adding %d new cells to check assumptions (and reusing %d).\n",
				GetSize(problem_cells) - old_size,
				old_size - (GetSize(problem_cells) - GetSize(extra_problem_cells)));
		#if 0
			for (auto cell : extra_problem_cells)
				log("      cell: %s\n", log_id(cell));
		#endif
		}
	}

	// Ensure the input cones of $assume cells get modelled by the problem
	pool<Cell*> add_assumes_to_problem(const Cone& cone_a, const Cone& cone_b) const
	{
		pool<Cell*> extra_problem_cells;
		for (auto assume : assume_cells) {
			pool<SigBit> assume_seed, dummy_next_seed, overlap_bits;
			assume_seed.insert(model.sigmap(assume->getPort(ID::A)).as_bit());
			assume_seed.insert(model.sigmap(assume->getPort(ID::EN)).as_bit());

			for (auto& cone : {cone_a, cone_b}) {
				Cone assume_cone;
				ConeFinder{model, dummy_next_seed, assume_cone, cone, &overlap_bits}
					.find_input_cone(assume_seed);
				if (GetSize(overlap_bits)) {
					extra_problem_cells.insert(assume);
					extra_problem_cells.insert(assume_cone.cells.begin(), assume_cone.cells.end());
					overlap_bits.clear();
				}
				assume_cone.clear();
				dummy_next_seed.clear();
			}
		}
		return extra_problem_cells;
	}

	static void report_missing_model(Cell* cell)
	{
		if (RTLIL::builtin_ff_cell_types().count(cell->type))
			log_cmd_error("No SAT model available for async FF cell %s (%s).  Consider running `async2sync` or `clk2fflogic` first.\n", log_id(cell), log_id(cell->type));
		else
			log_cmd_error("No SAT model available for cell %s (%s).\n", log_id(cell), log_id(cell->type));
	}

	void prepare_ezsat(int ez_context, SigBit bit_a, SigBit bit_b)
	{
		if (satgen.model_undef)
		{
			int ez_a = satgen.importSigBit(bit_a, cfg.max_seq+1);
			int ez_b = satgen.importDefSigBit(bit_b, cfg.max_seq+1);
			int ez_undef_a = satgen.importUndefSigBit(bit_a, cfg.max_seq+1);

			ez->assume(ez->XOR(ez_a, ez_b), ez_context);
			ez->assume(ez->NOT(ez_undef_a), ez_context);
		}
		else
		{
			int ez_a = satgen.importSigBit(bit_a, cfg.max_seq+1);
			int ez_b = satgen.importSigBit(bit_b, cfg.max_seq+1);
			ez->assume(ez->XOR(ez_a, ez_b), ez_context);
		}
	}
	void construct_ezsat(const pool<SigBit>& input_bits, int step)
	{
		if (cfg.set_assumes) {
			if (cfg.verbose && step == cfg.max_seq) {
				RTLIL::SigSpec assumes_a, assumes_en;
				satgen.getAssumes(assumes_a, assumes_en, step+1);
				for (int i = 0; i < GetSize(assumes_a); i++)
					log("    Import constraint from assume cell: %s when %s (%d).\n", log_signal(assumes_a[i]), log_signal(assumes_en[i]), step);
			}
			ez->assume(satgen.importAssumes(step+1));
		}

		if (satgen.model_undef) {
			for (auto bit : input_bits)
				ez->assume(ez->NOT(satgen.importUndefSigBit(bit, step+1)));
		}

		if (cfg.verbose)
			log("    Problem size at t=%d: %d literals, %d clauses\n", step, ez->numCnfVariables(), ez->numCnfClauses());
	}

	bool prove_equiv_cell(Cell* cell)
	{
		SigBit bit_a = model.sigmap(cell->getPort(ID::A)).as_bit();
		SigBit bit_b = model.sigmap(cell->getPort(ID::B)).as_bit();
		int ez_context = ez->frozen_literal();

		prepare_ezsat(ez_context, bit_a, bit_b);

		// Two bits, bit_a, and bit_b, have been marked equivalent in the design
		// We will be traversing the input cones for each of them
		// In the first iteration, we will using those as starting points
		pool<SigBit> seed_a = { bit_a };
		pool<SigBit> seed_b = { bit_b };

		if (cfg.verbose) {
			log("  Trying to prove $equiv cell %s:\n", log_id(cell));
			log("    A = %s, B = %s, Y = %s\n", log_signal(bit_a), log_signal(bit_b), log_signal(cell->getPort(ID::Y)));
		} else {
			log("  Trying to prove $equiv for %s:", log_signal(cell->getPort(ID::Y)));
		}

		int step = cfg.max_seq;
		while (1)
		{
			// Traverse input cones of seed_a and seed_b, potentially finding new seeds
			auto [input_bits, cone_a, cone_b] = init_iter(seed_a, seed_b);

			// Cells to model in SAT solver
			pool<Cell*> problem_cells;
			problem_cells.insert(cone_a.cells.begin(), cone_a.cells.end());
			problem_cells.insert(cone_b.cells.begin(), cone_b.cells.end());

			if (cfg.verbose)
				report_new_cells(problem_cells, cone_a, cone_b);

			if (cfg.set_assumes) {
				auto extras = add_assumes_to_problem(cone_a, cone_b);
				if (GetSize(extras)) {
					auto old_size = GetSize(problem_cells);
					problem_cells.insert(extras.begin(), extras.end());
					report_new_assume_cells(extras, old_size, problem_cells);
				}
			}

			for (auto cell : problem_cells) {
				auto key = pair<Cell*, int>(cell, step+1);
				if (!imported_cells_cache.count(key) && !satgen.importCell(cell, step+1)) {
					report_missing_model(cell);
				}
				imported_cells_cache.insert(key);
			}

			construct_ezsat(input_bits, step);

			if (!ez->solve(ez_context)) {
				log(cfg.verbose ? "    Proved equivalence! Marking $equiv cell as proven.\n" : " success!\n");
				// Replace $equiv cell with a short
				cell->setPort(ID::B, cell->getPort(ID::A));
				ez->assume(ez->NOT(ez_context));
				return true;
			}

			if (cfg.verbose)
				log("    Failed to prove equivalence with sequence length %d.\n", cfg.max_seq - step);

			if (--step < 0) {
				if (cfg.verbose)
					log("    Reached sequence limit.\n");
				break;
			}

			if (seed_a.empty() && seed_b.empty()) {
				if (cfg.verbose)
					log("    No nets to continue in previous time step.\n");
				break;
			}

			if (seed_a.empty()) {
				if (cfg.verbose)
					log("    No nets on A-side to continue in previous time step.\n");
				break;
			}

			if (seed_b.empty()) {
				if (cfg.verbose)
					log("    No nets on B-side to continue in previous time step.\n");
				break;
			}

			if (cfg.verbose) {
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

		if (!cfg.verbose)
			log(" failed.\n");

		ez->assume(ez->NOT(ez_context));
		return false;
	}

	int run()
	{
		if (GetSize(equiv_cells) > 1) {
			SigSpec sig;
			for (auto c : equiv_cells)
				sig.append(model.sigmap(c->getPort(ID::Y)));
			log(" Grouping SAT models for %s:\n", log_signal(sig));
		}

		int counter = 0;
		for (auto c : equiv_cells) {
			if (prove_equiv_cell(c))
				counter++;
		}
		return counter;
	}

};

struct EquivSimplePass : public Pass {
	EquivSimplePass() : Pass("equiv_simple", "try proving simple $equiv instances") { }
	void help() override
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
		log("    -set-assumes\n");
		log("        set all assumptions provided via $assume cells\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, Design *design) override
	{
		EquivSimpleWorker::Config cfg = {};
		int success_counter = 0;

		log_header(design, "Executing EQUIV_SIMPLE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-v") {
				cfg.verbose = true;
				continue;
			}
			if (args[argidx] == "-short") {
				cfg.short_cones = true;
				continue;
			}
			if (args[argidx] == "-undef") {
				cfg.model_undef = true;
				continue;
			}
			if (args[argidx] == "-nogroup") {
				cfg.nogroup = true;
				continue;
			}
			if (args[argidx] == "-seq" && argidx+1 < args.size()) {
				cfg.max_seq = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-set-assumes") {
				cfg.set_assumes = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();
		ct.setup_internals_ff();
		ct.setup_stdcells_mem();

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			dict<SigBit, Cell*> bit2driver;
			dict<SigBit, dict<SigBit, Cell*>> unproven_equiv_cells;
			vector<Cell*> assumes;
			int unproven_cells_counter = 0;

			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($equiv) && cell->getPort(ID::A) != cell->getPort(ID::B)) {
					auto bit = sigmap(cell->getPort(ID::Y).as_bit());
					auto bit_group = bit;
					if (!cfg.nogroup && bit_group.wire)
						bit_group.offset = 0;
					unproven_equiv_cells[bit_group][bit] = cell;
					unproven_cells_counter++;
				} else if (cell->type == ID($assume)) {
					assumes.push_back(cell);
				}
			}

			if (unproven_equiv_cells.empty())
				continue;

			log("Found %d unproven $equiv cells (%d groups) in %s:\n",
					unproven_cells_counter, GetSize(unproven_equiv_cells), log_id(module));

			for (auto cell : module->cells()) {
				if (!ct.cell_known(cell->type))
					continue;
				for (auto &conn : cell->connections())
					if (yosys_celltypes.cell_output(cell->type, conn.first))
						for (auto bit : sigmap(conn.second))
							bit2driver[bit] = cell;
			}

			unproven_equiv_cells.sort();
			for (auto [_, d] : unproven_equiv_cells)
			{
				d.sort();

				vector<Cell*> cells;
				for (auto [_, cell] : d)
					cells.push_back(cell);

				EquivSimpleWorker::DesignModel model {sigmap, bit2driver};
				EquivSimpleWorker worker(cells, assumes, model, cfg);
				success_counter += worker.run();
			}
		}

		log("Proved %d previously unproven $equiv cells.\n", success_counter);
	}
} EquivSimplePass;

PRIVATE_NAMESPACE_END
