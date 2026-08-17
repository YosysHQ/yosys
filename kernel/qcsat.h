/* -*- c++ -*-
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
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

#ifndef QCSAT_H
#define QCSAT_H

#include "kernel/satgen.h"
#include "kernel/modtools.h"

YOSYS_NAMESPACE_BEGIN

// This is a helper class meant for easy construction of quick SAT queries
// to a combinatorial input cone of some set of signals, meant for SAT-based
// optimizations.  Various knobs are provided to set just how much of the
// cone should be included in the model — since this class is meant for
// optimization, it should not be a correctness problem when some cells are
// skipped and the solver spuriously returns SAT with a solution that
// cannot exist in reality due to skipped constraints (ie. only UNSAT results
// from this class should be considered binding).
struct QuickConeSat {
	ModWalker &modwalker;
	ezSatPtr ez;
	SatGen satgen;

	// The effort level knobs.

	// The maximum "complexity level" of cells that will be imported.
	// - 1: bitwise operations, muxes, equality comparisons, lut, sop, fa
	// - 2: addition, subtraction, greater/less than comparisons, lcu
	// - 3: shifts
	// - 4: multiplication, division, power
	int max_cell_complexity = 2;
	// The maximum number of cells to import, or 0 for no limit.
	int max_cell_count = 0;
	// If non-0, skip importing cells with more than this number of output bits.
	int max_cell_outs = 0;

	// Internal state.
	pool<RTLIL::Cell*> imported_cells;
	pool<RTLIL::Wire*> imported_onehot;
	pool<RTLIL::SigBit> bits_queue;

	QuickConeSat(ModWalker &modwalker) : modwalker(modwalker), ez(), satgen(ez.get(), &modwalker.sigmap) {}

	// Imports a signal into the SAT solver, queues its input cone to be
	// imported in the next prepare() call.
	std::vector<int> importSig(SigSpec sig);
	int importSigBit(SigBit bit);

	// Imports the input cones of all previously importSig'd signals into
	// the SAT solver.
	void prepare();

	// Returns the "complexity level" of a given cell.
	static int cell_complexity(RTLIL::Cell *cell);
};

// A deterministic effort budget for SAT-based optimizations, measured in solver
// propagation steps (see ezSAT::getSolverProps). The budget is held once per unit
// of work (typically a module) and reused across many QuickConeSat instances: a
// pass that rebuilds the solver in batches keeps a single SatEffortBudget and
// spends from it in every batch, rather than resetting the budget per solver.
// Spending the budget only skips optimizations, and it never affects correctness,
// because a skipped proof just leaves a candidate un-optimized.
struct SatEffortBudget {
	enum class Result { Sat, Unsat, LimitReached };

	// Effort charged per imported cell
	static constexpr int64_t import_cell_cost = 100;

	// starting budget (0 = unlimited)
	int64_t total = 0;
	int64_t remaining = 0;

	SatEffortBudget() {}
	explicit SatEffortBudget(int64_t total) : total(total), remaining(total) {}

	bool enabled() const { return total > 0; }

	// True once the budget is used up
	bool spent() const { return enabled() && remaining <= 0; }

	// Charge for the cells imported into qcsat since the previous call (pricing the cells pulled in)
	// cells_charged records how many of qcsat's imported cells are already paid for
	void charge_import(QuickConeSat &qcsat, int64_t &cells_charged);

	Result solve(QuickConeSat &qcsat, int64_t cap, const std::vector<int> &modelExprs,
			std::vector<bool> &modelVals, const std::vector<int> &assumptions);

	// Assumptions-only query without a model
	Result solve(QuickConeSat &qcsat, int64_t cap, const std::vector<int> &assumptions);
};

YOSYS_NAMESPACE_END

#endif
