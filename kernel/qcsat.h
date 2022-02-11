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

YOSYS_NAMESPACE_END

#endif
