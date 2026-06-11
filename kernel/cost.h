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

#ifndef COST_H
#define COST_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct CellCosts
{

	private:
	dict<TwineRef, int> mod_cost_cache_;
	Design *design_ = nullptr;

	public:
	CellCosts(RTLIL::Design *design) : design_(design) { }

	static const dict<TwineRef, int>& default_gate_cost() {
		// Default size heuristics for several common PDK standard cells
		// used by abc and stat
		static const dict<TwineRef, int> db = {
			{ TW($_BUF_),    1 },
			{ TW($_NOT_),    2 },
			{ TW($_AND_),    4 },
			{ TW($_NAND_),   4 },
			{ TW($_OR_),     4 },
			{ TW($_NOR_),    4 },
			{ TW($_ANDNOT_), 4 },
			{ TW($_ORNOT_),  4 },
			{ TW($_XOR_),    5 },
			{ TW($_XNOR_),   5 },
			{ TW($_AOI3_),   6 },
			{ TW($_OAI3_),   6 },
			{ TW($_AOI4_),   7 },
			{ TW($_OAI4_),   7 },
			{ TW($_MUX_),    4 },
			{ TW($_NMUX_),   4 },
		};
		return db;
	}

	static const dict<TwineRef, int>& cmos_gate_cost() {
		// Estimated CMOS transistor counts for several common PDK standard cells
		// used by stat and optionally by abc
		static const dict<TwineRef, int> db = {
			{ TW($_BUF_),     1 },
			{ TW($_NOT_),     2 },
			{ TW($_AND_),     6 },
			{ TW($_NAND_),    4 },
			{ TW($_OR_),      6 },
			{ TW($_NOR_),     4 },
			{ TW($_ANDNOT_),  6 },
			{ TW($_ORNOT_),   6 },
			{ TW($_XOR_),    12 },
			{ TW($_XNOR_),   12 },
			{ TW($_AOI3_),    6 },
			{ TW($_OAI3_),    6 },
			{ TW($_AOI4_),    8 },
			{ TW($_OAI4_),    8 },
			{ TW($_MUX_),    12 },
			{ TW($_NMUX_),   10 },
			{ TW($_DFF_P_),  16 },
			{ TW($_DFF_N_),  16 },
		};
		return db;
	}

	// Get the cell cost for a cell based on its parameters.
	// This cost is an *approximate* upper bound for the number of gates that
	// the cell will get mapped to with "opt -fast; techmap"
	// The intended usage is for flattening heuristics and similar situations
	unsigned int get(RTLIL::Cell *cell);
	// Sum up the cell costs of all cells in the module
	// and all its submodules recursively
	unsigned int get(RTLIL::Module *mod);
};

YOSYS_NAMESPACE_END

#endif
