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

#ifndef BITPATTERN_H
#define BITPATTERN_H

#include "kernel/log.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

/**
 * This file implements BitPatternPool for efficiently storing and querying
 * sets of fixed-width 2-valued logic constants.
 * A pattern (cube) can have don't cares on one or more bit positions (State::Sa).
 *
 * The pool is a reduced ordered BDD, see https://github.com/YosysHQ/yosys/issues/6359.
 * Past max_nodes it gives up and answers conservatively.
 *
 * BitPatternPool does not permit adding new patterns, only removing.
 * Its intended use case is in analysing cases in case/match constructs in HDL.
 */
struct BitPatternPool
{
	enum class Terminal : int {
		Empty = 0,
		Full = 1
	};

	// bounds recursion depth
	static constexpr int MAX_WIDTH = 4096;

	int width;
	int max_nodes = 1 << 17;
	bool gave_up = false;

	BitPatternPool(RTLIL::SigSpec sig);

	/**
	 * Constructs a pool of all possible patterns (all don't-care bits)
	 */
	BitPatternPool(int width);

	/**
	 * A literal x/z bit can never match a 2-valued selector, so a pattern containing
	 * one covers nothing.
	 */
	static bool covers_nothing(RTLIL::SigSpec sig);

	/**
	 * Does cube sig overlap the pool?
	 * For example:
	 * pool({aaa}).has_any(01a) == true
	 * pool({01a}).has_any(01a) == true
	 * pool({011}).has_any(01a) == true
	 * pool({01a}).has_any(011) == true
	 * pool({111}).has_any(01a) == false
	 */
	bool has_any(RTLIL::SigSpec sig);

	/**
	 * Is cube sig covered by the pool?
	 * For example:
	 * pool({aaa}).has_all(01a) == true
	 * pool({01a}).has_all(01a) == true
	 * pool({01a}).has_all(011) == true
	 * pool({011}).has_all(01a) == false
	 * pool({111}).has_all(01a) == false
	 */
	bool has_all(RTLIL::SigSpec sig);

	/**
	 * Remove cube sig from the pool. True if the pool overlapped sig.
	 * For example:
	 * Taking 011 out of pool({01a}) -> pool({010}), returns true.
	 * Taking 011 out of pool({010}) does nothing, returns false.
	 */
	bool take(RTLIL::SigSpec sig);

	/**
	 * Remove all patterns. Returns false if already empty.
	 */
	bool take_all();

	bool empty();
private:
	int budget();
	int bit_index(int level);
	int make_node(int level, int low, int high);
	bool reaches(int node, const std::vector<RTLIL::State> &bits, int terminal, pool<int> &misses);
	int remove_cube(int node, int level, const std::vector<RTLIL::State> &bits, dict<std::pair<int, int>, int> &cache);
	bool remove(const std::vector<RTLIL::State> &bits);
	bool rebuild();

	enum class Attempt {
		MsbFirstQuarterBudget,
		LsbFirst,
		MsbFirst
	};

	Attempt attempt = Attempt::MsbFirstQuarterBudget;

	// (level, low, high)
	idict<std::tuple<int, int, int>> nodes;
	int root = int(Terminal::Empty);

	std::vector<RTLIL::State> universe;
	std::vector<std::vector<RTLIL::State>> taken;
};

YOSYS_NAMESPACE_END

#endif
