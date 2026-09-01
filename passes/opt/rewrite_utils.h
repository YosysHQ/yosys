/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.     <akash@silimate.com>
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
 */

// Small shared helpers for Silimate functional-rewrite passes. Include inside
// each pass's PRIVATE_NAMESPACE_BEGIN (same pattern as cut_region.h). Keep
// cone/cut infrastructure in cut_region.h; put only type lists and tiny
// numeric/Const helpers here so passes that do not use CutRegionWorker
// (e.g. opt_prienc) can share them without pulling that machinery in.
//
// Guarded so a pass may include this directly and also via cut_region.h.

#ifndef SILIMATE_REWRITE_UTILS_H
#define SILIMATE_REWRITE_UTILS_H

// Process-level / gate-level cells that terminate combinational cone walks.
static inline bool is_sequential(Cell *c)
{
	// Include $aldff/$aldffe: proc emits async-load FFs for async-reset
	// flops; opt later rewrites them to $adff. Omitting them lets get_cone
	// walk through the launch flop into D/CLK/ALOAD (e.g. full wdata).
	return c->type.in(
		ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
		ID($aldff), ID($aldffe),
		ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr), ID($dffsre),
		ID($_DFF_P_), ID($_DFF_N_),
		ID($_DFFE_PP_), ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_),
		ID($_DFF_PP0_), ID($_DFF_PP1_), ID($_DFF_PN0_), ID($_DFF_PN1_),
		ID($_DFF_NP0_), ID($_DFF_NP1_), ID($_DFF_NN0_), ID($_DFF_NN1_),
		ID($dlatch), ID($adlatch), ID($dlatchsr),
		ID($mem), ID($mem_v2), ID($meminit), ID($meminit_v2),
		ID($memrd), ID($memrd_v2), ID($memwr), ID($memwr_v2),
		ID($fsm),
		ID($assert), ID($assume), ID($cover), ID($live), ID($fair),
		ID($print), ID($check),
		ID($anyconst), ID($anyseq), ID($allconst), ID($allseq),
		ID($initstate));
}

// Clocked process-level FFs (no $ff, latches, or gate $_DFF_*). Used for
// flop-D gather roots where Q/D semantics matter.
static inline bool is_clocked_ff(Cell *c)
{
	return c->type.in(ID($dff), ID($dffe), ID($adff), ID($adffe),
	                  ID($aldff), ID($aldffe),
	                  ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr), ID($dffsre));
}

// Storage cells whose D port is a useful rewrite root (clocked FFs + $ff +
// latches). Broader than is_clocked_ff; narrower than is_sequential.
static inline bool is_storage_ff(Cell *c)
{
	return is_clocked_ff(c) ||
	       c->type.in(ID($ff), ID($dlatch), ID($adlatch), ID($dlatchsr));
}

// Ceiling of log2(x) for x >= 1; clog2_int(1) == 0. Same as Yosys $clog2 for
// positive widths used by these passes.
static inline int clog2_int(int x)
{
	int r = 0;
	while ((1 << r) < x)
		r++;
	return r;
}

// Src attribute of an anchor/driver cell for Module::And/addAnd/... emitters.
// Passing this (instead of relying on the empty default) keeps rewritten
// networks attributable to the original RTL region.
static inline std::string cell_src(Cell *c)
{
	return c ? c->get_src_attribute() : std::string();
}

static inline bool is_power_of_two(int x)
{
	return x > 0 && (x & (x - 1)) == 0;
}

static inline uint64_t lowmask_u64(int w)
{
	if (w <= 0)
		return 0;
	if (w >= 64)
		return ~0ULL;
	return (1ULL << w) - 1;
}

// Pack the low bits of `value` into an existing Const, keeping its width.
static inline void set_const_u64(Const &out, uint64_t value)
{
	auto &bits = out.bits();
	for (int i = 0; i < GetSize(bits); i++)
		bits[i] = i < 64 && ((value >> i) & 1ULL) ? State::S1 : State::S0;
}

// Pack the low `width` bits of `value` into a Const (bit i <- value bit i).
static inline Const const_u64(uint64_t value, int width)
{
	Const c(State::S0, width);
	set_const_u64(c, value);
	return c;
}

// Pack `lanes` into one Const of `count * elem_width` bits, lane k occupying
// bits [k*elem_width +: elem_width]. The lane layout every fingerprint in
// these passes drives its candidate buses with.
static inline Const pack_lanes(const vector<uint64_t> &lanes, int elem_width)
{
	Const c(State::S0, GetSize(lanes) * elem_width);
	auto &bits = c.bits();
	for (int k = 0; k < GetSize(lanes); k++)
		for (int b = 0; b < elem_width; b++)
			if (b < 64 && ((lanes[k] >> b) & 1ULL))
				bits[k * elem_width + b] = State::S1;
	return c;
}

// Reduce `leaves[begin:end]` with `combine` over a balanced binary tree, so the
// result is log-depth rather than a linear chain. Leaf order is preserved, so
// `combine` may be order-sensitive (a priority merge) as well as associative.
// The two halves are built in named steps because `combine` emits cells and
// argument evaluation order is unspecified, which would renumber them.
template <typename T, typename FnCombine>
T reduce_balanced(const vector<T> &leaves, int begin, int end, FnCombine combine)
{
	log_assert(begin < end);
	if (begin + 1 == end)
		return leaves[begin];
	int mid = begin + (end - begin) / 2;
	T lhs = reduce_balanced(leaves, begin, mid, combine);
	T rhs = reduce_balanced(leaves, mid, end, combine);
	return combine(lhs, rhs);
}

template <typename T, typename FnCombine>
T reduce_balanced(const vector<T> &leaves, FnCombine combine)
{
	return reduce_balanced(leaves, 0, GetSize(leaves), combine);
}

#endif // SILIMATE_REWRITE_UTILS_H
