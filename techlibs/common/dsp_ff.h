// ISC License
//
// Copyright (C) 2024 Microchip Technology Inc. and its subsidiaries
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
// ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
// ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
// OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

#ifndef DSP_FF_H
#define DSP_FF_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

// Helper function to remove unused bits
inline SigSpec dsp_unextend(const SigSpec &sig)
{
	int i = {};
	for (i = GetSize(sig)-1; i > 0; i--)
		if (sig[i] != sig[i-1])
			break;
	// Do not remove non-const sign bit
	if (sig[i].wire)
		++i;
	return sig.extract(0, i);
}

// Number of low bits of P that have users besides the DSP
inline int dsp_used_width(const MatchPatternBase &pm, const SigSpec &P)
{
	int i = {};
	for (i = GetSize(P)-1; i >= 0; i--)
		if (pm.nusers(P[i]) > 1)
			break;
	i++;
	log_assert(pm.nusers(P.extract_end(i)) <= 1);
	return i;
}

inline bool dsp_same_ff_controls(const MatchPatternBase &pm, Cell *ff, Cell *other)
{
	if (ff->type != other->type)
		return false;
	if (ff->type.in(ID($sdff), ID($sdffe), ID($sdffce))) {
		if (pm.param(ff, ID::SRST_POLARITY) != pm.param(other, ID::SRST_POLARITY))
			return false;
		if (pm.port(ff, ID::SRST) != pm.port(other, ID::SRST))
			return false;
	}
	if (ff->type.in(ID($dffe), ID($sdffe), ID($sdffce))) {
		if (pm.param(ff, ID::EN_POLARITY) != pm.param(other, ID::EN_POLARITY))
			return false;
		if (pm.port(ff, ID::EN) != pm.port(other, ID::EN))
			return false;
	}
	return true;
}

inline bool dsp_is_extension_of(const SigSpec &sig, const SigSpec &low)
{
	SigSpec high = sig.extract_end(GetSize(low));
	return high == SigSpec(low[GetSize(low)-1], GetSize(high)) || high == SigSpec(State::S0, GetSize(high));
}

struct DspFf
{
	Cell *cell = nullptr;
	SigSpec sig = {};
	SigBit clock = {};
};

struct DspFfIndex
{
	struct FfSlice {
		Cell *cell = nullptr;
		int offset = {};
	};

	MatchIndex<SigBit, FfSlice> by_q = {};
	MatchIndex<SigBit, FfSlice> by_d = {};

	void add_input(const MatchPatternBase &pm, Cell *cell)
	{
		// async reset flops are only taken when in_dffe allows them
		// does not support clock inversion
		if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($adff), ID($adffe)) && pm.param(cell, ID::CLK_POLARITY).as_bool()) {
			// it is possible that only part of a dff output matches argQ
			for (int offset = 0; offset < GetSize(pm.port(cell, ID::D)); offset++)
				by_q.add(pm.port(cell, ID::Q)[offset], {cell, offset});
		}
	}

	void add_output(const MatchPatternBase &pm, Cell *cell)
	{
		// does not support clock inversion
		if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe)) && pm.param(cell, ID::CLK_POLARITY).as_bool())
			for (int offset = 0; offset < GetSize(pm.port(cell, ID::D)); offset++)
				by_d.add(pm.port(cell, ID::D)[offset], {cell, offset});
	}

	static bool nonzero_init(const SigChunk &c)
	{
		Const init = c.wire->attributes.at(ID::init, Const());
		if (!init.empty())
			for (auto b : init.extract(c.offset, c.width))
				if (b != State::Sx && b != State::S0)
					return true;
		return false;
	}

	// Subpattern for matching against input registers, based on knowledge of the
	//   'Q' input.
	DspFf in_dffe(const MatchPatternBase &pm, const SigSpec &argQ, SigBit clock, bool allow_async = false) const
	{
		DspFf found = {};
		if (argQ.empty())
			return found;
		for (const auto &c : argQ.chunks()) {
			// Abandon matches when 'Q' is a constant
			if (!c.wire)
				return found;
			// Abandon matches when 'Q' has the keep attribute set
			if (c.wire->get_bool_attribute(ID::keep))
				return found;
			// Abandon matches when 'Q' has a non-zero init attribute set
			// (not supported by the DSP)
			if (nonzero_init(c))
				return found;
		}
		for (auto &[ff, offset] : pm.candidates(by_q.find(argQ[0]))) {
			// only consider async rst flops when flag is set
			if (ff->type.in(ID($adff), ID($adffe)) && !allow_async)
				continue;
			// Check that reset value, if present, is fully 0.
			bool noResetFlop = ff->type.in(ID($dff), ID($dffe));
			bool srstZero = ff->type.in(ID($sdff), ID($sdffe)) && pm.param(ff, ID::SRST_VALUE).is_fully_zero();
			bool arstZero = ff->type.in(ID($adff), ID($adffe)) && pm.param(ff, ID::ARST_VALUE).is_fully_zero();
			if (!noResetFlop && !srstZero && !arstZero)
				continue;
			// Check that the rest of argQ is present
			if (GetSize(pm.port(ff, ID::Q)) < offset + GetSize(argQ))
				continue;
			if (pm.port(ff, ID::Q).extract(offset, GetSize(argQ)) != argQ)
				continue;
			// clock must be consistent
			if (clock != SigBit() && pm.port(ff, ID::CLK)[0] != clock)
				continue;
			SigSpec Q = pm.port(ff, ID::Q);
			found.cell = ff;
			found.clock = pm.port(ff, ID::CLK);
			found.sig = argQ;
			SigSpec D = pm.port(ff, ID::D);
			found.sig.replace(Q, D);
		}
		return found;
	}

	// Subpattern for matching against output registers, based on knowledge of the
	//   'D' input.
	// At a high level:
	//   (1) Starting from an optional $mux cell that implements clock enable
	//       semantics --- one where the given 'D' argument (partially or fully)
	//       drives one of its two inputs
	//   (2) Starting from, or continuing onto, another optional $mux cell that
	//       implements synchronous reset semantics --- one where the given 'D'
	//       argument (or the clock enable $mux output) drives one of its two inputs
	//       and where the other input is fully zero
	//   (3) Match for a $dff cell (whose 'D' input is the 'D' argument, or the
	//       output of the previous clock enable or reset $mux cells)
	DspFf out_dffe(const MatchPatternBase &pm, const SigSpec &argD, SigBit clock) const
	{
		DspFf found = {};
		for (auto c : argD.chunks())
			// Abandon matches when 'D' has the keep attribute set
			if (c.wire->get_bool_attribute(ID::keep))
				return found;
		for (auto &[ff, offset] : pm.candidates(by_d.find(argD[0]))) {
			// Check that the rest of argD is present
			if (GetSize(pm.port(ff, ID::D)) < offset + GetSize(argD))
				continue;
			if (pm.port(ff, ID::D).extract(offset, GetSize(argD)) != argD)
				continue;
			if (clock != SigBit() && pm.port(ff, ID::CLK)[0] != clock)
				continue;
			SigSpec D = pm.port(ff, ID::D);
			SigSpec Q = pm.port(ff, ID::Q);
			SigSpec argQ = argD;
			argQ.replace(D, Q);

			// Abandon matches when 'Q' has a non-zero init attribute set
			// (not supported by the DSP)
			bool init_ok = true;
			for (auto c : argQ.chunks())
				if (nonzero_init(c)) {
					init_ok = false;
					break;
				}
			if (!init_ok)
				continue;

			found.cell = ff;
			found.sig = argQ;
			found.clock = pm.port(ff, ID::CLK);
		}
		return found;
	}

	// Take an input register for a DSP register slot: on a match, record the
	// flop in n.*ff and move n.*sig and n.clock to its input side. With
	// same_controls set, the flop must share its enable and reset with it.
	template <typename Match>
	bool absorb_in(const MatchPatternBase &pm, Match &n, Cell *Match::*ff, SigSpec Match::*sig, Cell *same_controls = nullptr, bool allow_async = false) const
	{
		DspFf found = in_dffe(pm, n.*sig, n.clock, allow_async);
		if (!found.cell || (same_controls && !dsp_same_ff_controls(pm, found.cell, same_controls)))
			return false;
		n.*ff = found.cell;
		n.clock = found.clock;
		n.*sig = found.sig;
		return true;
	}

	template <typename Match>
	bool absorb_in_async(const MatchPatternBase &pm, Match &n, Cell *Match::*ff, SigSpec Match::*sig) const
	{
		return absorb_in(pm, n, ff, sig, nullptr, true);
	}

	template <typename Match>
	bool absorb_out(const MatchPatternBase &pm, Match &n, Cell *Match::*ff, SigSpec Match::*sig) const
	{
		DspFf found = out_dffe(pm, n.*sig, n.clock);
		if (!found.cell)
			return false;
		n.*ff = found.cell;
		n.clock = found.clock;
		n.*sig = found.sig;
		return true;
	}
};

YOSYS_NAMESPACE_END

#endif
