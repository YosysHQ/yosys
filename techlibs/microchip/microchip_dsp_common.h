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

#ifndef MICROCHIP_DSP_COMMON_H
#define MICROCHIP_DSP_COMMON_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

// Helper function to remove unused bits
inline SigSpec microchip_dsp_unextend(const SigSpec &sig)
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

struct MicrochipDspFf
{
	Cell *cell = nullptr;
	SigSpec sig = {};
	SigBit clock = {};
};

struct MicrochipDspFfIndex
{
	struct FfSlice {
		Cell *cell = nullptr;
		int offset = {};
	};

	MatchIndex<SigBit, FfSlice> by_q = {};
	MatchIndex<SigBit, FfSlice> by_d = {};

	void add_input(const MatchPatternBase &pm, Cell *cell)
	{
		// reg D has async rst
		// reg A, B has sync rst
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
	MicrochipDspFf in_dffe(const MatchPatternBase &pm, const SigSpec &argQ, SigBit clock, bool allow_async) const
	{
		MicrochipDspFf found = {};
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
			if (nonzero_init(c))
				return found;
		}
		for (auto &[ff, offset] : by_q.find(argQ[0])) {
			if (pm.blacklisted(ff))
				continue;
			// Check that the rest of argQ is present
			if (GetSize(pm.port(ff, ID::Q)) < offset + GetSize(argQ))
				continue;
			if (pm.port(ff, ID::Q).extract(offset, GetSize(argQ)) != argQ)
				continue;
			// only consider async rst flops when flag is set
			if (ff->type.in(ID($adff), ID($adffe)) && !allow_async)
				continue;
			// clock must be consistent
			if (clock != SigBit() && pm.port(ff, ID::CLK)[0] != clock)
				continue;
			// Check that reset value, if present, is fully 0.
			bool noResetFlop = ff->type.in(ID($dff), ID($dffe));
			bool srstZero = ff->type.in(ID($sdff), ID($sdffe)) && pm.param(ff, ID::SRST_VALUE).is_fully_zero();
			bool arstZero = ff->type.in(ID($adff), ID($adffe)) && pm.param(ff, ID::ARST_VALUE).is_fully_zero();
			bool resetLegal = noResetFlop || srstZero || arstZero;
			if (!resetLegal)
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

	MicrochipDspFf out_dffe(const MatchPatternBase &pm, const SigSpec &argD, SigBit clock) const
	{
		MicrochipDspFf found = {};
		for (auto c : argD.chunks())
			// Abandon matches when 'D' has the keep attribute set
			if (c.wire->get_bool_attribute(ID::keep))
				return found;
		for (auto &[ff, offset] : by_d.find(argD[0])) {
			if (pm.blacklisted(ff))
				continue;
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
};

YOSYS_NAMESPACE_END

#endif
