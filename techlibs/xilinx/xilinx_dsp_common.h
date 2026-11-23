#ifndef XILINX_DSP_COMMON_H
#define XILINX_DSP_COMMON_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

inline SigSpec xilinx_dsp_unextend(const SigSpec &sig)
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

inline bool xilinx_dsp_same_ff_controls(const MatchPatternBase &pm, Cell *ff, Cell *other)
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

inline bool xilinx_dsp_is_extension_of(const SigSpec &sig, const SigSpec &low)
{
	SigSpec high = sig.extract_end(GetSize(low));
	return high == SigSpec(low[GetSize(low)-1], GetSize(high)) || high == SigSpec(State::S0, GetSize(high));
}

struct XilinxDspFf
{
	Cell *cell = nullptr;
	SigSpec sig = {};
	SigBit clock = {};
};

struct XilinxDspFfIndex
{
	struct FfSlice {
		Cell *cell = nullptr;
		int offset = {};
	};

	MatchIndex<SigBit, FfSlice> by_q = {};
	MatchIndex<SigBit, FfSlice> by_d = {};

	static bool usable(const MatchPatternBase &pm, Cell *cell)
	{
		return cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe)) &&
				// DSP48E1 does not support clock inversion
				pm.param(cell, ID::CLK_POLARITY).as_bool();
	}

	void add_input(const MatchPatternBase &pm, Cell *cell)
	{
		if (usable(pm, cell))
			for (int offset = 0; offset < GetSize(pm.port(cell, ID::D)); offset++)
				by_q.add(pm.port(cell, ID::Q)[offset], {cell, offset});
	}

	void add_output(const MatchPatternBase &pm, Cell *cell)
	{
		if (usable(pm, cell))
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
	XilinxDspFf in_dffe(const MatchPatternBase &pm, const SigSpec &argQ, SigBit clock) const
	{
		XilinxDspFf found = {};
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
			// (not supported by DSP48E1)
			if (nonzero_init(c))
				return found;
		}
		for (auto &[ff, offset] : by_q.find(argQ[0])) {
			if (pm.blacklisted(ff))
				continue;
			// Check that reset value, if present, is fully 0.
			if (!ff->type.in(ID($dff), ID($dffe)) && !pm.param(ff, ID::SRST_VALUE).is_fully_zero())
				continue;
			// Check that the rest of argQ is present
			if (GetSize(pm.port(ff, ID::Q)) < offset + GetSize(argQ))
				continue;
			if (pm.port(ff, ID::Q).extract(offset, GetSize(argQ)) != argQ)
				continue;
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
	XilinxDspFf out_dffe(const MatchPatternBase &pm, const SigSpec &argD, SigBit clock) const
	{
		XilinxDspFf found = {};
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
			// (not supported by DSP48E1)
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
