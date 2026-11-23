#ifndef XILINX_DSP_CREG_H
#define XILINX_DSP_CREG_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

// This file describes the second of three pattern matcher setups that
//   forms the `xilinx_dsp` pass described in xilinx_dsp.cc
// At a high level, it works as follows:
//   (1) Starting from a DSP48* cell that (a) doesn't have a CREG already,
//       and (b) uses the 'C' port
//   (2) Match the driver of the 'C' input to a possible $dff cell (CREG)
//       (attached to at most two $mux cells that implement clock-enable or
//        reset functionality, using a subpattern discussed below)
// Notes:
//   - Running CREG packing after xilinx_dsp_pack is necessary since there is no
//     guarantee that the cell ordering corresponds to the "expected" case (i.e.
//     the order in which they appear in the source) thus the possiblity existed
//     that a register got packed as a CREG into a downstream DSP that should
//     have otherwise been a PREG of an upstream DSP that had not been visited
//     yet
//   - Each pattern is a class, which when constructed, creates a custom
//     database tailored to the pattern contained within. Since the pattern in
//     this file must be executed after the pattern contained in xilinx_dsp.h,
//     it is necessary to reconstruct this database.

struct XilinxDspPackC : MatchPattern
{
	struct Match {
		SigBit clock = {};
		SigSpec sigC = {};
		SigSpec sigP = {};
		Cell *ffC = nullptr;
		Cell *dsp = nullptr;
		// Variables used for subpatterns
		SigSpec argQ = {};
		Cell *ff = nullptr;
	};
	using Callback = void (*)(XilinxDspPackC &, const Match &);

	struct FfSlice {
		Cell *cell = nullptr;
		int offset = {};
	};

	SigSpec dffD = {};
	SigBit dffclock = {};
	Cell *dff = nullptr;

	vector<Cell*> dsp_cells = {};
	MatchIndex<SigBit, FfSlice> ff_index = {};
	Callback on_accept = nullptr;

	XilinxDspPackC(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::DSP48A, ID::DSP48A1, ID::DSP48E1) &&
					param(cell, ID::CREG).as_int() == 0 &&
					nusers(port(cell, ID::C, SigSpec())) > 1)
				dsp_cells.push_back(cell);
			if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe)) &&
					// DSP48E1 does not support clock inversion
					param(cell, ID::CLK_POLARITY).as_bool())
				for (int offset = 0; offset < GetSize(port(cell, ID::D)); offset++)
					ff_index.add(port(cell, ID::Q)[offset], {cell, offset});
		}
	}

	int run(Callback callback = nullptr)
	{
		on_accept = callback;
		begin_run();
		match_dsp(Match{});
		return end_run();
	}

	bool accept(const Match &m)
	{
		accept_cnt++;
		if (on_accept)
			on_accept(*this, m);
		return unwinding();
	}

	static SigSpec unextend(const SigSpec &sig)
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

	// (1) Starting from a DSP48* cell that (a) doesn't have a CREG already,
	//     and (b) uses the 'C' port
	void match_dsp(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *dsp : dsp_cells) {
			if (blacklisted(dsp))
				continue;
			Match n = m;
			n.dsp = dsp;
			frame.enter(dsp);
			code_signals(n);
			if (frame.leave())
				return;
		}
	}

	void code_signals(const Match &m)
	{
		Match n = m;
		n.sigC = unextend(port(n.dsp, ID::C, SigSpec()));

		SigSpec P = port(n.dsp, ID::P);
		if (!n.dsp->type.in(ID::DSP48E1) ||
				param(n.dsp, ID::USE_MULT).decode_string() == "MULTIPLY") {
			// Only care about those bits that are used
			int i = {};
			for (i = GetSize(P)-1; i >= 0; i--)
				if (nusers(P[i]) > 1)
					break;
			i++;
			log_assert(nusers(P.extract_end(i)) <= 1);
			n.sigP = P.extract(0, i);
		}
		else
			n.sigP = P;

		n.clock = port(n.dsp, ID::CLK, SigBit());
		code_ffC(n);
	}

	// (2) Match the driver of the 'C' input to a possible $dff cell (CREG)
	//     (attached to at most two $mux cells that implement clock-enable or
	//      reset functionality, using the in_dffe subpattern)
	void code_ffC(const Match &m)
	{
		Match n = m;
		n.argQ = n.sigC;
		in_dffe(n);
		if (unwinding())
			return;
		if (dff) {
			n.ffC = dff;
			n.clock = dffclock;
			n.sigC = dffD;
		}
		code_accept(n);
	}

	void code_accept(const Match &m)
	{
		if (m.ffC)
			accept(m);
	}

	// #######################

	// Subpattern for matching against input registers, based on knowledge of the
	//   'Q' input.
	void in_dffe(const Match &m)
	{
		dff = nullptr;
		if (m.argQ.empty())
			return;
		for (const auto &c : m.argQ.chunks()) {
			// Abandon matches when 'Q' is a constant
			if (!c.wire)
				return;
			// Abandon matches when 'Q' has the keep attribute set
			if (c.wire->get_bool_attribute(ID::keep))
				return;
			// Abandon matches when 'Q' has a non-zero init attribute set
			// (not supported by DSP48E1)
			Const init = c.wire->attributes.at(ID::init, Const());
			if (!init.empty())
				for (auto b : init.extract(c.offset, c.width))
					if (b != State::Sx && b != State::S0)
						return;
		}
		in_dffe_match_ff(m);
	}

	void in_dffe_match_ff(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[ff, offset] : ff_index.find(m.argQ[0])) {
			if (blacklisted(ff))
				continue;
			// Check that reset value, if present, is fully 0.
			if (!(ff->type.in(ID($dff), ID($dffe)) || param(ff, ID::SRST_VALUE).is_fully_zero()))
				continue;
			// Check that the rest of argQ is present
			if (GetSize(port(ff, ID::Q)) < offset + GetSize(m.argQ))
				continue;
			if (port(ff, ID::Q).extract(offset, GetSize(m.argQ)) != m.argQ)
				continue;
			if (!(m.clock == SigBit() || port(ff, ID::CLK)[0] == m.clock))
				continue;
			Match n = m;
			n.ff = ff;
			frame.enter(ff);
			in_dffe_code_found(n);
			if (frame.leave())
				return;
		}
	}

	void in_dffe_code_found(const Match &m)
	{
		SigSpec Q = port(m.ff, ID::Q);
		dff = m.ff;
		dffclock = port(m.ff, ID::CLK);
		dffD = m.argQ;
		SigSpec D = port(m.ff, ID::D);
		dffD.replace(Q, D);
	}
};

YOSYS_NAMESPACE_END

#endif
