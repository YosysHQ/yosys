#ifndef XILINX_DSP_CREG_H
#define XILINX_DSP_CREG_H

#include "techlibs/common/dsp_ff.h"

YOSYS_NAMESPACE_BEGIN

// This file describes the second of three pattern matcher setups that
//   forms the `xilinx_dsp` pass described in xilinx_dsp.cc
// At a high level, it works as follows:
//   (1) Starting from a DSP48* cell that (a) doesn't have a CREG already,
//       and (b) uses the 'C' port
//   (2) Match the driver of the 'C' input to a possible $dff cell (CREG)
//       (attached to at most two $mux cells that implement clock-enable or
//        reset functionality, using a subpattern in dsp_ff.h)
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

struct XilinxDspPackCMatch
{
	SigBit clock = {};
	SigSpec sigC = {};
	SigSpec sigP = {};
	Cell *ffC = nullptr;
	Cell *dsp = nullptr;
};

struct XilinxDspPackC : MatchPattern<XilinxDspPackC, XilinxDspPackCMatch>
{
	vector<Cell*> dsp_cells = {};
	DspFfIndex ff_index = {};

	XilinxDspPackC(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &XilinxDspPackC::match_dsp)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::DSP48A, ID::DSP48A1, ID::DSP48E1) &&
					param(cell, ID::CREG).as_int() == 0 &&
					nusers(port(cell, ID::C, SigSpec())) > 1)
				dsp_cells.push_back(cell);
			ff_index.add_input(*this, cell);
		}
	}

	// (1) Starting from a DSP48* cell that (a) doesn't have a CREG already,
	//     and (b) uses the 'C' port
	void match_dsp(const Match &m)
	{
		match_each(m, dsp_cells, &Match::dsp, &XilinxDspPackC::code_signals);
	}

	void code_signals(const Match &m)
	{
		Match n = m;
		n.sigC = dsp_unextend(port(n.dsp, ID::C, SigSpec()));

		SigSpec P = port(n.dsp, ID::P);
		if (!n.dsp->type.in(ID::DSP48E1) ||
				param(n.dsp, ID::USE_MULT).decode_string() == "MULTIPLY") {
			// Only care about those bits that are used
			int i = dsp_used_width(*this, P);
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
		ff_index.absorb_in(*this, n, &Match::ffC, &Match::sigC);
		code_accept(n);
	}

	void code_accept(const Match &m)
	{
		if (m.ffC)
			accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
