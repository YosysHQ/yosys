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

#ifndef MICROCHIP_DSP_CREG_H
#define MICROCHIP_DSP_CREG_H

#include "techlibs/common/dsp_ff.h"

YOSYS_NAMESPACE_BEGIN

// This file describes the second of three pattern matcher setups that
//   forms the `microchip_dsp` pass described in microchip_dsp.cc
// At a high level, it works as follows:
//   (1) Starting from a DSP cell that (a) doesn't have a CREG already,
//       and (b) uses the 'C' port
//   (2) Match the driver of the 'C' input to a possible $dff cell (CREG)
//       (attached to at most two $mux cells that implement clock-enable or
//        reset functionality, using a subpattern in dsp_ff.h)
// Notes:
//   - Running CREG packing after microchip_dsp_pack is necessary since there is no
//     guarantee that the cell ordering corresponds to the "expected" case (i.e.
//     the order in which they appear in the source) thus the possiblity existed
//     where a register got packed as a CREG into a downstream DSP, while it should
//     have otherwise been a PREG of an upstream DSP that had not been visited.
//     yet.
//   - Each pattern is a class,
//     which when constructed, creates a custom database tailored to the
//     pattern contained within. Since the pattern in this file must be
//     executed after the pattern contained in microchip_dsp.h, it is necessary
//     to reconstruct this database.

struct MicrochipDspPackCMatch
{
	SigBit clock = {};
	SigSpec sigC = {};
	SigSpec sigP = {};
	Cell *ffC = nullptr;
	Cell *dsp = nullptr;
};

struct MicrochipDspPackC : MatchPattern<MicrochipDspPackC, MicrochipDspPackCMatch>
{
	vector<Cell*> dsp_cells = {};
	DspFfIndex ff_index = {};

	MicrochipDspPackC(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &MicrochipDspPackC::match_dsp)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::MACC_PA) && port(cell, ID::C_BYPASS, SigSpec()).is_fully_ones() && nusers(port(cell, ID::C, SigSpec())) > 1)
				dsp_cells.push_back(cell);
			ff_index.add_input(*this, cell);
		}
	}

	// (1) Starting from a DSP cell that (a) doesn't have a CREG already,
	//     and (b) uses the 'C' port
	void match_dsp(const Match &m)
	{
		match_each(m, dsp_cells, &Match::dsp, &MicrochipDspPackC::code_signals);
	}

	void code_signals(const Match &m)
	{
		Match n = m;
		n.sigC = dsp_unextend(port(n.dsp, ID::C, SigSpec()));

		SigSpec P = port(n.dsp, ID::P);

		// Only care about those bits that are used
		int i = dsp_used_width(*this, P);
		n.sigP = P.extract(0, i);

		n.clock = port(n.dsp, ID::CLK, SigBit());
		code_ffC(n);
	}

	// (2) Match the driver of the 'C' input to a possible $dff cell (CREG)
	//     (attached to at most two $mux cells that implement clock-enable or
	//      reset functionality, using the in_dffe subpattern)
	void code_ffC(const Match &m)
	{
		Match n = m;
		ff_index.absorb_in_async(*this, n, &Match::ffC, &Match::sigC);
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
