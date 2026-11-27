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

#ifndef MICROCHIP_DSP_H
#define MICROCHIP_DSP_H

#include "techlibs/common/dsp_ff.h"

YOSYS_NAMESPACE_BEGIN

// This file describes the main pattern matcher setup (of three total) that
//   forms the `microchip_dsp` pass described in microchip_dsp.cc
// At a high level, it works as follows:
//   ( 1) Starting from a DSP cell. Capture DSP configurations as states
//   ( 2) Match for pre-adder
//   ( 3) Match for post-adder
//   ( 4) Match register 'A', 'B', 'D', 'P'
//   ( 5) If post-adder and PREG both present, check if PREG feeds into post-adder.
//        This indicates an accumulator situation like the ASCII diagram below:
//             +--------------------------------+
//             |_________                       |
//                       | /-------\   +----+   |
//            +----+     +-| post- |___|PREG|---+ 'P'
//            |MULT|------ | adder |   +----+
//            +----+       \-------/

struct MicrochipDspPackMatch
{
	SigBit clock = {};
	SigSpec sigA = {};
	SigSpec sigB = {};
	SigSpec sigC = {};
	SigSpec sigD = {};
	SigSpec sigP = {};
	Cell *ffA = nullptr;
	Cell *ffB = nullptr;
	Cell *ffD = nullptr;
	Cell *ffP = nullptr;
	Cell *preAdderStatic = nullptr;
	Cell *postAdderStatic = nullptr;
	bool moveBtoA = {};
	bool useFeedBack = {};
	Cell *dsp = nullptr;
	// static ports, used to detect dsp configuration
	SigSpec bypassA = {};
	SigSpec bypassB = {};
	SigSpec bypassD = {};
	SigSpec bypassP = {};
	SigSpec bypassPASUB = {};
	// Variables used for subpatterns
	IdString postAddAB = {};
	Cell *postAdd = nullptr;
	Cell *preAdd = nullptr;
};

struct MicrochipDspPack : MatchPattern<MicrochipDspPack, MicrochipDspPackMatch>
{
	struct PortChoice {
		Cell *cell = nullptr;
		IdString AB = {};
	};

	Cell *u_preAdderStatic = nullptr;
	Cell *u_postAdderStatic = nullptr;
	IdString u_postAddAB = {};

	vector<Cell*> dsp_cells = {};
	MatchIndex<SigBit, PortChoice> postAdd_index = {};
	vector<Cell*> preAdd_cells = {};
	DspFfIndex ff_index = {};

	MicrochipDspPack(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &MicrochipDspPack::match_dsp)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::MACC_PA))
				dsp_cells.push_back(cell);
			if (cell->type.in(ID($add), ID($sub)) && GetSize(port(cell, ID::Y)) <= 48) {
				// AB is the port that connects MUL to ADD
				for (IdString AB : {ID::A, ID::B})
					if (nusers(port(cell, AB)) == 2)
						postAdd_index.add(port(cell, AB)[0], {cell, AB});
			}
			// can handle add or sub
			if (cell->type.in(ID($add), ID($sub)) &&
					// Output has to be 18 bits or less, and only has single fanout
					GetSize(port(cell, ID::Y)) <= 18 &&
					nusers(port(cell, ID::Y)) == 2 &&
					// Adder inputs must be 18 bits or less
					GetSize(port(cell, ID::A)) <= 18 &&
					GetSize(port(cell, ID::B)) <= 18)
				preAdd_cells.push_back(cell);
			ff_index.add_input(*this, cell);
			ff_index.add_output(*this, cell);
		}
	}

	// (1) Starting from a DSP cell
	void match_dsp(const Match &m)
	{
		match_each(m, dsp_cells, &Match::dsp, &MicrochipDspPack::code_signals);
	}

	// detect existing signals connected to DSP
	// detect configuration ports
	void code_signals(const Match &m)
	{
		Match n = m;
		//unextend to remove unused bits
		n.sigA = dsp_unextend(port(n.dsp, ID::A));
		n.sigB = dsp_unextend(port(n.dsp, ID::B));

		//update signals
		n.sigC = port(n.dsp, ID::C, SigSpec());
		n.sigD = port(n.dsp, ID::D, SigSpec());


		SigSpec P = port(n.dsp, ID::P);
		// Only care about bits that are used
		int i = dsp_used_width(*this, P);
		// This sigP could have no users if downstream sinks (e.g. $add) is
		//   narrower than $mul result, for example
		if (i == 0)
			return;
		n.sigP = P.extract(0, i);
		n.clock = port(n.dsp, ID::CLK, SigBit());

		code_bypass(n);
	}

	// capture static configuration ports
	void code_bypass(const Match &m)
	{
		Match n = m;
		n.bypassA = port(n.dsp, ID::A_BYPASS, SigSpec());
		n.bypassB = port(n.dsp, ID::B_BYPASS, SigSpec());
		n.bypassD = port(n.dsp, ID::D_BYPASS, SigSpec());
		n.bypassPASUB = port(n.dsp, ID::PASUB_BYPASS, SigSpec());
		n.bypassP = port(n.dsp, ID::P_BYPASS, SigSpec());
		code_preAdder(n);
	}

	// (2) Match for pre-adder
	//
	void code_preAdder(const Match &m)
	{
		Match n = m;
		preAddMatching(n);
		if (unwinding())
			return;
		n.preAdderStatic = u_preAdderStatic;
		n.moveBtoA = false;

		if (n.preAdderStatic) {

			if (port(n.preAdderStatic, ID::Y) == n.sigA)
			{
				//used for packing
				n.moveBtoA = true;

				// sigA should be the input to the multiplier without the preAdd. sigB and sigD should be
				//the preAdd inputs. If our "A" input into the multiplier is from the preAdd (not sigA), then
				// we basically swap it.
				n.sigA = n.sigB;
			}

			// port B of preAdderStatic must be mapped to port D of DSP for subtraction
			n.sigD = port(n.preAdderStatic, ID::B);
			n.sigB = port(n.preAdderStatic, ID::A);
		}
		code_postAdder(n);
	}

	//  (3) Match for post-adder
	//
	void code_postAdder(const Match &m)
	{
		Match n = m;
		u_postAdderStatic = nullptr;
		postAddMatching(n);
		if (unwinding())
			return;
		n.postAdderStatic = u_postAdderStatic;

		if (n.postAdderStatic) {
			//sigC will be whichever input to the postAdder that is NOT from the multiplier
			// u_postAddAB is the input to the postAdder from the multiplier
			n.sigC = port(n.postAdderStatic, u_postAddAB == ID::A ? ID::B : ID::A);
			n.sigP = port(n.postAdderStatic, ID::Y);
		}
		code_ffA(n);
	}

	// (4) Matching registers
	//
	// 'A' input for REG_A
	void code_ffA(const Match &m)
	{
		Match n = m;
		if (n.bypassA.is_fully_ones()){
			ff_index.absorb_in(*this, n, &Match::ffA, &Match::sigA);
		}
		code_ffB(n);
	}

	// 'B' input for REG_B
	void code_ffB(const Match &m)
	{
		Match n = m;
		if (n.bypassB.is_fully_ones()){
			ff_index.absorb_in(*this, n, &Match::ffB, &Match::sigB);
		}
		code_ffD(n);
	}

	// 'D' input for REG_D
	void code_ffD(const Match &m)
	{
		Match n = m;
		if (n.bypassD.is_fully_ones()){
			ff_index.absorb_in_async(*this, n, &Match::ffD, &Match::sigD);
		}
		code_ffP(n);
	}

	// 'P' output for REG_P
	void code_ffP(const Match &m)
	{
		Match n = m;
		if (n.bypassP.is_fully_ones() && nusers(n.sigP) == 2) {
			ff_index.absorb_out(*this, n, &Match::ffP, &Match::sigP);
		}
		code_useFeedBack(n);
	}

	// (5) If post-adder and PREG both present, check if PREG feeds into post-adder via port C.
	//        This indicates an accumulator situation. Port C can be freed
	//             +--------------------------------+
	//             |_________                       |
	//                       | /-------\   +----+   |
	//            +----+     +-| post- |___|PREG|---+ 'P'
	//            |MULT|------ | adder |   +----+
	//            +----+       \-------/
	void code_useFeedBack(const Match &m)
	{
		Match n = m;
		n.useFeedBack = false;
		if (n.postAdderStatic && n.ffP)	{
			if (n.sigC == n.sigP) {
				n.useFeedBack = true;
			}
		}

		code_accept(n);
	}

	// if any cells are absorbed, invoke the callback function
	void code_accept(const Match &m)
	{
		if (m.preAdderStatic || m.postAdderStatic) {
			if (accept(m))
				return;
		}
		if (m.ffA || m.ffB || m.ffD || m.ffP)
			accept(m);
	}

	// #######################
	// Subpattern for matching against post-adder
	//   Match 'P' output that exclusively drives one of two inputs to an $add
	//   cell (post-adder).
	//   The other input to the adder is assumed to come in from the 'C' input
	void postAddMatching(const Match &m)
	{
		MatchFrame frame(ctx);
		// has one input coming from multiplier
		for (auto &[postAdd, AB] : candidates(postAdd_index.find(m.sigP[0]))) {
			if (!(GetSize(port(postAdd, AB)) >= GetSize(m.sigP)))
				continue;
			if (!(port(postAdd, AB).extract(0, GetSize(m.sigP)) == m.sigP))
				continue;
			// Check that remainder of AB is a sign- or zero-extension
			if (!(port(postAdd, AB).extract_end(GetSize(m.sigP)) == SigSpec(m.sigP[GetSize(m.sigP)-1], GetSize(port(postAdd, AB))-GetSize(m.sigP)) || port(postAdd, AB).extract_end(GetSize(m.sigP)) == SigSpec(State::S0, GetSize(port(postAdd, AB))-GetSize(m.sigP))))
				continue;
			Match n = m;
			n.postAdd = postAdd;
			n.postAddAB = AB;
			if (descend(frame, postAdd, &MicrochipDspPack::postAddMatching_code_found, n))
				return;
		}
	}

	void postAddMatching_code_found(const Match &m)
	{
		if (m.postAdd->type.in(ID($sub)) && m.postAddAB == ID::A) {
			// if $sub, the multiplier output must match to $sub.B, otherwise no match
		} else {
			u_postAddAB = m.postAddAB;
			u_postAdderStatic = m.postAdd;
		}
	}

	// #######################
	// Subpattern for matching against pre-adder
	//		support static PASUB only
	void preAddMatching(const Match &m)
	{
		u_preAdderStatic = nullptr;

		// Ensure that preAdder not already used
		// Assume we can inspect port D to see if its all zeros.
		if (!(m.sigD.empty() || m.sigD.is_fully_zero()))
			return;
		if (!m.bypassB.is_fully_ones())
			return;
		if (!m.bypassD.is_fully_ones())
			return;
		if (!m.bypassPASUB.is_fully_ones())
			return;
		preAddMatching_match_preAdd(m);
	}

	bool preadd_feeds_mul(const Match &m, Cell *preAdd) const
	{
		// Output feeds into one of multiplier input
		return port(preAdd, ID::Y) == m.sigB || port(preAdd, ID::Y) == m.sigA;
	}

	void preAddMatching_match_preAdd(const Match &m)
	{
		match_each(m, preAdd_cells, &MicrochipDspPack::preadd_feeds_mul, &Match::preAdd, &MicrochipDspPack::preAddMatching_code_found);
	}

	void preAddMatching_code_found(const Match &m)
	{
		u_preAdderStatic = m.preAdd;
	}
};

YOSYS_NAMESPACE_END

#endif
