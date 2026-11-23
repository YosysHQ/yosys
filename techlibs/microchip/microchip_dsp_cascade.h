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

#ifndef MICROCHIP_DSP_CASCADE_H
#define MICROCHIP_DSP_CASCADE_H

#include "techlibs/microchip/microchip_dsp_common.h"

YOSYS_NAMESPACE_BEGIN

// This file describes the third of three pattern matcher setups that
//   forms the `microchip_dsp` pass described in microchip_dsp.cc
// At a high level, it works as follows:
//   (1) Starting from a DSP cell that
//         (a) CDIN_FDBK_SEL is set to default "00"
//         (b) doesn't already use the 'PCOUT' port
//   (2) Match another DSP cell that
//         (a) does not have the CREG enabled,
//         (b) 'C' port is driven by the 'P' output of the previous DSP cell
//         (c) has its 'PCIN' port unused
//   (3) Recursively go to (2) until no more matches possible, keeping track
//       of the longest possible chain found
//   (4) The longest chain is then divided into chunks of no more than
//       MAX_DSP_CASCADE in length (to prevent long cascades that exceed the
//       height of a DSP column) with each DSP in each chunk being rewritten
//       to use [ABP]COUT -> [ABP]CIN cascading as appropriate

struct MicrochipDspCascadeMatch
{
	Cell *next = nullptr;
	Cell *first = nullptr;
	Cell *nextP = nullptr;
};

struct MicrochipDspCascade : MatchPattern<MicrochipDspCascade, MicrochipDspCascadeMatch>
{
	// Maximum of 24 cascaded blocks
	static constexpr int MAX_DSP_CASCADE = 24;

	// NOTE: Chain vector
	//  +--------+      +--------+
	//  | first  |----> |  next  | ----> ...
	//  +--------+      +--------+
	//  first.COUT cascades to next.CIN, so on and so forth
	vector<std::tuple<Cell*,int>> chain = {};
	vector<std::tuple<Cell*,int>> longest_chain = {};
	std::set<Cell*> visited = {};

	vector<Cell*> first_cells = {};
	vector<Cell*> nextP_cells = {};

	MicrochipDspCascade(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &MicrochipDspCascade::match_first)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::MACC_PA) && port(cell, ID::CDIN_FDBK_SEL, Const(0, 2)) == Const::from_string("00") &&
					nusers(port(cell, ID::CDOUT, SigSpec())) <= 1)
				first_cells.push_back(cell);
			// find candidates where nextP.C port is driven (maybe partially) by chain's tail DSP.P port
			//      and with no registers in between (since cascade path cannot be pipelined)

			// reg C must not be used
			if (port(cell, ID::C_BYPASS, SigSpec()).is_fully_ones() &&
					// must be same DSP type
					cell->type.in(ID::MACC_PA) &&
					// port C should be driven by something
					nusers(port(cell, ID::C, SigSpec())) > 1 &&
					// CIN must be unused
					nusers(port(cell, ID::PCIN, SigSpec())) == 0 &&
					// should not have internal feedback connection
					port(cell, ID::CDIN_FDBK_SEL, SigSpec()).is_fully_zero() &&
					// SHIFT should be unused
					port(cell, ID::ARSHFT17_BYPASS).is_fully_ones() &&
					port(cell, ID::ARSHFT17).is_fully_zero() &&
					nusers(port(cell, ID::ARSHFT17, SigSpec())) == 0)
				nextP_cells.push_back(cell);
		}
	}

	// (1) Starting from a DSP cell that
	//     (a) CDIN_FDBK_SEL is set to default "00"
	//     (b) doesn't already use the 'PCOUT' port
	void match_first(const Match &m)
	{
		match_each(m, first_cells, &Match::first, &MicrochipDspCascade::code_chain);
	}

	// (4) The longest chain is then divided into chunks of no more than
	//     MAX_DSP_CASCADE in length (to prevent long cascades that exceed the
	//     height of a DSP column) with each DSP in each chunk being rewritten
	//     to use [ABP]COUT -> [ABP]CIN cascading as appropriate
	void code_chain(const Match &m)
	{
		visited.clear();
		visited.insert(m.first);

		longest_chain.clear();
		chain.emplace_back(m.first, -1);
		tail(m);

		// longest cascade chain has been found with DSP "first" being the head of the chain
		// do some post processing

		chain.pop_back();
		visited.clear();
		log_assert(chain.empty());

		if (GetSize(longest_chain) > 1) {
			Cell *dsp = std::get<0>(longest_chain.front());

			Cell *dsp_pcin = {};
			int SHIFT = -1;
			for (int i = 1; i < GetSize(longest_chain); i++) {
				log_assert(dsp->type.in(ID::MACC_PA));

				std::tie(dsp_pcin,SHIFT) = longest_chain[i];

				// Chain length exceeds the maximum cascade length, must split it up
				if (i % MAX_DSP_CASCADE > 0) {
					Wire *cascade = module->addWire(NEW_ID, 48);

					// zero port C and move wire to cascade
					dsp_pcin->setPort(ID::C, Const(0, 48));
					dsp_pcin->setPort(ID::CDIN, cascade);
					dsp->setPort(ID::CDOUT, cascade);

					// Configure wire to cascade the dsps
					add_siguser(cascade, dsp_pcin);
					add_siguser(cascade, dsp);

					// configure mux to use cascade for signal E
					SigSpec cdin_fdbk_sel = port(dsp_pcin, ID::CDIN_FDBK_SEL, Const(0, 2));
					cdin_fdbk_sel[1] = State::S1;
					dsp_pcin->setPort(ID::CDIN_FDBK_SEL, cdin_fdbk_sel);

					// check if shifting is required for wide multiplier implmentation
					if (SHIFT == 17)
					{
						dsp_pcin->setPort(ID::ARSHFT17, State::S1);
					}


					log_debug("PCOUT -> PCIN cascade for %s -> %s\n", dsp, dsp_pcin);

				} else {
					log_debug("  Blocking %s -> %s cascade (exceeds max: %d)\n", dsp, dsp_pcin, MAX_DSP_CASCADE);
				}

				dsp = dsp_pcin;
			}

			accept(m);
		}
	}

	// ------------------------------------------------------------------

	// (2) Match another DSP cell that
	//          (a) does not have the CREG enabled,
	//          (b) 'C' port is driven by the 'P' output of the previous DSP cell
	//          (c) has its 'PCIN' port unused
	void tail(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *nextP : candidates(nextP_cells)) {
			// current DSP cell can be cascaded with the back of the cascade chain
			if (!(port(nextP, ID::C)[0] == port(std::get<0>(chain.back()), ID::P)[0] || port(nextP, ID::C)[0] == port(std::get<0>(chain.back()), ID::P)[17]))
				continue;
			Match n = m;
			n.nextP = nextP;
			if (descend(frame, nextP, &MicrochipDspCascade::tail_code_next, n))
				return;
		}

		match_none(m, &Match::nextP, &MicrochipDspCascade::tail_code_next);
	}

	void tail_code_next(const Match &m)
	{
		Match n = m;
		n.next = n.nextP;

		// keep DSP type consistent in the chain
		// currently since we only have one type anyways, this line is always false
		if (n.next && n.next->type != n.first->type) return;

		// break infinite recursion when there's a combinational loop
		if (visited.count(n.next) > 0) return;

		tail_code_chain(n);
	}

	// (3) Recursively go to (2) until no more matches possible, recording the
	//     longest possible chain
	void tail_code_chain(const Match &m)
	{
		if (m.next) {
			SigSpec driver_sigP = port(std::get<0>(chain.back()), ID::P);
			int shift = 0;
			if (port(m.next, ID::C)[0] == port(std::get<0>(chain.back()), ID::P)[17]) shift = 17;

			chain.emplace_back(m.next, shift);
			visited.insert(m.next);

			SigSpec sigC = microchip_dsp_unextend(port(m.next, ID::C));

			// Make sure driverDSP.P === DSP.C
			if (GetSize(sigC) + shift <= GetSize(driver_sigP) && driver_sigP.extract(shift, GetSize(sigC)) == sigC)
			{
				tail(m);
			}
		} else {
			if (GetSize(chain) > GetSize(longest_chain))
				longest_chain = chain;
		}

		if (m.next)
		{
			visited.erase(m.next);
			chain.pop_back();
		}
	}
};

YOSYS_NAMESPACE_END

#endif
