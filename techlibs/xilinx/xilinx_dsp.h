#ifndef XILINX_DSP_H
#define XILINX_DSP_H

#include "techlibs/common/dsp_ff.h"

YOSYS_NAMESPACE_BEGIN

// This file describes the main pattern matcher setup (of three total) that
//   forms the `xilinx_dsp` pass described in xilinx_dsp.cc
// At a high level, it works as follows:
//   ( 1) Starting from a DSP48E1 cell
//   ( 2) Match the driver of the 'A' input to a possible $sdffe cell (ADREG)
//        If ADREG matched, treat 'A' input as input of ADREG
//   ( 3) Match the driver of the 'A' and 'D' inputs for a possible $add cell
//       (pre-adder)
// 	 (3.1) Match the driver of the 'A' and 'D' inputs for a possible $sub cell
//         (pre-adder)
//   ( 4) If pre-adder was present, find match 'A' input for A2REG
//        If pre-adder was not present, move ADREG to A2REG
//        If A2REG, then match 'A' input for A1REG
//   ( 5) Match 'B' input for B2REG
//        If B2REG, then match 'B' input for B1REG
//   ( 6) Match 'D' input for DREG
//   ( 7) Match 'P' output that exclusively drives an MREG
//   ( 8) Match 'P' output that exclusively drives one of two inputs to an $add
//        cell (post-adder).
//        The other input to the adder is assumed to come in from the 'C' input
//        (note: 'P' -> 'C' connections that exist for accumulators are
//         recognised in xilinx_dsp.cc).
//   ( 9) Match 'P' output that exclusively drives a PREG
//   (10) If post-adder and PREG both present, match for a $mux cell driving
//        the 'C' input, where one of the $mux's inputs is the PREG output.
//        This indicates an accumulator situation, and one where a $mux exists
//        to override the accumulated value:
//             +--------------------------------+
//             |   ____                         |
//             +--|    \                        |
//                |$mux|-+                      |
//         'C' ---|____/ |                      |
//                       | /-------\   +----+   |
//            +----+     +-| post- |___|PREG|---+ 'P'
//            |MREG|------ | adder |   +----+
//            +----+       \-------/
//   (11) If PREG present, match for a greater-than-or-equal $ge cell attached
//        to the 'P' output where it is compared to a constant that is a
//        power-of-2: e.g. `assign overflow = (PREG >= 2**40);`
//        In this scenario, the pattern detector functionality of a DSP48E1 can
//        to implement this function
// Notes:
//   - The intention of this pattern matcher is for it to be compatible with
//     DSP48E1 cells inferred from multiply operations by Yosys, as well as for
//     user instantiations that may already contain the cells being packed...
//     (though the latter is currently untested)
//   - Since the $sdffe pattern is used
//     for each *REG match, it has been factored out into two subpatterns:
//     in_dffe and out_dffe in dsp_ff.h.
//   - Matching for pattern detector features is currently incomplete. For
//     example, matching for underflow as well as overflow detection is
//     possible, as would auto-reset, enabling saturated arithmetic, detecting
//     custom patterns, etc.

struct XilinxDspPackMatch
{
	SigBit clock = {};
	SigSpec sigA = {};
	SigSpec sigB = {};
	SigSpec sigC = {};
	SigSpec sigD = {};
	SigSpec sigM = {};
	SigSpec sigP = {};
	IdString postAddAB = {};
	IdString postAddMuxAB = {};
	Cell *ffAD = nullptr;
	Cell *ffA1 = nullptr;
	Cell *ffA2 = nullptr;
	Cell *ffB1 = nullptr;
	Cell *ffB2 = nullptr;
	Cell *ffD = nullptr;
	Cell *ffM = nullptr;
	Cell *ffP = nullptr;
	Cell *dsp = nullptr;
	Cell *preAdd = nullptr;
	Cell *preSub = nullptr;
	Cell *postAdd = nullptr;
	Cell *postAddMux = nullptr;
	Cell *overflow = nullptr;
};

struct XilinxDspPack : MatchPattern<XilinxDspPack, XilinxDspPackMatch>
{
	struct PortChoice {
		Cell *cell = nullptr;
		IdString AB = {};
	};

	vector<Cell*> dsp_cells = {};
	MatchIndex<SigSpec> preAdd_index = {};
	MatchIndex<SigSpec> preSub_index = {};
	MatchIndex<SigBit, PortChoice> postAdd_index = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>, PortChoice> postAddMux_index = {};
	MatchIndex<SigSpec> overflow_index = {};
	DspFfIndex ff_index = {};

	XilinxDspPack(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &XilinxDspPack::match_dsp)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::DSP48E1))
				dsp_cells.push_back(cell);
			if (cell->type.in(ID($add)) &&
					// Output has to be 25 bits or less
					GetSize(port(cell, ID::Y)) <= 25 &&
					nusers(port(cell, ID::Y)) == 2)
				for (IdString AB : {ID::A, ID::B}) {
					IdString BA = (AB == ID::A ? ID::B : ID::A);
					// A port has to be 30 bits or less
					// D port has to be 25 bits or less
					if (GetSize(port(cell, AB)) <= 30 && GetSize(port(cell, BA)) <= 25)
						preAdd_index.add(port(cell, ID::Y), cell);
				}
			if (cell->type.in(ID($sub)) &&
					// Output has to be 25 bits or less
					GetSize(port(cell, ID::Y)) <= 25 &&
					nusers(port(cell, ID::Y)) == 2 &&
					// D port has to be 25 bits or less
					GetSize(port(cell, ID::A)) <= 25 &&
					// A port has to be 30 bits or less
					GetSize(port(cell, ID::B)) <= 30)
				preSub_index.add(port(cell, ID::Y), cell);
			if (cell->type.in(ID($add)) && GetSize(port(cell, ID::Y)) <= 48)
				for (IdString AB : {ID::A, ID::B})
					if (nusers(port(cell, AB)) == 2)
						postAdd_index.add(port(cell, AB)[0], {cell, AB});
			if (cell->type.in(ID($mux)) && nusers(port(cell, ID::Y)) == 2)
				for (IdString AB : {ID::A, ID::B})
					postAddMux_index.add({port(cell, AB), port(cell, ID::Y)}, {cell, AB});
			if (cell->type.in(ID($ge)) &&
					GetSize(port(cell, ID::Y)) <= 48 &&
					port(cell, ID::B).is_fully_const()) {
				Const B = port(cell, ID::B).as_const();
				if (std::count(B.begin(), B.end(), State::S1) == 1)
					overflow_index.add(port(cell, ID::A), cell);
			}
			ff_index.add_input(*this, cell);
			ff_index.add_output(*this, cell);
		}
	}

	bool preadder_usable(const Match &m) const
	{
		return (m.sigD.empty() || m.sigD.is_fully_zero()) &&
				// Ensure that preAdder not already used
				param(m.dsp, ID::USE_DPORT).decode_string() == "FALSE" &&
				port(m.dsp, ID::INMODE, Const(0, 5)).is_fully_zero();
	}

	// (1) Starting from a DSP48E1 cell
	void match_dsp(const Match &m)
	{
		match_each(m, dsp_cells, &Match::dsp, &XilinxDspPack::code_signals);
	}

	void code_signals(const Match &m)
	{
		Match n = m;
		n.sigA = dsp_unextend(port(n.dsp, ID::A));
		n.sigB = dsp_unextend(port(n.dsp, ID::B));

		n.sigC = port(n.dsp, ID::C, SigSpec());
		n.sigD = port(n.dsp, ID::D, SigSpec());

		SigSpec P = port(n.dsp, ID::P);
		if (param(n.dsp, ID::USE_MULT).decode_string() == "MULTIPLY") {
			// Only care about those bits that are used
			int i = {};
			for (i = GetSize(P)-1; i >= 0; i--)
				if (nusers(P[i]) > 1)
					break;
			i++;
			log_assert(nusers(P.extract_end(i)) <= 1);
			// This sigM could have no users if downstream sinks (e.g. $add) is
			//   narrower than $mul result, for example
			if (i == 0)
				return;
			n.sigM = P.extract(0, i);
		}
		else
			n.sigM = P;

		n.clock = port(n.dsp, ID::CLK, SigBit());
		code_ffAD(n);
	}

	// (2) Match the driver of the 'A' input to a possible $sdffe cell (ADREG)
	//     If matched, treat 'A' input as input of ADREG
	void code_ffAD(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::ADREG).as_int() == 0) {
			ff_index.absorb_in(*this, n, &Match::ffAD, &Match::sigA);
		}
		match_preAdd(n);
	}

	// (3) Match the driver of the 'A' and 'D' inputs for a possible $add cell
	//     (pre-adder)
	void match_preadder(const Match &m, const MatchIndex<SigSpec> &index, Cell *Match::*state, Stage next)
	{
		if (preadder_usable(m)) {
			MatchFrame frame(ctx);
			for (Cell *cell : candidates(index.find(m.sigA))) {
				Match n = m;
				n.*state = cell;
				if (descend(frame, cell, next, n))
					return;
			}
		}
		match_none(m, state, next);
	}

	void match_preAdd(const Match &m)
	{
		match_preadder(m, preAdd_index, &Match::preAdd, &XilinxDspPack::code_preAdd);
	}

	void code_preAdd(const Match &m)
	{
		Match n = m;
		if (n.preAdd) {
			n.sigA = port(n.preAdd, ID::A);
			n.sigD = port(n.preAdd, ID::B);
		}
		match_preSub(n);
	}

	// (3.1) Match the driver of the 'A' and 'D' inputs for a possible $sub cell
	//     (pre-adder)
	void match_preSub(const Match &m)
	{
		match_preadder(m, preSub_index, &Match::preSub, &XilinxDspPack::code_preSub);
	}

	void code_preSub(const Match &m)
	{
		Match n = m;
		if (n.preSub) {
			n.sigD = port(n.preSub, ID::A);
			n.sigA = port(n.preSub, ID::B);
		}
		code_ffA(n);
	}

	// (4) If pre-adder was present, find match 'A' input for A2REG
	//     If pre-adder was not present, move ADREG to A2REG
	//     Then match 'A' input for A1REG
	void code_ffA(const Match &m)
	{
		Match n = m;
		// Only search for ffA2 if there was a pre-adder
		//   (otherwise ffA2 would have been matched as ffAD)
		if (n.preAdd || n.preSub) {
			if (param(n.dsp, ID::AREG).as_int() == 0) {
				ff_index.absorb_in(*this, n, &Match::ffA2, &Match::sigA);
			}
		}
		// And if there wasn't a pre-adder,
		//   move AD register to A
		else if (n.ffAD) {
			log_assert(!n.ffA2);
			std::swap(n.ffA2, n.ffAD);
		}

		// Now attempt to match A1
		if (n.ffA2)
			ff_index.absorb_in(*this, n, &Match::ffA1, &Match::sigA, n.ffA2);
		code_ffB(n);
	}

	// (5) Match 'B' input for B2REG
	//     If B2REG, then match 'B' input for B1REG
	void code_ffB(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::BREG).as_int() == 0)
			if (ff_index.absorb_in(*this, n, &Match::ffB2, &Match::sigB))
				// Now attempt to match B1
				ff_index.absorb_in(*this, n, &Match::ffB1, &Match::sigB, n.ffB2);
		code_ffD(n);
	}

	// (6) Match 'D' input for DREG
	void code_ffD(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::DREG).as_int() == 0) {
			ff_index.absorb_in(*this, n, &Match::ffD, &Match::sigD);
		}
		code_ffM(n);
	}

	// (7) Match 'P' output that exclusively drives an MREG
	void code_ffM(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::MREG).as_int() == 0 && nusers(n.sigM) == 2) {
			ff_index.absorb_out(*this, n, &Match::ffM, &Match::sigM);
		}
		n.sigP = n.sigM;
		match_postAdd(n);
	}

	// (8) Match 'P' output that exclusively drives one of two inputs to an $add
	//     cell (post-adder).
	//     The other input to the adder is assumed to come in from the 'C' input
	//     (note: 'P' -> 'C' connections that exist for accumulators are
	//      recognised in xilinx_dsp.cc).
	void match_postAdd(const Match &m)
	{
		// Ensure that Z mux is not already used
		if (port(m.dsp, ID::OPMODE, SigSpec(0, 7)).extract(4,3).is_fully_zero()) {
			MatchFrame frame(ctx);
			for (auto &[postAdd, AB] : candidates(postAdd_index.find(m.sigP[0]))) {
				if (GetSize(port(postAdd, AB)) < GetSize(m.sigP))
					continue;
				if (port(postAdd, AB).extract(0, GetSize(m.sigP)) != m.sigP)
					continue;
				// Check that remainder of AB is a sign- or zero-extension
				if (!dsp_is_extension_of(port(postAdd, AB), m.sigP))
					continue;
				Match n = m;
				n.postAdd = postAdd;
				n.postAddAB = AB;
				if (descend(frame, postAdd, &XilinxDspPack::code_postAdd, n))
					return;
			}
		}
		match_none(m, &Match::postAdd, &XilinxDspPack::code_postAdd);
	}

	void code_postAdd(const Match &m)
	{
		Match n = m;
		if (n.postAdd) {
			n.sigC = port(n.postAdd, n.postAddAB == ID::A ? ID::B : ID::A);
			n.sigP = port(n.postAdd, ID::Y);
		}
		code_ffP(n);
	}

	// (9) Match 'P' output that exclusively drives a PREG
	void code_ffP(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::PREG).as_int() == 0) {
			if (nusers(n.sigP) == 2) {
				ff_index.absorb_out(*this, n, &Match::ffP, &Match::sigP);
			}
		}
		match_postAddMux(n);
	}

	// (10) If post-adder and PREG both present, match for a $mux cell driving
	//      the 'C' input, where one of the $mux's inputs is the PREG output.
	//      This indicates an accumulator situation, and one where a $mux exists
	//      to override the accumulated value:
	//           +--------------------------------+
	//           |   ____                         |
	//           +--|    \                        |
	//              |$mux|-+                      |
	//       'C' ---|____/ |                      |
	//                     | /-------\   +----+   |
	//          +----+     +-| post- |___|PREG|---+ 'P'
	//          |MREG|------ | adder |   +----+
	//          +----+       \-------/
	void match_postAddMux(const Match &m)
	{
		if (m.postAdd && m.ffP) {
			MatchFrame frame(ctx);
			for (auto &[postAddMux, AB] : candidates(postAddMux_index.find({m.sigP, m.sigC}))) {
				Match n = m;
				n.postAddMux = postAddMux;
				n.postAddMuxAB = AB;
				if (descend(frame, postAddMux, &XilinxDspPack::code_postAddMux, n))
					return;
			}
		}
		match_none(m, &Match::postAddMux, &XilinxDspPack::code_postAddMux);
	}

	void code_postAddMux(const Match &m)
	{
		Match n = m;
		if (n.postAddMux)
			n.sigC = port(n.postAddMux, n.postAddMuxAB == ID::A ? ID::B : ID::A);
		match_overflow(n);
	}

	// (11) If PREG present, match for a greater-than-or-equal $ge cell attached to
	//      the 'P' output where it is compared to a constant that is a power-of-2:
	//      e.g. `assign overflow = (PREG >= 2**40);`
	//      In this scenario, the pattern detector functionality of a DSP48E1 can
	//      to implement this function
	void match_overflow(const Match &m)
	{
		if (m.ffP && param(m.dsp, ID::USE_PATTERN_DETECT).decode_string() == "NO_PATDET") {
			MatchFrame frame(ctx);
			for (Cell *overflow : candidates(overflow_index.find(m.sigP))) {
				Match n = m;
				n.overflow = overflow;
				if (descend(frame, overflow, &XilinxDspPack::accept, n))
					return;
			}
		}
		match_none(m, &Match::overflow, &XilinxDspPack::accept);
	}
};

YOSYS_NAMESPACE_END

#endif
