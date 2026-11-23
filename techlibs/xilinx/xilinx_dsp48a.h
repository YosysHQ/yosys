#ifndef XILINX_DSP48A_H
#define XILINX_DSP48A_H

#include "techlibs/xilinx/xilinx_dsp_common.h"

YOSYS_NAMESPACE_BEGIN

// This file describes the main pattern matcher setup (of three total) that
//   forms the `xilinx_dsp` pass described in xilinx_dsp.cc - version for
//   DSP48A/DSP48A1 (Spartan 3A DSP, Spartan 6).
// At a high level, it works as follows:
//   ( 1) Starting from a DSP48A/DSP48A1 cell
//   ( 2) Match the driver of the 'B' input to a possible $dff cell (B1REG)
//        If B1REG matched, treat 'B' input as input of B1REG
//   ( 3) Match the driver of the 'B' and 'D' inputs for a possible $add cell
//       (pre-adder)
//   ( 4) Match 'B' input for B0REG
//   ( 5) Match 'A' input for A1REG
//        If A1REG, then match 'A' input for A0REG
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
// Notes: see the notes in xilinx_dsp.h

struct XilinxDsp48aPackMatch
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
	Cell *ffA0 = nullptr;
	Cell *ffA1 = nullptr;
	Cell *ffB0 = nullptr;
	Cell *ffB1 = nullptr;
	Cell *ffD = nullptr;
	Cell *ffM = nullptr;
	Cell *ffP = nullptr;
	Cell *dsp = nullptr;
	Cell *preAdd = nullptr;
	Cell *postAdd = nullptr;
	Cell *postAddMux = nullptr;
};

struct XilinxDsp48aPack : MatchPattern<XilinxDsp48aPack, XilinxDsp48aPackMatch>
{
	struct PortChoice {
		Cell *cell = nullptr;
		IdString AB = {};
	};

	vector<Cell*> dsp_cells = {};
	MatchIndex<SigSpec> preAdd_index = {};
	MatchIndex<SigBit, PortChoice> postAdd_index = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>, PortChoice> postAddMux_index = {};
	XilinxDspFfIndex ff_index = {};

	XilinxDsp48aPack(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &XilinxDsp48aPack::match_dsp)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::DSP48A, ID::DSP48A1))
				dsp_cells.push_back(cell);
			if (cell->type.in(ID($add), ID($sub)) &&
					// Output has to be 18 bits or less
					GetSize(port(cell, ID::Y)) <= 18 &&
					nusers(port(cell, ID::Y)) == 2 &&
					// D port has to be 18 bits or less
					GetSize(port(cell, ID::A)) <= 18 &&
					// B port has to be 18 bits or less
					GetSize(port(cell, ID::B)) <= 18)
				preAdd_index.add(port(cell, ID::Y), cell);
			if (cell->type.in(ID($add)) && GetSize(port(cell, ID::Y)) <= 48)
				for (IdString AB : {ID::A, ID::B})
					if (nusers(port(cell, AB)) == 2)
						postAdd_index.add(port(cell, AB)[0], {cell, AB});
			if (cell->type.in(ID($mux)) && nusers(port(cell, ID::Y)) == 2)
				for (IdString AB : {ID::A, ID::B})
					postAddMux_index.add({port(cell, AB), port(cell, ID::Y)}, {cell, AB});
			ff_index.add_input(*this, cell);
			ff_index.add_output(*this, cell);
		}
	}

	bool preadder_usable(const Match &m) const
	{
		return (m.sigD.empty() || m.sigD.is_fully_zero()) &&
				param(m.dsp, ID::B0REG).as_int() == 0 &&
				// Ensure that preAdder not already used
				port(m.dsp, ID::OPMODE, SigSpec()).extract(4, 1).is_fully_zero();
	}

	// (1) Starting from a DSP48A/DSP48A1 cell
	void match_dsp(const Match &m)
	{
		match_each(m, dsp_cells, &Match::dsp, &XilinxDsp48aPack::code_signals);
	}

	void code_signals(const Match &m)
	{
		Match n = m;
		n.sigA = xilinx_dsp_unextend(port(n.dsp, ID::A));
		n.sigB = xilinx_dsp_unextend(port(n.dsp, ID::B));

		n.sigC = port(n.dsp, ID::C, SigSpec());
		n.sigD = port(n.dsp, ID::D, SigSpec());

		SigSpec P = port(n.dsp, ID::P);
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

		n.clock = port(n.dsp, ID::CLK, SigBit());
		code_ffB1(n);
	}

	// (2) Match the driver of the 'B' input to a possible $dff cell (B1REG)
	//     (attached to at most two $mux cells that implement clock-enable or
	//      reset functionality, using a subpattern in xilinx_dsp_common.h)
	//     If matched, treat 'B' input as input of B1REG
	void code_ffB1(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::B1REG).as_int() == 0 && param(n.dsp, ID::B0REG).as_int() == 0 && port(n.dsp, ID::OPMODE, SigSpec()).extract(4, 1).is_fully_zero()) {
			XilinxDspFf b1reg = ff_index.in_dffe(*this, n.sigB, n.clock);
			if (b1reg.cell) {
				n.ffB1 = b1reg.cell;
				n.clock = b1reg.clock;
				n.sigB = b1reg.sig;
			}
		}
		match_preAdd(n);
	}

	// (3) Match the driver of the 'B' and 'D' inputs for a possible $add cell
	//     (pre-adder)
	void match_preAdd(const Match &m)
	{
		if (preadder_usable(m)) {
			MatchFrame frame(ctx);
			for (Cell *preAdd : candidates(preAdd_index.find(m.sigB))) {
				Match n = m;
				n.preAdd = preAdd;
				if (descend(frame, preAdd, &XilinxDsp48aPack::code_preAdd, n))
					return;
			}
		}
		Match n = m;
		n.preAdd = nullptr;
		code_preAdd(n);
	}

	void code_preAdd(const Match &m)
	{
		Match n = m;
		if (n.preAdd) {
			n.sigD = port(n.preAdd, ID::A);
			n.sigB = port(n.preAdd, ID::B);
		}
		code_ffB0(n);
	}

	// (4) Match 'B' input for B0REG
	void code_ffB0(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::B0REG).as_int() == 0) {
			XilinxDspFf b0reg = ff_index.in_dffe(*this, n.sigB, n.clock);
			if (b0reg.cell && (!n.ffB1 || xilinx_dsp_same_ff_controls(*this, b0reg.cell, n.ffB1))) {
				n.ffB0 = b0reg.cell;
				n.clock = b0reg.clock;
				n.sigB = b0reg.sig;
			}
		}
		code_ffA(n);
	}

	// (5) Match 'A' input for A1REG
	//     If A1REG, then match 'A' input for A0REG
	void code_ffA(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::A0REG).as_int() == 0 && param(n.dsp, ID::A1REG).as_int() == 0) {
			XilinxDspFf a1reg = ff_index.in_dffe(*this, n.sigA, n.clock);
			if (a1reg.cell) {
				n.ffA1 = a1reg.cell;
				n.clock = a1reg.clock;
				n.sigA = a1reg.sig;

				// Now attempt to match A0
				XilinxDspFf a0reg = ff_index.in_dffe(*this, n.sigA, n.clock);
				if (a0reg.cell && xilinx_dsp_same_ff_controls(*this, a0reg.cell, n.ffA1)) {
					n.ffA0 = a0reg.cell;
					n.clock = a0reg.clock;
					n.sigA = a0reg.sig;
				}
			}
		}
		code_ffD(n);
	}

	// (6) Match 'D' input for DREG
	void code_ffD(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::DREG).as_int() == 0) {
			XilinxDspFf dreg = ff_index.in_dffe(*this, n.sigD, n.clock);
			if (dreg.cell) {
				n.ffD = dreg.cell;
				n.clock = dreg.clock;
				n.sigD = dreg.sig;
			}
		}
		code_ffM(n);
	}

	// (7) Match 'P' output that exclusively drives an MREG
	void code_ffM(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::MREG).as_int() == 0 && nusers(n.sigM) == 2) {
			XilinxDspFf mreg = ff_index.out_dffe(*this, n.sigM, n.clock);
			if (mreg.cell) {
				n.ffM = mreg.cell;
				n.clock = mreg.clock;
				n.sigM = mreg.sig;
			}
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
		if (port(m.dsp, ID::OPMODE, SigSpec()).extract(2,2).is_fully_zero()) {
			MatchFrame frame(ctx);
			for (auto &[postAdd, AB] : candidates(postAdd_index.find(m.sigP[0]))) {
				if (GetSize(port(postAdd, AB)) < GetSize(m.sigP))
					continue;
				if (port(postAdd, AB).extract(0, GetSize(m.sigP)) != m.sigP)
					continue;
				// Check that remainder of AB is a sign- or zero-extension
				if (!xilinx_dsp_is_extension_of(port(postAdd, AB), m.sigP))
					continue;
				Match n = m;
				n.postAdd = postAdd;
				n.postAddAB = AB;
				if (descend(frame, postAdd, &XilinxDsp48aPack::code_postAdd, n))
					return;
			}
		}
		Match n = m;
		n.postAdd = nullptr;
		code_postAdd(n);
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
				XilinxDspFf preg = ff_index.out_dffe(*this, n.sigP, n.clock);
				if (preg.cell) {
					n.ffP = preg.cell;
					n.clock = preg.clock;
					n.sigP = preg.sig;
				}
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
				if (descend(frame, postAddMux, &XilinxDsp48aPack::code_postAddMux, n))
					return;
			}
		}
		Match n = m;
		n.postAddMux = nullptr;
		code_postAddMux(n);
	}

	void code_postAddMux(const Match &m)
	{
		Match n = m;
		if (n.postAddMux)
			n.sigC = port(n.postAddMux, n.postAddMuxAB == ID::A ? ID::B : ID::A);
		accept(n);
	}
};

YOSYS_NAMESPACE_END

#endif
