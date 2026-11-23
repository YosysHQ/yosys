#ifndef XILINX_DSP_H
#define XILINX_DSP_H

#include "kernel/matcher.h"

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
//     in_dffe and out_dffe located at the bottom of this file.
//   - Matching for pattern detector features is currently incomplete. For
//     example, matching for underflow as well as overflow detection is
//     possible, as would auto-reset, enabling saturated arithmetic, detecting
//     custom patterns, etc.

struct XilinxDspPack : MatchPattern
{
	struct Match {
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
		// Variables used for subpatterns
		SigSpec argQ = {};
		SigSpec argD = {};
		Cell *ff = nullptr;
	};
	using Callback = void (*)(XilinxDspPack &, const Match &);

	struct PortChoice {
		Cell *cell = nullptr;
		IdString AB = {};
	};

	struct FfSlice {
		Cell *cell = nullptr;
		int offset = {};
	};

	SigSpec dffD = {};
	SigSpec dffQ = {};
	SigBit dffclock = {};
	Cell *dff = nullptr;

	vector<Cell*> dsp_cells = {};
	MatchIndex<SigSpec> preAdd_index = {};
	MatchIndex<SigSpec> preSub_index = {};
	MatchIndex<SigBit, PortChoice> postAdd_index = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>, PortChoice> postAddMux_index = {};
	MatchIndex<SigSpec> overflow_index = {};
	MatchIndex<SigBit, FfSlice> in_ff_index = {};
	MatchIndex<SigBit, FfSlice> out_ff_index = {};
	Callback on_accept = nullptr;

	XilinxDspPack(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx)
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
			if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe)) &&
					// DSP48E1 does not support clock inversion
					param(cell, ID::CLK_POLARITY).as_bool())
				for (int offset = 0; offset < GetSize(port(cell, ID::D)); offset++) {
					in_ff_index.add(port(cell, ID::Q)[offset], {cell, offset});
					out_ff_index.add(port(cell, ID::D)[offset], {cell, offset});
				}
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

	bool preadder_usable(const Match &m) const
	{
		return (m.sigD.empty() || m.sigD.is_fully_zero()) &&
				// Ensure that preAdder not already used
				param(m.dsp, ID::USE_DPORT).decode_string() == "FALSE" &&
				port(m.dsp, ID::INMODE, Const(0, 5)).is_fully_zero();
	}

	bool same_ff_controls(Cell *ff, Cell *other) const
	{
		if (ff->type != other->type)
			return false;
		if (ff->type.in(ID($sdff), ID($sdffe), ID($sdffce))) {
			if (param(ff, ID::SRST_POLARITY) != param(other, ID::SRST_POLARITY))
				return false;
			if (port(ff, ID::SRST) != port(other, ID::SRST))
				return false;
		}
		if (ff->type.in(ID($dffe), ID($sdffe), ID($sdffce))) {
			if (param(ff, ID::EN_POLARITY) != param(other, ID::EN_POLARITY))
				return false;
			if (port(ff, ID::EN) != port(other, ID::EN))
				return false;
		}
		return true;
	}

	// (1) Starting from a DSP48E1 cell
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
		n.sigA = unextend(port(n.dsp, ID::A));
		n.sigB = unextend(port(n.dsp, ID::B));

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
			n.argQ = n.sigA;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff) {
				n.ffAD = dff;
				n.clock = dffclock;
				n.sigA = dffD;
			}
		}
		match_preAdd(n);
	}

	// (3) Match the driver of the 'A' and 'D' inputs for a possible $add cell
	//     (pre-adder)
	void match_preAdd(const Match &m)
	{
		if (preadder_usable(m)) {
			MatchFrame frame(ctx);
			for (Cell *preAdd : preAdd_index.find(m.sigA)) {
				if (blacklisted(preAdd))
					continue;
				Match n = m;
				n.preAdd = preAdd;
				frame.enter(preAdd);
				code_preAdd(n);
				if (frame.leave())
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
			n.sigA = port(n.preAdd, ID::A);
			n.sigD = port(n.preAdd, ID::B);
		}
		match_preSub(n);
	}

	// (3.1) Match the driver of the 'A' and 'D' inputs for a possible $sub cell
	//     (pre-adder)
	void match_preSub(const Match &m)
	{
		if (preadder_usable(m)) {
			MatchFrame frame(ctx);
			for (Cell *preSub : preSub_index.find(m.sigA)) {
				if (blacklisted(preSub))
					continue;
				Match n = m;
				n.preSub = preSub;
				frame.enter(preSub);
				code_preSub(n);
				if (frame.leave())
					return;
			}
		}
		Match n = m;
		n.preSub = nullptr;
		code_preSub(n);
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
				n.argQ = n.sigA;
				in_dffe(n);
				if (unwinding())
					return;
				if (dff) {
					n.ffA2 = dff;
					n.clock = dffclock;
					n.sigA = dffD;
				}
			}
		}
		// And if there wasn't a pre-adder,
		//   move AD register to A
		else if (n.ffAD) {
			log_assert(!n.ffA2);
			std::swap(n.ffA2, n.ffAD);
		}

		// Now attempt to match A1
		if (n.ffA2) {
			n.argQ = n.sigA;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff && same_ff_controls(dff, n.ffA2)) {
				n.ffA1 = dff;
				n.clock = dffclock;
				n.sigA = dffD;
			}
		}
		code_ffB(n);
	}

	// (5) Match 'B' input for B2REG
	//     If B2REG, then match 'B' input for B1REG
	void code_ffB(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::BREG).as_int() == 0) {
			n.argQ = n.sigB;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff) {
				n.ffB2 = dff;
				n.clock = dffclock;
				n.sigB = dffD;

				// Now attempt to match B1
				n.argQ = n.sigB;
				in_dffe(n);
				if (unwinding())
					return;
				if (dff && same_ff_controls(dff, n.ffB2)) {
					n.ffB1 = dff;
					n.clock = dffclock;
					n.sigB = dffD;
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
			n.argQ = n.sigD;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff) {
				n.ffD = dff;
				n.clock = dffclock;
				n.sigD = dffD;
			}
		}
		code_ffM(n);
	}

	// (7) Match 'P' output that exclusively drives an MREG
	void code_ffM(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::MREG).as_int() == 0 && nusers(n.sigM) == 2) {
			n.argD = n.sigM;
			out_dffe(n);
			if (unwinding())
				return;
			if (dff) {
				n.ffM = dff;
				n.clock = dffclock;
				n.sigM = dffQ;
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
		if (port(m.dsp, ID::OPMODE, SigSpec(0, 7)).extract(4,3).is_fully_zero()) {
			MatchFrame frame(ctx);
			for (auto &[postAdd, AB] : postAdd_index.find(m.sigP[0])) {
				if (blacklisted(postAdd))
					continue;
				if (GetSize(port(postAdd, AB)) < GetSize(m.sigP))
					continue;
				if (port(postAdd, AB).extract(0, GetSize(m.sigP)) != m.sigP)
					continue;
				// Check that remainder of AB is a sign- or zero-extension
				if (!(port(postAdd, AB).extract_end(GetSize(m.sigP)) == SigSpec(m.sigP[GetSize(m.sigP)-1], GetSize(port(postAdd, AB))-GetSize(m.sigP)) || port(postAdd, AB).extract_end(GetSize(m.sigP)) == SigSpec(State::S0, GetSize(port(postAdd, AB))-GetSize(m.sigP))))
					continue;
				Match n = m;
				n.postAdd = postAdd;
				n.postAddAB = AB;
				frame.enter(postAdd);
				code_postAdd(n);
				if (frame.leave())
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
				n.argD = n.sigP;
				out_dffe(n);
				if (unwinding())
					return;
				if (dff) {
					n.ffP = dff;
					n.clock = dffclock;
					n.sigP = dffQ;
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
			for (auto &[postAddMux, AB] : postAddMux_index.find({m.sigP, m.sigC})) {
				if (blacklisted(postAddMux))
					continue;
				Match n = m;
				n.postAddMux = postAddMux;
				n.postAddMuxAB = AB;
				frame.enter(postAddMux);
				code_postAddMux(n);
				if (frame.leave())
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
			for (Cell *overflow : overflow_index.find(m.sigP)) {
				if (blacklisted(overflow))
					continue;
				Match n = m;
				n.overflow = overflow;
				frame.enter(overflow);
				accept(n);
				if (frame.leave())
					return;
			}
		}
		Match n = m;
		n.overflow = nullptr;
		accept(n);
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
		for (auto &[ff, offset] : in_ff_index.find(m.argQ[0])) {
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

	// #######################

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
	void out_dffe(const Match &m)
	{
		dff = nullptr;
		for (auto c : m.argD.chunks())
			// Abandon matches when 'D' has the keep attribute set
			if (c.wire->get_bool_attribute(ID::keep))
				return;
		out_dffe_match_ff(m);
	}

	void out_dffe_match_ff(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[ff, offset] : out_ff_index.find(m.argD[0])) {
			if (blacklisted(ff))
				continue;
			// Check that the rest of argD is present
			if (GetSize(port(ff, ID::D)) < offset + GetSize(m.argD))
				continue;
			if (port(ff, ID::D).extract(offset, GetSize(m.argD)) != m.argD)
				continue;
			if (!(m.clock == SigBit() || port(ff, ID::CLK)[0] == m.clock))
				continue;
			Match n = m;
			n.ff = ff;
			frame.enter(ff);
			out_dffe_code_found(n);
			if (frame.leave())
				return;
		}
	}

	void out_dffe_code_found(const Match &m)
	{
		SigSpec D = port(m.ff, ID::D);
		SigSpec Q = port(m.ff, ID::Q);
		SigSpec argQ = m.argD;
		argQ.replace(D, Q);

		// Abandon matches when 'Q' has a non-zero init attribute set
		// (not supported by DSP48E1)
		for (auto c : argQ.chunks()) {
			Const init = c.wire->attributes.at(ID::init, Const());
			if (!init.empty())
				for (auto b : init.extract(c.offset, c.width))
					if (b != State::Sx && b != State::S0)
						return;
		}

		dff = m.ff;
		dffQ = argQ;
		dffclock = port(m.ff, ID::CLK);
	}
};

YOSYS_NAMESPACE_END

#endif
