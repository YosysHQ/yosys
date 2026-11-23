#ifndef XILINX_DSP48A_H
#define XILINX_DSP48A_H

#include "kernel/matcher.h"

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

struct XilinxDsp48aPack : MatchPattern
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
		// Variables used for subpatterns
		SigSpec argQ = {};
		SigSpec argD = {};
		Cell *ff = nullptr;
	};
	using Callback = void (*)(XilinxDsp48aPack &, const Match &);

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
	MatchIndex<SigBit, PortChoice> postAdd_index = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>, PortChoice> postAddMux_index = {};
	MatchIndex<SigBit, FfSlice> in_ff_index = {};
	MatchIndex<SigBit, FfSlice> out_ff_index = {};
	Callback on_accept = nullptr;

	XilinxDsp48aPack(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx)
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
				param(m.dsp, ID::B0REG).as_int() == 0 &&
				// Ensure that preAdder not already used
				port(m.dsp, ID::OPMODE, SigSpec()).extract(4, 1).is_fully_zero();
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

	// (1) Starting from a DSP48A/DSP48A1 cell
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
	//      reset functionality, using a subpattern discussed above)
	//     If matched, treat 'B' input as input of B1REG
	void code_ffB1(const Match &m)
	{
		Match n = m;
		if (param(n.dsp, ID::B1REG).as_int() == 0 && param(n.dsp, ID::B0REG).as_int() == 0 && port(n.dsp, ID::OPMODE, SigSpec()).extract(4, 1).is_fully_zero()) {
			n.argQ = n.sigB;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff) {
				n.ffB1 = dff;
				n.clock = dffclock;
				n.sigB = dffD;
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
			for (Cell *preAdd : preAdd_index.find(m.sigB)) {
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
			n.argQ = n.sigB;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff && (!n.ffB1 || same_ff_controls(dff, n.ffB1))) {
				n.ffB0 = dff;
				n.clock = dffclock;
				n.sigB = dffD;
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
			n.argQ = n.sigA;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff) {
				n.ffA1 = dff;
				n.clock = dffclock;
				n.sigA = dffD;

				// Now attempt to match A0
				n.argQ = n.sigA;
				in_dffe(n);
				if (unwinding())
					return;
				if (dff && same_ff_controls(dff, n.ffA1)) {
					n.ffA0 = dff;
					n.clock = dffclock;
					n.sigA = dffD;
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
		if (port(m.dsp, ID::OPMODE, SigSpec()).extract(2,2).is_fully_zero()) {
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
