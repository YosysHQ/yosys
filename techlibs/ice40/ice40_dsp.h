#ifndef ICE40_DSP_H
#define ICE40_DSP_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

struct Ice40Dsp : MatchPattern
{
	struct Match {
		SigBit clock = {};
		bool clock_pol = {};
		bool cd_signed = {};
		bool o_lo = {};
		SigSpec sigA = {};
		SigSpec sigB = {};
		SigSpec sigCD = {};
		SigSpec sigH = {};
		SigSpec sigO = {};
		Cell *add = nullptr;
		Cell *mux = nullptr;
		IdString addAB = {};
		IdString muxAB = {};
		Cell *ffA = nullptr;
		Cell *ffB = nullptr;
		Cell *ffCD = nullptr;
		Cell *ffFJKG = nullptr;
		Cell *ffH = nullptr;
		Cell *ffO = nullptr;
		Cell *mul = nullptr;
		// subpattern
		bool argSdff = {};
		SigSpec argQ = {};
		SigSpec argD = {};
		Cell *ff = nullptr;
	};
	using Callback = void (*)(Ice40Dsp &, const Match &);

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
	bool dffclock_pol = {};

	vector<Cell*> mul_cells = {};
	MatchIndex<SigBit, PortChoice> add_index = {};
	MatchIndex<SigSpec, PortChoice> mux_index = {};
	MatchIndex<SigBit, FfSlice> in_ff_index = {};
	MatchIndex<SigBit, FfSlice> out_ff_index = {};
	Callback on_accept = nullptr;

	Ice40Dsp(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($mul), ID::SB_MAC16) && GetSize(cell->getPort(ID::A)) + GetSize(cell->getPort(ID::B)) > 10)
				mul_cells.push_back(cell);
			if (cell->type.in(ID($add)))
				for (IdString AB : {ID::A, ID::B})
					if (nusers(port(cell, AB)) == 2)
						add_index.add(port(cell, AB)[0], {cell, AB});
			if (cell->type == ID($mux))
				for (IdString AB : {ID::A, ID::B})
					if (nusers(port(cell, AB)) == 2)
						mux_index.add(port(cell, AB), {cell, AB});
			// DSP48E1 does not support clock inversion
			if (cell->type.in(ID($dff), ID($dffe)) && param(cell, ID::CLK_POLARITY).as_bool())
				for (int offset = 0; offset < GetSize(port(cell, ID::D)); offset++)
					in_ff_index.add(port(cell, ID::Q)[offset], {cell, offset});
			// SB_MAC16 does not support clock inversion
			if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffce)) && param(cell, ID::CLK_POLARITY).as_bool())
				for (int offset = 0; offset < GetSize(port(cell, ID::D)); offset++)
					out_ff_index.add(port(cell, ID::D)[offset], {cell, offset});
		}
	}

	int run(Callback callback = nullptr)
	{
		on_accept = callback;
		begin_run();
		match_mul(Match{});
		return end_run();
	}

	bool accept(const Match &m)
	{
		accept_cnt++;
		if (on_accept)
			on_accept(*this, m);
		return unwinding();
	}

	static SigSpec unextend_signed(const SigSpec &sig)
	{
		int i = {};
		for (i = GetSize(sig)-1; i > 0; i--)
			if (sig[i] != sig[i-1])
				break;
		// Do not remove sign bit
		++i;
		return sig.extract(0, i);
	}

	static SigSpec unextend_unsigned(const SigSpec &sig)
	{
		int i = {};
		for (i = GetSize(sig)-1; i > 0; i--)
			if (sig[i] != SigBit(State::S0))
				break;
		++i;
		return sig.extract(0, i);
	}

	bool same_arst(Cell *input_ff, Cell *ff) const
	{
		if (input_ff->hasPort(ID::ARST) != ff->hasPort(ID::ARST))
			return false;
		if (input_ff->hasPort(ID::ARST)) {
			if (port(input_ff, ID::ARST) != port(ff, ID::ARST))
				return false;
			if (param(input_ff, ID::ARST_POLARITY) != param(ff, ID::ARST_POLARITY))
				return false;
		}
		return true;
	}

	bool same_arst_as_inputs(const Match &m, Cell *ff) const
	{
		if (m.ffA && !same_arst(m.ffA, ff))
			return false;
		if (m.ffB && !same_arst(m.ffB, ff))
			return false;
		return true;
	}

	bool ffFJKG_compatible(const Match &m, Cell *ff) const
	{
		// F/J/K/G do not have a CE-like (hold) input
		if (ff->hasPort(ID::EN))
			return false;

		// Reset signal of F/J (IRSTTOP) and K/G (IRSTBOT)
		//   shared with A and B
		return same_arst_as_inputs(m, ff);
	}

	bool ffH_compatible(const Match &m, Cell *ff) const
	{
		// H does not have a CE-like (hold) input
		if (ff->hasPort(ID::EN))
			return false;

		// Reset signal of H (IRSTBOT) shared with B
		return same_arst(m.ffB, ff);
	}

	bool ffCD_compatible(const Match &m, Cell *ff) const
	{
		// Reset signal of C (IRSTTOP) and D (IRSTBOT)
		//   shared with A and B
		return same_arst_as_inputs(m, ff);
	}

	void match_mul(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *mul : mul_cells) {
			if (blacklisted(mul))
				continue;
			Match n = m;
			n.mul = mul;
			frame.enter(mul);
			code_signals(n);
			if (frame.leave())
				return;
		}
	}

	void code_signals(const Match &m)
	{
		Match n = m;
		n.sigA = param(n.mul, ID::A_SIGNED).as_bool() ? unextend_signed(port(n.mul, ID::A)) : unextend_unsigned(port(n.mul, ID::A));
		n.sigB = param(n.mul, ID::B_SIGNED).as_bool() ? unextend_signed(port(n.mul, ID::B)) : unextend_unsigned(port(n.mul, ID::B));

		SigSpec O = {};
		if (n.mul->type == ID($mul))
			O = n.mul->getPort(ID::Y);
		else if (n.mul->type == ID::SB_MAC16)
			O = n.mul->getPort(ID::O);
		else log_abort();
		if (GetSize(O) <= 10)
			return;

		// Only care about those bits that are used
		int i = {};
		for (i = GetSize(O) - 1; i > 0 && nusers(O[i]) <= 1; i--)
			;
		// This sigM could have no users if downstream sinks (e.g. $add) is
		//   narrower than $mul result, for example
		if (i == 0)
			return;

		for (int j = 0, wire_width = 0; j <= i; j++)
			if (nusers(O[j]) == 0)
				wire_width++;
			else {
				if (wire_width) { // add empty wires for bit offset if needed
					n.sigH.append(module->addWire(NEW_ID, wire_width));
					wire_width = 0;
				}
				n.sigH.append(O[j]);
			}

		code_ffA(n);
	}

	void code_ffA(const Match &m)
	{
		Match n = m;
		if (n.mul->type != ID::SB_MAC16 || !param(n.mul, ID::A_REG).as_bool()) {
			n.argQ = n.sigA;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff) {
				n.ffA = dff;
				n.clock = dffclock;
				n.clock_pol = dffclock_pol;
				n.sigA = dffD;
			}
		}
		code_ffB(n);
	}

	void code_ffB(const Match &m)
	{
		Match n = m;
		if (n.mul->type != ID::SB_MAC16 || !param(n.mul, ID::B_REG).as_bool()) {
			n.argQ = n.sigB;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff) {
				n.ffB = dff;
				n.clock = dffclock;
				n.clock_pol = dffclock_pol;
				n.sigB = dffD;
			}
		}
		code_ffFJKG(n);
	}

	void code_ffFJKG(const Match &m)
	{
		Match n = m;
		if (nusers(n.sigH) == 2 &&
				(n.mul->type != ID::SB_MAC16 ||
				 (!param(n.mul, ID::TOP_8x8_MULT_REG).as_bool() && !param(n.mul, ID::BOT_8x8_MULT_REG).as_bool() && !param(n.mul, ID::PIPELINE_16x16_MULT_REG1).as_bool() && !param(n.mul, ID::PIPELINE_16x16_MULT_REG1).as_bool()))) {
			n.argD = n.sigH;
			n.argSdff = false;
			out_dffe(n);
			if (unwinding())
				return;
			if (dff && ffFJKG_compatible(n, dff)) {
				n.ffFJKG = dff;
				n.clock = dffclock;
				n.clock_pol = dffclock_pol;
				n.sigH = dffQ;
			}
		}
		code_ffH(n);
	}

	void code_ffH(const Match &m)
	{
		Match n = m;
		if (n.ffFJKG && nusers(n.sigH) == 2 &&
				(n.mul->type != ID::SB_MAC16 || !param(n.mul, ID::PIPELINE_16x16_MULT_REG2).as_bool())) {
			n.argD = n.sigH;
			n.argSdff = false;
			out_dffe(n);
			if (unwinding())
				return;
			if (dff && ffH_compatible(n, dff)) {
				n.ffH = dff;
				n.clock = dffclock;
				n.clock_pol = dffclock_pol;
				n.sigH = dffQ;
			}
		}

		n.sigO = n.sigH;
		match_add(n);
	}

	void match_add(const Match &m)
	{
		if (m.mul->type != ID::SB_MAC16 || (param(m.mul, ID::TOPOUTPUT_SELECT).as_int() == 3 && param(m.mul, ID::BOTOUTPUT_SELECT).as_int() == 3)) {
			MatchFrame frame(ctx);
			for (auto &[add, AB] : add_index.find(m.sigH[0])) {
				if (blacklisted(add))
					continue;
				if (!(GetSize(port(add, AB)) <= GetSize(m.sigH)))
					continue;
				if (!(port(add, AB) == m.sigH.extract(0, GetSize(port(add, AB)))))
					continue;
				if (!(nusers(m.sigH.extract_end(GetSize(port(add, AB)))) <= 1))
					continue;
				Match n = m;
				n.add = add;
				n.addAB = AB;
				frame.enter(add);
				code_add(n);
				if (frame.leave())
					return;
			}
		}

		Match n = m;
		n.add = nullptr;
		code_add(n);
	}

	void code_add(const Match &m)
	{
		Match n = m;
		if (n.add) {
			n.sigCD = port(n.add, n.addAB == ID::A ? ID::B : ID::A);
			n.cd_signed = param(n.add, n.addAB == ID::A ? ID::B_SIGNED : ID::A_SIGNED).as_bool();

			int natural_mul_width = GetSize(n.sigA) + GetSize(n.sigB);
			int actual_mul_width = GetSize(n.sigH);
			int actual_acc_width = GetSize(n.sigCD);

			if ((actual_acc_width > actual_mul_width) && (natural_mul_width > actual_mul_width))
				return;
			// If accumulator, check adder width and signedness
			if (n.sigCD == n.sigH && (actual_acc_width != actual_mul_width) && (param(n.mul, ID::A_SIGNED).as_bool() != param(n.add, ID::A_SIGNED).as_bool()))
				return;

			n.sigO = port(n.add, ID::Y);
		}
		match_mux(n);
	}

	void match_mux(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[mux, AB] : mux_index.find(m.sigO)) {
			if (blacklisted(mux))
				continue;
			Match n = m;
			n.mux = mux;
			n.muxAB = AB;
			frame.enter(mux);
			code_mux(n);
			if (frame.leave())
				return;
		}

		Match n = m;
		n.mux = nullptr;
		code_mux(n);
	}

	void code_mux(const Match &m)
	{
		Match n = m;
		if (n.mux)
			n.sigO = port(n.mux, ID::Y);
		code_ffO(n);
	}

	void code_ffO(const Match &m)
	{
		Match n = m;
		if (n.mul->type != ID::SB_MAC16 ||
				// Ensure that register is not already used
				((param(n.mul, ID::TOPOUTPUT_SELECT).as_int() != 1 && param(n.mul, ID::BOTOUTPUT_SELECT).as_int() != 1) &&
				 // Ensure that OLOADTOP/OLOADBOT is unused or zero
				 (port(n.mul, ID::OLOADTOP, State::S0).is_fully_zero() && port(n.mul, ID::OLOADBOT, State::S0).is_fully_zero()))) {

			dff = nullptr;

			// First try entire sigO
			if (nusers(n.sigO) == 2) {
				n.argD = n.sigO;
				n.argSdff = !n.mux;
				out_dffe(n);
				if (unwinding())
					return;
			}

			// Otherwise try just its least significant 16 bits
			if (!dff && GetSize(n.sigO) > 16) {
				n.argD = n.sigO.extract(0, 16);
				if (nusers(n.argD) == 2) {
					n.argSdff = !n.mux;
					out_dffe(n);
					if (unwinding())
						return;
					n.o_lo = dff;
				}
			}

			if (dff) {
				n.ffO = dff;
				n.clock = dffclock;
				n.clock_pol = dffclock_pol;

				n.sigO.replace(n.sigO.extract(0, GetSize(dffQ)), dffQ);
			}

			// Loading value into output register is not
			//   supported unless using accumulator
			if (n.mux) {
				if (n.sigCD != n.sigO)
					return;
				n.sigCD = port(n.mux, n.muxAB == ID::B ? ID::A : ID::B);

				n.cd_signed = n.add && param(n.add, ID::A_SIGNED).as_bool() && param(n.add, ID::B_SIGNED).as_bool();
			} else if (dff && dff->hasPort(ID::SRST)) {
				if (n.sigCD != n.sigO)
					return;
				n.sigCD = param(dff, ID::SRST_VALUE);

				n.cd_signed = n.add && param(n.add, ID::A_SIGNED).as_bool() && param(n.add, ID::B_SIGNED).as_bool();
			}
		}
		code_ffCD(n);
	}

	void code_ffCD(const Match &m)
	{
		Match n = m;
		if (!n.sigCD.empty() && n.sigCD != n.sigO &&
				(n.mul->type != ID::SB_MAC16 || (!param(n.mul, ID::C_REG).as_bool() && !param(n.mul, ID::D_REG).as_bool()))) {
			n.argQ = n.sigCD;
			in_dffe(n);
			if (unwinding())
				return;
			if (dff && ffCD_compatible(n, dff)) {
				n.ffCD = dff;
				n.clock = dffclock;
				n.clock_pol = dffclock_pol;
				n.sigCD = dffD;
			}
		}
		code_extend_sigCD(n);
	}

	void code_extend_sigCD(const Match &m)
	{
		Match n = m;
		n.sigCD.extend_u0(32, n.cd_signed);
		accept(n);
	}

	// #######################

	void in_dffe(const Match &m)
	{
		dff = nullptr;
		if (m.argQ.empty())
			return;
		for (auto c : m.argQ.chunks()) {
			if (!c.wire)
				return;
			if (c.wire->get_bool_attribute(ID::keep))
				return;
			Const init = c.wire->attributes.at(ID::init, State::Sx);
			if (!init.is_fully_undef() && !init.is_fully_zero())
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
			// Check that the rest of argQ is present
			if (!(GetSize(port(ff, ID::Q)) >= offset + GetSize(m.argQ)))
				continue;
			if (!(port(ff, ID::Q).extract(offset, GetSize(m.argQ)) == m.argQ))
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
		if (m.clock != SigBit()) {
			if (port(m.ff, ID::CLK)[0] != m.clock)
				return;
			if (param(m.ff, ID::CLK_POLARITY).as_bool() != m.clock_pol)
				return;
		}

		SigSpec Q = port(m.ff, ID::Q);
		dff = m.ff;
		dffclock = port(m.ff, ID::CLK);
		dffclock_pol = param(m.ff, ID::CLK_POLARITY).as_bool();
		dffD = m.argQ;
		SigSpec argD = port(m.ff, ID::D);
		dffD.replace(Q, argD);
	}

	// #######################

	void out_dffe(const Match &m)
	{
		dff = nullptr;
		for (auto c : m.argD.chunks())
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
			// Only allow sync reset if requested.
			if (!(m.argSdff || ff->type.in(ID($dff), ID($dffe))))
				continue;
			// Check that the rest of argD is present
			if (!(GetSize(port(ff, ID::D)) >= offset + GetSize(m.argD)))
				continue;
			if (!(port(ff, ID::D).extract(offset, GetSize(m.argD)) == m.argD))
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
		if (m.clock != SigBit()) {
			if (port(m.ff, ID::CLK)[0] != m.clock)
				return;
			if (param(m.ff, ID::CLK_POLARITY).as_bool() != m.clock_pol)
				return;
		}
		SigSpec D = port(m.ff, ID::D);
		SigSpec Q = port(m.ff, ID::Q);
		SigSpec argQ = m.argD;
		argQ.replace(D, Q);

		for (auto c : argQ.chunks()) {
			Const init = c.wire->attributes.at(ID::init, State::Sx);
			if (!init.is_fully_undef() && !init.is_fully_zero())
				return;
		}

		dff = m.ff;
		dffQ = argQ;
		dffclock = port(m.ff, ID::CLK);
		dffclock_pol = param(m.ff, ID::CLK_POLARITY).as_bool();
	}
};

YOSYS_NAMESPACE_END

#endif
