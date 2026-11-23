#ifndef PEEPOPT_SHIFTPOW2_H
#define PEEPOPT_SHIFTPOW2_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

//
// Optimize shifts that result from expressions such as foo[s*W+:W]
// when W is a power of two and the multiply has been folded away.
//

struct PeepoptShiftpow2Match
{
	Cell *shift = nullptr;
};

struct PeepoptShiftpow2 : MatchPattern<PeepoptShiftpow2, PeepoptShiftpow2Match>
{
	bool did_something = {};

	vector<Cell*> shift_cells = {};

	PeepoptShiftpow2(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &PeepoptShiftpow2::match_shift)
	{
		for (auto cell : cells)
			if (cell->type.in(ID($shift), ID($shiftx), ID($shr)))
				shift_cells.push_back(cell);
	}

	void match_shift(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *shift : shift_cells) {
			if (blacklisted(shift))
				continue;
			if (port(shift, ID::B).empty())
				continue;
			Match n = m;
			n.shift = shift;
			frame.enter(shift);
			code_rewrite(n);
			if (frame.leave())
				return;
		}
	}

	void code_rewrite(const Match &m)
	{
		// make sure the shift amount cannot be negative
		SigSpec amount = port(m.shift, ID::B);
		bool b_signed = m.shift->type.in(ID($shift), ID($shiftx)) && param(m.shift, ID::B_SIGNED).as_bool();
		if (!b_signed)
			amount.append(State::S0);
		if (amount.bits().back() != State::S0)
			return;

		while (GetSize(amount) > 1 && amount.bits().back() == State::S0)
			amount.remove(GetSize(amount) - 1);

		// low zero bits encode the power-of-two scale
		int log2scale = 0;
		while (!amount.empty() && amount[0] == State::S0) {
			amount.remove(0);
			log2scale++;
		}

		if (log2scale < 1)
			return;

		if (amount.empty() || amount.is_fully_const())
			return;

		SigSpec sel = amount;
		int sel_width = GetSize(sel);
		int width = param(m.shift, ID::Y_WIDTH).as_int();
		if (log2scale >= 8 * (int)sizeof(int) - 1)
			return;
		int stride = 1 << log2scale;

		// avoid overlapping selections
		if (width > stride)
			return;

		if (sel_width > 20)
			return;
		long long ways = 1LL << sel_width;

		SigSpec A = port(m.shift, ID::A);
		int a_width = GetSize(A);
		bool a_signed = !m.shift->type.in(ID($shiftx)) && param(m.shift, ID::A_SIGNED).as_bool();
		int extended_a_width = a_signed ? std::max(a_width, width) : a_width;

		// limit padding for out-of-range select values
		int max_ratio = module->design->scratchpad_get_int("peepopt.shiftpow2.max_data_multiple", 2);
		if (ways * (long long)width > (long long)max_ratio * std::max(a_width, width))
			return;

		did_something = true;
		log("shiftpow2 pattern in %s: shift=%s, index=%s, stride=%d, width=%d, ways=%lld\n",
				module, m.shift, log_signal(sel), stride, width, ways);

		// way i holds A[i*stride +: width], way 0 in the LSBs
		State fill = m.shift->type.in(ID($shiftx)) ? State::Sx : State::S0;
		SigSpec bmux_a = {};
		for (long long i = 0; i < ways; i++) {
			long long base = i * (long long)stride;
			for (int b = 0; b < width; b++) {
				long long idx = base + b;
				if (idx < a_width)
					bmux_a.append(A[idx]);
				else if (idx < extended_a_width)
					bmux_a.append(A.back());
				else
					bmux_a.append(fill);
			}
		}

		module->addBmux(NEW_ID, bmux_a, sel, port(m.shift, ID::Y));
		autoremove(m.shift);
		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
