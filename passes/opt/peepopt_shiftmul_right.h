#ifndef PEEPOPT_SHIFTMUL_RIGHT_H
#define PEEPOPT_SHIFTMUL_RIGHT_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

//
// Optimize mul+shift pairs that result from expressions such as foo[s*W+:W]
//

struct PeepoptShiftmulRightMatch
{
	Cell *shift = nullptr;
	// the right shift amount
	SigSpec shift_amount = {};
	// log2 scale factor in interpreting of shift_amount
	// due to zero padding on the shift cell's B port
	int log2scale = {};
	SigSpec mul_din = {};
	Const mul_const = {};
	Cell *mul = nullptr;
};

struct PeepoptShiftmulRight : MatchPattern<PeepoptShiftmulRight, PeepoptShiftmulRightMatch>
{
	struct MulChoice {
		Cell *cell = nullptr;
		IdString constport = {};
		IdString varport = {};
	};

	bool did_something = {};

	vector<Cell*> shift_cells = {};
	MatchIndex<SigSpec, MulChoice> mul_index = {};

	PeepoptShiftmulRight(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &PeepoptShiftmulRight::match_shift)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($shift), ID($shiftx), ID($shr)))
				shift_cells.push_back(cell);
			if (cell->type.in(ID($mul))) {
				for (IdString constport : {ID::A, ID::B}) {
					IdString varport = (constport == ID::A ? ID::B : ID::A);
					mul_index.add(port(cell, ID::Y), {cell, constport, varport});
				}
			}
		}
	}

	void match_shift(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *shift : candidates(shift_cells)) {
			if (port(shift, ID::B).empty())
				continue;
			Match n = m;
			n.shift = shift;
			if (descend(frame, shift, &PeepoptShiftmulRight::code_shift_amount, n))
				return;
		}
	}

	void code_shift_amount(const Match &m)
	{
		Match n = m;
		n.shift_amount = port(n.shift, ID::B);
		if (n.shift->type.in(ID($shr)) || !param(n.shift, ID::B_SIGNED).as_bool())
			n.shift_amount.append(State::S0);

		// at this point shift_amount is signed, make
		// sure we can never go negative
		if (n.shift_amount.bits().back() != State::S0)
			return;

		while (n.shift_amount.bits().back() == State::S0) {
			n.shift_amount.remove(GetSize(n.shift_amount) - 1);
			if (n.shift_amount.empty()) return;
		}

		n.log2scale = 0;
		while (n.shift_amount[0] == State::S0) {
			n.shift_amount.remove(0);
			if (n.shift_amount.empty()) return;
			n.log2scale++;
		}

		if (GetSize(n.shift_amount) > 20)
			return;

		match_mul(n);
	}

	void match_mul(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[mul, constport, varport] : candidates(mul_index.find(m.shift_amount))) {
			if (param(mul, ID::A_SIGNED).as_bool())
				continue;
			if (!port(mul, constport).is_fully_const())
				continue;
			Match n = m;
			n.mul = mul;
			n.mul_const = SigSpec({port(mul, constport), SigSpec(State::S0, n.log2scale)}).as_const();
			// get mul_din unmapped (so no `port()` shorthand)
			// because we will be using it to set the \A port
			// on the shift cell, and we want to stay close
			// to the original design
			n.mul_din = mul->getPort(varport);
			if (descend(frame, mul, &PeepoptShiftmulRight::code_rewrite, n))
				return;
		}
	}

	void code_rewrite(const Match &m)
	{
		if (m.mul_const.empty() || GetSize(m.mul_const) > 20)
			return;

		// make sure there's no overlap in the signal
		// selections by the shiftmul pattern
		if (GetSize(port(m.shift, ID::Y)) > m.mul_const.as_int())
			return;

		int factor_bits = ceil_log2(m.mul_const.as_int());
		// make sure the multiplication never wraps around
		if (GetSize(m.shift_amount) + m.log2scale < factor_bits + GetSize(m.mul_din))
			return;

		did_something = true;
		log("right shiftmul pattern in %s: shift=%s, mul=%s\n", module, m.shift, m.mul);

		int const_factor = m.mul_const.as_int();
		int new_const_factor = 1 << factor_bits;
		SigSpec padding(State::Sx, new_const_factor-const_factor);
		SigSpec old_a = port(m.shift, ID::A), new_a = {};

		for (int i = 0; i*const_factor < GetSize(old_a); i++) {
			if ((i+1)*const_factor < GetSize(old_a)) {
				SigSpec slice = old_a.extract(i*const_factor, const_factor);
				new_a.append(slice);
				new_a.append(padding);
			} else {
				new_a.append(old_a.extract_end(i*const_factor));
			}
		}

		SigSpec new_b = {m.mul_din, SigSpec(State::S0, factor_bits)};
		if (param(m.shift, ID::B_SIGNED).as_bool())
			new_b.append(State::S0);

		m.shift->setPort(ID::A, new_a);
		m.shift->setParam(ID::A_WIDTH, GetSize(new_a));
		m.shift->setPort(ID::B, new_b);
		m.shift->setParam(ID::B_WIDTH, GetSize(new_b));

		blacklist(m.shift);
		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
