#ifndef PEEPOPT_SHIFTMUL_RIGHT_H
#define PEEPOPT_SHIFTMUL_RIGHT_H

#include "passes/opt/peepopt_shiftmul.h"

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

	bool has_shift_amount(const Match &, Cell *shift) const
	{
		return !port(shift, ID::B).empty();
	}

	void match_shift(const Match &m)
	{
		match_each(m, shift_cells, &PeepoptShiftmulRight::has_shift_amount, &Match::shift, &PeepoptShiftmulRight::code_shift_amount);
	}

	void code_shift_amount(const Match &m)
	{
		Match n = m;
		n.shift_amount = port(n.shift, ID::B);
		if (n.shift->type.in(ID($shr)) || !param(n.shift, ID::B_SIGNED).as_bool())
			n.shift_amount.append(State::S0);

		if (!peepopt_shiftmul_normalize(n.shift_amount, n.log2scale))
			return;

		match_mul(n);
	}

	void match_mul(const Match &m)
	{
		peepopt_shiftmul_match_mul(*this, m);
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

		denylist(m.shift);
		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
