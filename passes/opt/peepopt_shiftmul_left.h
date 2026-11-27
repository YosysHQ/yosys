#ifndef PEEPOPT_SHIFTMUL_LEFT_H
#define PEEPOPT_SHIFTMUL_LEFT_H

#include "passes/opt/peepopt_shiftmul.h"

YOSYS_NAMESPACE_BEGIN

//
// Optimize mul+shift pairs that result from expressions such as foo[s*W+:W]
//

struct PeepoptShiftmulLeftMatch
{
	Cell *shift = nullptr;
	Cell *neg = nullptr;
	// the left shift amount
	SigSpec shift_amount = {};
	// log2 scale factor in interpreting of shift_amount
	// due to zero padding on the shift cell's B port
	int log2scale = {};
	SigSpec mul_din = {};
	Const mul_const = {};
	Cell *mul = nullptr;
};

struct PeepoptShiftmulLeft : MatchPattern<PeepoptShiftmulLeft, PeepoptShiftmulLeftMatch>
{
	struct MulChoice {
		Cell *cell = nullptr;
		IdString constport = {};
		IdString varport = {};
	};

	bool did_something = {};

	vector<Cell*> shift_cells = {};
	MatchIndex<SigSpec> neg_index = {};
	MatchIndex<SigSpec, MulChoice> mul_index = {};

	PeepoptShiftmulLeft(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &PeepoptShiftmulLeft::match_shift)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($shift), ID($shiftx), ID($shl)) && (cell->type.in(ID($shl)) || param(cell, ID::B_SIGNED).as_bool()))
				shift_cells.push_back(cell);
			if (cell->type == ID($neg))
				neg_index.add(port(cell, ID::Y), cell);
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
		match_each(m, shift_cells, &PeepoptShiftmulLeft::has_shift_amount, &Match::shift, &PeepoptShiftmulLeft::match_neg);
	}

	void match_neg(const Match &m)
	{
		if (!m.shift->type.in(ID($shift), ID($shiftx))) {
			match_none(m, &Match::neg, &PeepoptShiftmulLeft::code_shift_amount);
			return;
		}
		MatchFrame frame(ctx);
		for (Cell *neg : candidates(neg_index.find(port(m.shift, ID::B)))) {
			if (port(m.shift, ID::A).empty())
				continue;
			Match n = m;
			n.neg = neg;
			if (descend(frame, neg, &PeepoptShiftmulLeft::code_shift_amount, n))
				return;
		}
	}

	void code_shift_amount(const Match &m)
	{
		Match n = m;
		if (n.neg) {
			// case of `$shift`, `$shiftx`
			n.shift_amount = port(n.neg, ID::A);
			if (!param(n.neg, ID::A_SIGNED).as_bool())
				n.shift_amount.append(State::S0);
		} else {
			// case of `$shl`
			n.shift_amount = port(n.shift, ID::B);
			if (!param(n.shift, ID::B_SIGNED).as_bool())
				n.shift_amount.append(State::S0);
		}

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
		if (GetSize(port(m.shift, ID::A)) > m.mul_const.as_int())
			return;

		int factor_bits = ceil_log2(m.mul_const.as_int());
		// make sure the multiplication never wraps around
		if (GetSize(m.shift_amount) < factor_bits + GetSize(m.mul_din))
			return;

		if (m.neg) {
			// make sure the negation never wraps around
			if (GetSize(port(m.shift, ID::B)) < factor_bits + GetSize(m.mul_din)
							+ m.log2scale + 1)
				return;
		}

		did_something = true;
		log("left shiftmul pattern in %s: shift=%s, mul=%s\n", module, m.shift, m.mul);

		int const_factor = m.mul_const.as_int();
		int new_const_factor = 1 << factor_bits;
		SigSpec padding(State::Sm, new_const_factor-const_factor);
		SigSpec old_y = port(m.shift, ID::Y), new_y = {};
		int trunc = 0;

		if (GetSize(old_y) % const_factor != 0) {
			trunc = const_factor - GetSize(old_y) % const_factor;
			old_y.append(SigSpec(State::Sm, trunc));
		}

		for (int i = 0; i*const_factor < GetSize(old_y); i++) {
			SigSpec slice = old_y.extract(i*const_factor, const_factor);
			new_y.append(slice);
			new_y.append(padding);
		}

		if (trunc > 0)
			new_y.remove(GetSize(new_y)-trunc, trunc);

		{
			// Now replace occurences of Sm in new_y with bits
			// of a dummy wire
			int padbits = 0;
			for (auto bit : new_y)
			if (bit == SigBit(State::Sm))
				padbits++;

			SigSpec padwire = module->addWire(NEW_ID, padbits);

			for (int i = new_y.size() - 1; i >= 0; i--)
			if (new_y[i] == SigBit(State::Sm)) {
				new_y[i] = padwire.bits().back();
				padwire.remove(padwire.size() - 1);
			}
		}

		SigSpec new_b = {m.mul_din, SigSpec(State::S0, factor_bits)};

		m.shift->setPort(ID::Y, new_y);
		m.shift->setParam(ID::Y_WIDTH, GetSize(new_y));
		if (m.shift->type == ID($shl)) {
			if (param(m.shift, ID::B_SIGNED).as_bool())
				new_b.append(State::S0);
			m.shift->setPort(ID::B, new_b);
			m.shift->setParam(ID::B_WIDTH, GetSize(new_b));
		} else {
			SigSpec b_neg = module->addWire(NEW_ID, GetSize(new_b) + 1);
			module->addNeg(NEW_ID, new_b, b_neg);
			m.shift->setPort(ID::B, b_neg);
			m.shift->setParam(ID::B_WIDTH, GetSize(b_neg));
		}

		denylist(m.shift);
		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
