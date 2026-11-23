#ifndef PEEPOPT_SHIFTMUL_LEFT_H
#define PEEPOPT_SHIFTMUL_LEFT_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

//
// Optimize mul+shift pairs that result from expressions such as foo[s*W+:W]
//

struct PeepoptShiftmulLeft : MatchPattern
{
	struct Match {
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
	using Callback = void (*)(PeepoptShiftmulLeft &, const Match &);

	struct MulChoice {
		Cell *cell = nullptr;
		IdString constport = {};
		IdString varport = {};
	};

	bool did_something = {};

	vector<Cell*> shift_cells = {};
	MatchIndex<SigSpec> neg_index = {};
	MatchIndex<SigSpec, MulChoice> mul_index = {};
	Callback on_accept = nullptr;

	PeepoptShiftmulLeft(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx)
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

	int run(Callback callback = nullptr)
	{
		on_accept = callback;
		begin_run();
		match_shift(Match{});
		return end_run();
	}

	bool accept(const Match &m)
	{
		accept_cnt++;
		if (on_accept)
			on_accept(*this, m);
		return unwinding();
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
			match_neg(n);
			if (frame.leave())
				return;
		}
	}

	void match_neg(const Match &m)
	{
		if (!m.shift->type.in(ID($shift), ID($shiftx))) {
			Match n = m;
			n.neg = nullptr;
			code_shift_amount(n);
			return;
		}
		MatchFrame frame(ctx);
		for (Cell *neg : neg_index.find(port(m.shift, ID::B))) {
			if (blacklisted(neg))
				continue;
			if (port(m.shift, ID::A).empty())
				continue;
			Match n = m;
			n.neg = neg;
			frame.enter(neg);
			code_shift_amount(n);
			if (frame.leave())
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
		for (auto &[mul, constport, varport] : mul_index.find(m.shift_amount)) {
			if (blacklisted(mul))
				continue;
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
			frame.enter(mul);
			code_rewrite(n);
			if (frame.leave())
				return;
		}
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

		blacklist(m.shift);
		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
