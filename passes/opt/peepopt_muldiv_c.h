//
// Authored by Akash Levy and Alain Dargelas of Silimate, Inc. under ISC license.
// Transforms mul->div into const->mul when b and c are divisible constants:
// y = (a * b_const) / c_const   ===>   a * eval(b_const / c_const)
//

#ifndef PEEPOPT_MULDIV_C_H
#define PEEPOPT_MULDIV_C_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

struct PeepoptMuldivCMatch
{
	SigSpec a = {};
	SigSpec b_const = {};
	SigSpec mul_y = {};
	Cell *mul = nullptr;
	Cell *div = nullptr;
};

struct PeepoptMuldivC : MatchPattern<PeepoptMuldivC, PeepoptMuldivCMatch>
{
	bool did_something = {};

	vector<Cell*> mul_cells = {};
	MatchIndex<SigSpec> div_index = {};

	PeepoptMuldivC(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &PeepoptMuldivC::match_mul)
	{
		for (auto cell : cells) {
			// Select multiplier
			if (cell->type == ID($mul))
				mul_cells.push_back(cell);
			// Select div of form (a * b_const) / c_const
			if (cell->type == ID($div))
				div_index.add(remove_bottom_padding(port(cell, ID::A)), cell);
		}
	}

	// Helper function, removes LSB 0s
	static SigSpec remove_bottom_padding(SigSpec sig)
	{
		int i = 0;
		for (; i < sig.size() - 1 && sig[i] == State::S0; i++);
		return sig.extract(i, sig.size() - i);
	}

	// Helper functions for two's complement math
	static int sign2sComplement(int value, int numBits)
	{
		if (value & (1 << (numBits - 1))) {
			return -1;
		} else {
			return 1;
		}
	}

	static int twosComplement(int value, int numBits)
	{
		if (value & (1 << (numBits - 1))) {
			return (~value) + 1; // invert bits before adding 1
		} else {
			return value;
		}
	}

	void match_mul(const Match &m)
	{
		match_each(m, mul_cells, &Match::mul, &PeepoptMuldivC::code_operands);
	}

	void code_operands(const Match &m)
	{
		Match n = m;
		// Get multiplier signals
		n.a = port(n.mul, ID::A);
		n.b_const = port(n.mul, ID::B);
		n.mul_y = port(n.mul, ID::Y);

		// Fanout of each multiplier Y bit should be 1 (no bit-split)
		if (nusers(n.mul_y) != 2)
			return;

		// A and B can be interchanged
		match_div(n);
		if (unwinding())
			return;
		std::swap(n.a, n.b_const);
		match_div(n);
	}

	void match_div(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *div : candidates(div_index.find(m.mul_y))) {
			// Check that b_const and c_const is constant
			if (!m.b_const.is_fully_const())
				continue;
			if (!port(div, ID::B).is_fully_const())
				continue;
			if (param(div, ID::A_SIGNED).as_bool() != param(m.mul, ID::A_SIGNED).as_bool())
				continue;
			Match n = m;
			n.div = div;
			if (descend(frame, div, &PeepoptMuldivC::code_rewire, n))
				return;
		}
	}

	void code_rewire(const Match &m)
	{
		// Get div signals
		SigSpec div_a = port(m.div, ID::A);
		SigSpec c_const = port(m.div, ID::B);
		SigSpec div_y = port(m.div, ID::Y);

		// Get offset of multiplier result chunk in divider
		int offset = GetSize(div_a) - GetSize(m.mul_y);

		// Get properties and values of b_const and c_const
		// b_const may be coming from the A port
		// But it is an RTLIL invariant that A_SIGNED equals B_SIGNED
		bool b_const_signed = m.mul->getParam(ID::B_SIGNED).as_bool();
		bool c_const_signed = m.div->getParam(ID::B_SIGNED).as_bool();
		int b_const_int = m.b_const.as_int(b_const_signed);
		int c_const_int = c_const.as_int(c_const_signed);
		int b_const_int_shifted = b_const_int << offset;

		// Two's complement conversion
		if (b_const_signed)
			b_const_int = sign2sComplement(b_const_int, GetSize(m.b_const)) * twosComplement(b_const_int, GetSize(m.b_const));
		if (c_const_signed)
			c_const_int = sign2sComplement(c_const_int, GetSize(c_const)) * twosComplement(c_const_int, GetSize(c_const));
		// Calculate the constant and compress the width to fit the value
		Const const_ratio = {};
		Const b_const_actual = {};
		// Avoid division by zero
		if (c_const_int == 0)
			return;
		b_const_actual = b_const_int_shifted;
		b_const_actual.compress(b_const_signed);

		const_ratio = b_const_int_shifted / c_const_int;
		const_ratio.compress(b_const_signed | c_const_signed);

		// Integer values should be lesser than 32 bits
		// This is because we are using C++ types, and int is 32 bits
		// FIXME: use long long or BigInteger to make pass work with >32 bits
		if (GetSize(m.mul->getParam(ID::B_WIDTH)) > 32)
			return;
		if (GetSize(m.b_const) > 32)
			return;
		if (GetSize(c_const) + offset > 32)
			return;

		// Check for potential multiplier overflow
		if (GetSize(b_const_actual) + GetSize(m.a) > GetSize(m.mul_y))
			return;

		// Check that there are only zeros before offset
		if (offset < 0 || !div_a.extract(0, offset).is_fully_zero())
			return;

		// Check that b is divisible by c
		if (b_const_int_shifted % c_const_int != 0)
			return;

		// Rewire to only keep multiplier
		m.mul->setPort(ID::A, m.a);
		m.mul->setPort(ID::B, const_ratio);
		m.mul->setPort(ID::Y, div_y);

		// Remove divider
		autoremove(m.div);

		// Log, fixup, accept
		log("muldiv_const pattern in %s: mul=%s, div=%s\n", module, m.mul, m.div);
		m.mul->fixup_parameters();
		did_something = true;
		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
