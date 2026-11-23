#ifndef ICE40_WRAPCARRY_H
#define ICE40_WRAPCARRY_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

struct Ice40WrapcarryMatch
{
	Cell *carry = nullptr;
	Cell *lut = nullptr;
};

struct Ice40Wrapcarry : MatchPattern<Ice40Wrapcarry, Ice40WrapcarryMatch>
{
	vector<Cell*> carry_cells = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>> lut_index = {};

	Ice40Wrapcarry(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &Ice40Wrapcarry::match_carry)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::SB_CARRY))
				carry_cells.push_back(cell);
			if (cell->type.in(ID::SB_LUT4))
				lut_index.add({port(cell, ID::I1), port(cell, ID::I2)}, cell);
		}
	}

	void match_carry(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *carry : carry_cells) {
			if (blacklisted(carry))
				continue;
			Match n = m;
			n.carry = carry;
			frame.enter(carry);
			match_lut(n);
			if (frame.leave())
				return;
		}
	}

	void match_lut(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *lut : lut_index.find({port(m.carry, ID::I0), port(m.carry, ID::I1)})) {
			if (blacklisted(lut))
				continue;
			Match n = m;
			n.lut = lut;
			frame.enter(lut);
			accept(n);
			if (frame.leave())
				return;
		}
	}
};

YOSYS_NAMESPACE_END

#endif
