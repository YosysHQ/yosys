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
		match_each(m, carry_cells, &Match::carry, &Ice40Wrapcarry::match_lut);
	}

	void match_lut(const Match &m)
	{
		match_each(m, lut_index.find({port(m.carry, ID::I0), port(m.carry, ID::I1)}), &Match::lut, &Ice40Wrapcarry::accept);
	}
};

YOSYS_NAMESPACE_END

#endif
