#ifndef ICE40_WRAPCARRY_H
#define ICE40_WRAPCARRY_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

struct Ice40Wrapcarry : MatchPattern
{
	struct Match {
		Cell *carry = nullptr;
		Cell *lut = nullptr;
	};
	using Callback = void (*)(Ice40Wrapcarry &, const Match &);

	vector<Cell*> carry_cells = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>> lut_index = {};
	Callback on_accept = nullptr;

	Ice40Wrapcarry(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID::SB_CARRY))
				carry_cells.push_back(cell);
			if (cell->type.in(ID::SB_LUT4))
				lut_index.add({port(cell, ID::I1), port(cell, ID::I2)}, cell);
		}
	}

	int run(Callback callback = nullptr)
	{
		on_accept = callback;
		begin_run();
		match_carry(Match{});
		return end_run();
	}

	bool accept(const Match &m)
	{
		accept_cnt++;
		if (on_accept)
			on_accept(*this, m);
		return unwinding();
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
