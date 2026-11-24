#ifndef PEEPOPT_MULDIV_H
#define PEEPOPT_MULDIV_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

struct PeepoptMuldivMatch
{
	SigSpec t = {};
	SigSpec x = {};
	SigSpec y = {};
	bool is_signed = {};
	Cell *mul = nullptr;
	Cell *div = nullptr;
};

struct PeepoptMuldiv : MatchPattern<PeepoptMuldiv, PeepoptMuldivMatch>
{
	bool did_something = {};

	vector<Cell*> mul_cells = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>> div_index = {};

	PeepoptMuldiv(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &PeepoptMuldiv::match_mul)
	{
		for (auto cell : cells) {
			if (cell->type == ID($mul) && GetSize(port(cell, ID::A)) + GetSize(port(cell, ID::B)) <= GetSize(port(cell, ID::Y)))
				mul_cells.push_back(cell);
			if (cell->type.in(ID($div)))
				div_index.add({port(cell, ID::A), port(cell, ID::B)}, cell);
		}
	}

	void match_mul(const Match &m)
	{
		match_each(m, mul_cells, &Match::mul, &PeepoptMuldiv::code_operands);
	}

	void code_operands(const Match &m)
	{
		Match n = m;
		n.t = port(n.mul, ID::Y);
		n.x = port(n.mul, ID::A);
		n.y = port(n.mul, ID::B);
		n.is_signed = param(n.mul, ID::A_SIGNED).as_bool();
		match_div(n);
		if (unwinding())
			return;
		std::swap(n.x, n.y);
		match_div(n);
	}

	bool div_signed_like_mul(const Match &m, Cell *div) const
	{
		return param(div, ID::A_SIGNED).as_bool() == m.is_signed;
	}

	void match_div(const Match &m)
	{
		match_each(m, div_index.find({m.t, m.x}), &PeepoptMuldiv::div_signed_like_mul, &Match::div, &PeepoptMuldiv::code_replace);
	}

	void code_replace(const Match &m)
	{
		SigSpec div_y = port(m.div, ID::Y);
		SigSpec val_y = m.y;

		if (GetSize(div_y) != GetSize(val_y))
			val_y.extend_u0(GetSize(div_y), param(m.div, ID::A_SIGNED).as_bool());

		did_something = true;
		log("muldiv pattern in %s: mul=%s, div=%s\n", module, m.mul, m.div);
		module->connect(div_y, val_y);
		autoremove(m.div);
		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
