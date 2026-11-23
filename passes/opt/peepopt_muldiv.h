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
		MatchFrame frame(ctx);
		for (Cell *mul : mul_cells) {
			if (blacklisted(mul))
				continue;
			Match n = m;
			n.mul = mul;
			frame.enter(mul);
			code_operands(n);
			if (frame.leave())
				return;
		}
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

	void match_div(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *div : div_index.find({m.t, m.x})) {
			if (blacklisted(div))
				continue;
			if (param(div, ID::A_SIGNED).as_bool() != m.is_signed)
				continue;
			Match n = m;
			n.div = div;
			frame.enter(div);
			code_replace(n);
			if (frame.leave())
				return;
		}
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
