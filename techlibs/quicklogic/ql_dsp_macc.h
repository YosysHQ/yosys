#ifndef QL_DSP_MACC_H
#define QL_DSP_MACC_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

// Rough sketch: (mux is optional)
//
//               /-----------------------\
//               |                       |
//              \ /                      |
//   mul ----> add -----> mux -----> ff -+---->
//         |              /\
//         |              |
//          --------------

struct QlDspMaccMatch
{
	Cell *mul = nullptr;
	Cell *add = nullptr;
	Cell *mux = nullptr;
	Cell *ff = nullptr;
	IdString add_ba = {};
	IdString mux_ab = {};
	// Is the output taken from before or after the FF?
	bool output_registered = {};
	// Is there a mux in the pattern?
	bool mux_in_pattern = {};
};

struct QlDspMacc : MatchPattern<QlDspMacc, QlDspMaccMatch>
{
	struct AddChoice {
		Cell *cell = nullptr;
		IdString BA = {};
	};

	struct MuxChoice {
		Cell *cell = nullptr;
		IdString AB = {};
	};

	vector<Cell*> mul_cells = {};
	MatchIndex<SigSpec, AddChoice> add_index = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>, MuxChoice> mux_index = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>> ff_index = {};

	QlDspMacc(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &QlDspMacc::code_mux_in_pattern)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($mul)) && nusers(port(cell, ID::Y)) <= 3)
				mul_cells.push_back(cell);
			if (cell->type.in(ID($add), ID($sub)))
				for (IdString AB : {ID::A, ID::B}) {
					IdString BA = (AB == ID::A ? ID::B : ID::A);
					add_index.add(port(cell, AB), {cell, BA});
				}
			if (cell->type.in(ID($mux)))
				for (IdString AB : {ID::A, ID::B}) {
					IdString BA = (AB == ID::A ? ID::B : ID::A);
					mux_index.add({port(cell, AB), port(cell, BA)}, {cell, AB});
				}
			if (cell->type.in(ID($dff), ID($adff), ID($dffe), ID($adffe)) && param(cell, ID::CLK_POLARITY).as_bool())
				ff_index.add({port(cell, ID::D), port(cell, ID::Q)}, cell);
		}
	}

	// Explores flag false, then flag true
	void branch(const Match &m, bool Match::*flag, Stage next)
	{
		Match n = m;
		n.*flag = false;
		(this->*next)(n);
		if (unwinding())
			return;
		n.*flag = true;
		(this->*next)(n);
	}

	void code_mux_in_pattern(const Match &m)
	{
		branch(m, &Match::mux_in_pattern, &QlDspMacc::match_mul);
	}

	// The multiplier is at the center of our pattern
	bool mul_users_fit(const Match &m, Cell *mul) const
	{
		// It has either two or three consumers depending on whether there's a mux
		// in the pattern or not
		return nusers(port(mul, ID::Y)) == (m.mux_in_pattern ? 3 : 2);
	}

	void match_mul(const Match &m)
	{
		match_each(m, mul_cells, &QlDspMacc::mul_users_fit, &Match::mul, &QlDspMacc::code_output_registered);
	}

	void code_output_registered(const Match &m)
	{
		branch(m, &Match::output_registered, &QlDspMacc::match_add);
	}

	void match_add(const Match &m)
	{
		MatchFrame frame(ctx);
		// One input to the adder is fed by the multiplier
		for (auto &[add, BA] : candidates(add_index.find(port(m.mul, ID::Y)))) {
			// Adder has either two or three consumers; it will have three consumers
			// IFF there's no mux in the pattern and the multiplier-accumulator result
			// is taken unregistered
			if (nusers(port(add, ID::Y)) != (!m.mux_in_pattern && !m.output_registered ? 3 : 2))
				continue;
			Match n = m;
			n.add = add;
			// Save the other input port, it needs to be fed by the flip-flop
			n.add_ba = BA;
			if (descend(frame, add, &QlDspMacc::match_mux, n))
				return;
		}
	}

	void match_mux(const Match &m)
	{
		if (!m.mux_in_pattern) {
			match_none(m, &Match::mux, &QlDspMacc::match_ff);
			return;
		}
		MatchFrame frame(ctx);
		for (auto &[mux, AB] : candidates(mux_index.find({port(m.mul, ID::Y), port(m.add, ID::Y)}))) {
			if (nusers(port(mux, ID::Y)) != (m.output_registered ? 2 : 3))
				continue;
			Match n = m;
			n.mux = mux;
			n.mux_ab = AB;
			if (descend(frame, mux, &QlDspMacc::match_ff, n))
				return;
		}
	}

	bool ff_users_fit(const Match &m, Cell *ff) const
	{
		return nusers(port(ff, ID::Q)) == (m.output_registered ? 3 : 2);
	}

	void match_ff(const Match &m)
	{
		match_each(m, ff_index.find({m.mux_in_pattern ? port(m.mux, ID::Y) : port(m.add, ID::Y), port(m.add, m.add_ba)}), &QlDspMacc::ff_users_fit, &Match::ff, &QlDspMacc::accept);
	}
};

YOSYS_NAMESPACE_END

#endif
