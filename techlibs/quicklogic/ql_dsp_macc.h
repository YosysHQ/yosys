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

struct QlDspMacc : MatchPattern
{
	struct Match {
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
	using Callback = void (*)(QlDspMacc &, const Match &);

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
	Callback on_accept = nullptr;

	QlDspMacc(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx)
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

	int run(Callback callback = nullptr)
	{
		on_accept = callback;
		begin_run();
		code_mux_in_pattern(Match{});
		return end_run();
	}

	bool accept(const Match &m)
	{
		accept_cnt++;
		if (on_accept)
			on_accept(*this, m);
		return unwinding();
	}

	void code_mux_in_pattern(const Match &m)
	{
		Match n = m;
		n.mux_in_pattern = false;
		match_mul(n);
		if (unwinding())
			return;
		n.mux_in_pattern = true;
		match_mul(n);
	}

	// The multiplier is at the center of our pattern
	void match_mul(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *mul : mul_cells) {
			if (blacklisted(mul))
				continue;
			// It has either two or three consumers depending on whether there's a mux
			// in the pattern or not
			if (nusers(port(mul, ID::Y)) != (m.mux_in_pattern ? 3 : 2))
				continue;
			Match n = m;
			n.mul = mul;
			frame.enter(mul);
			code_output_registered(n);
			if (frame.leave())
				return;
		}
	}

	void code_output_registered(const Match &m)
	{
		Match n = m;
		n.output_registered = false;
		match_add(n);
		if (unwinding())
			return;
		n.output_registered = true;
		match_add(n);
	}

	void match_add(const Match &m)
	{
		MatchFrame frame(ctx);
		// One input to the adder is fed by the multiplier
		for (auto &[add, BA] : add_index.find(port(m.mul, ID::Y))) {
			if (blacklisted(add))
				continue;
			// Adder has either two or three consumers; it will have three consumers
			// IFF there's no mux in the pattern and the multiplier-accumulator result
			// is taken unregistered
			if (nusers(port(add, ID::Y)) != (!m.mux_in_pattern && !m.output_registered ? 3 : 2))
				continue;
			Match n = m;
			n.add = add;
			// Save the other input port, it needs to be fed by the flip-flop
			n.add_ba = BA;
			frame.enter(add);
			match_mux(n);
			if (frame.leave())
				return;
		}
	}

	void match_mux(const Match &m)
	{
		if (!m.mux_in_pattern) {
			Match n = m;
			n.mux = nullptr;
			match_ff(n);
			return;
		}
		MatchFrame frame(ctx);
		for (auto &[mux, AB] : mux_index.find({port(m.mul, ID::Y), port(m.add, ID::Y)})) {
			if (blacklisted(mux))
				continue;
			if (nusers(port(mux, ID::Y)) != (m.output_registered ? 2 : 3))
				continue;
			Match n = m;
			n.mux = mux;
			n.mux_ab = AB;
			frame.enter(mux);
			match_ff(n);
			if (frame.leave())
				return;
		}
	}

	void match_ff(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *ff : ff_index.find({m.mux_in_pattern ? port(m.mux, ID::Y) : port(m.add, ID::Y), port(m.add, m.add_ba)})) {
			if (blacklisted(ff))
				continue;
			if (nusers(port(ff, ID::Q)) != (m.output_registered ? 3 : 2))
				continue;
			Match n = m;
			n.ff = ff;
			frame.enter(ff);
			accept(n);
			if (frame.leave())
				return;
		}
	}
};

YOSYS_NAMESPACE_END

#endif
