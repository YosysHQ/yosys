#ifndef TEST_PMGEN_H
#define TEST_PMGEN_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

struct TestPmgenReduceMatch
{
	IdString portname = {};
	Cell *first = nullptr;
	Cell *next = nullptr;
};

struct TestPmgenReduce : MatchPattern<TestPmgenReduce, TestPmgenReduceMatch>
{
	vector<pair<Cell*, IdString>> chain = {};
	vector<pair<Cell*, IdString>> longest_chain = {};
	pool<Cell*> non_first_cells = {};
	SigSpec leaves = {};

	vector<Cell*> first_cells = {};
	MatchIndex<std::tuple<IdString, SigSpec>> next_index = {};

	TestPmgenReduce(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &TestPmgenReduce::start)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($_AND_), ID($_OR_), ID($_XOR_)))
				first_cells.push_back(cell);
			if (cell->type.in(ID($_AND_), ID($_OR_), ID($_XOR_)) && nusers(port(cell, ID::Y)) == 2)
				next_index.add({cell->type, port(cell, ID::Y)}, cell);
		}
	}

	void start(const Match &m)
	{
		non_first_cells.clear();
		setup(m);
		if (unwinding())
			return;
		match_first(m);
	}

	void match_first(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *first : candidates(first_cells)) {
			if (non_first_cells.count(first))
				continue;
			found_any_match = true;
			Match n = m;
			n.first = first;
			if (descend(frame, first, &TestPmgenReduce::code_chain, n))
				return;
		}

		if (should_generate(found_any_match, 100, 0)) {
			SigSpec A = module->addWire(NEW_ID);
			SigSpec B = module->addWire(NEW_ID);
			SigSpec Y = module->addWire(NEW_ID);
			switch (rng(3))
			{
			case 0:
				module->addAndGate(NEW_ID, A, B, Y);
				break;
			case 1:
				module->addOrGate(NEW_ID, A, B, Y);
				break;
			case 2:
				module->addXorGate(NEW_ID, A, B, Y);
				break;
			}
		}
	}

	void code_chain(const Match &m)
	{
		code_chain_body(m);
		chain.pop_back();
		log_assert(chain.empty());
		if (GetSize(longest_chain) > 1)
			accept(m);
	}

	void code_chain_body(const Match &m)
	{
		leaves = SigSpec();
		longest_chain.clear();
		chain.push_back(make_pair(m.first, ID::A));
		tail(m);
		if (unwinding())
			return;
		chain.back().second = ID::B;
		tail(m);
	}

	void setup(const Match &m)
	{
		match_each(m, first_cells, &Match::first, &TestPmgenReduce::setup_code_portname);
	}

	void setup_code_portname(const Match &m)
	{
		Match n = m;
		n.portname = ID::A;
		setup_match_next(n);
		if (unwinding())
			return;
		n.portname = ID::B;
		setup_match_next(n);
	}

	void setup_match_next(const Match &m)
	{
		match_each(m, next_index.find({m.first->type, port(m.first, m.portname)}), &Match::next, &TestPmgenReduce::setup_code_mark);
	}

	void setup_code_mark(const Match &m)
	{
		non_first_cells.insert(m.next);
	}

	void tail(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *next : candidates(next_index.find({chain.back().first->type, port(chain.back().first, chain.back().second)}))) {
			found_any_match = true;
			Match n = m;
			n.next = next;
			if (descend(frame, next, &TestPmgenReduce::tail_code_extend, n))
				return;
		}

		if (!found_any_match)
			match_none(m, &Match::next, &TestPmgenReduce::tail_code_extend);

		if (should_generate(found_any_match, 10, 0)) {
			SigSpec A = module->addWire(NEW_ID);
			SigSpec B = module->addWire(NEW_ID);
			SigSpec Y = port(chain.back().first, chain.back().second);
			Cell *c = module->addAndGate(NEW_ID, A, B, Y);
			c->type = chain.back().first->type;
		}
	}

	void tail_code_extend(const Match &m)
	{
		tail_code_extend_body(m);
		if (m.next)
			chain.pop_back();
	}

	void tail_code_extend_body(const Match &m)
	{
		if (m.next) {
			chain.push_back(make_pair(m.next, ID::A));
			tail(m);
			if (unwinding())
				return;
			chain.back().second = ID::B;
			tail(m);
		} else {
			if (GetSize(chain) > GetSize(longest_chain))
				longest_chain = chain;
			leaves.append(port(chain.back().first, chain.back().second));
		}
	}
};

struct TestPmgenEqpmuxMatch
{
	bool eq_ne_signed = {};
	SigSpec eq_inA = {};
	SigSpec eq_inB = {};
	int pmux_slice_eq = {};
	int pmux_slice_ne = {};
	Cell *eq = nullptr;
	Cell *pmux = nullptr;
	Cell *ne = nullptr;
};

struct TestPmgenEqpmux : MatchPattern<TestPmgenEqpmux, TestPmgenEqpmuxMatch>
{
	struct PmuxSlice {
		Cell *cell = nullptr;
		int idx = {};
	};

	vector<Cell*> eq_cells = {};
	MatchIndex<SigBit, PmuxSlice> pmux_index = {};
	MatchIndex<std::tuple<SigSpec, SigSpec, int>> ne_index = {};
	MatchIndex<std::tuple<Cell*, SigBit>, PmuxSlice> pmux2_index = {};

	TestPmgenEqpmux(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &TestPmgenEqpmux::match_eq)
	{
		for (auto cell : cells) {
			if (cell->type == ID($eq))
				for ([[maybe_unused]] IdString AB : {ID::A, ID::B})
					eq_cells.push_back(cell);
			if (cell->type == ID($pmux))
				for (int idx = 0; idx < GetSize(port(cell, ID::S)); idx++) {
					pmux_index.add(port(cell, ID::S)[idx], {cell, idx});
					pmux2_index.add({cell, port(cell, ID::S)[idx]}, {cell, idx});
				}
			if (cell->type == ID($ne))
				for (IdString AB : {ID::A, ID::B}) {
					IdString BA = (AB == ID::A ? ID::B : ID::A);
					ne_index.add({port(cell, AB), port(cell, BA), int(param(cell, ID::A_SIGNED).as_bool())}, cell);
				}
		}
	}

	void match_eq(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *eq : candidates(eq_cells)) {
			found_any_match = true;
			Match n = m;
			n.eq = eq;
			n.eq_inA = port(eq, ID::A);
			n.eq_inB = port(eq, ID::B);
			n.eq_ne_signed = param(eq, ID::A_SIGNED).as_bool();
			if (descend(frame, eq, &TestPmgenEqpmux::match_pmux, n))
				return;
		}

		if (should_generate(found_any_match, 100, 10)) {
			SigSpec A = module->addWire(NEW_ID, rng(7)+1);
			SigSpec B = module->addWire(NEW_ID, rng(7)+1);
			SigSpec Y = module->addWire(NEW_ID);
			module->addEq(NEW_ID, A, B, Y, rng(2));
		}
	}

	void match_pmux(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (auto &[pmux, idx] : candidates(pmux_index.find(SigBit(port(m.eq, ID::Y))))) {
			found_any_match = true;
			Match n = m;
			n.pmux = pmux;
			n.pmux_slice_eq = idx;
			if (descend(frame, pmux, &TestPmgenEqpmux::match_ne, n))
				return;
		}

		if (should_generate(found_any_match, 100, 10)) {
			int width = rng(7) + 1;
			int numsel = rng(4) + 1;
			int idx = rng(numsel);

			SigSpec A = module->addWire(NEW_ID, width);
			SigSpec Y = module->addWire(NEW_ID, width);

			SigSpec B = {}, S = {};
			for (int i = 0; i < numsel; i++) {
				B.append(module->addWire(NEW_ID, width));
				S.append(i == idx ? port(m.eq, ID::Y) : module->addWire(NEW_ID));
			}

			module->addPmux(NEW_ID, A, B, S, Y);
		}
	}

	void match_ne(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *ne : candidates(ne_index.find({m.eq_inA, m.eq_inB, m.eq_ne_signed}))) {
			found_any_match = true;
			Match n = m;
			n.ne = ne;
			if (descend(frame, ne, &TestPmgenEqpmux::match_pmux2, n))
				return;
		}

		if (should_generate(found_any_match, 100, 10)) {
			SigSpec A = m.eq_inA, B = m.eq_inB, Y = {};
			if (rng(2)) {
				std::swap(A, B);
			}
			if (rng(2)) {
				for (auto bit : port(m.pmux, ID::S)) {
					if (nusers(bit) < 2)
						Y.append(bit);
				}
				if (GetSize(Y))
					Y = Y[rng(GetSize(Y))];
				else
					Y = module->addWire(NEW_ID);
			} else {
				Y = module->addWire(NEW_ID);
			}
			module->addNe(NEW_ID, A, B, Y, rng(2));
		}
	}

	void match_pmux2(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[pmux2, idx] : candidates(pmux2_index.find({m.pmux, SigBit(port(m.ne, ID::Y))}))) {
			Match n = m;
			n.pmux_slice_ne = idx;
			if (descend(frame, pmux2, &TestPmgenEqpmux::accept, n))
				return;
		}
	}
};

YOSYS_NAMESPACE_END

#endif
