#include <gtest/gtest.h>

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

namespace {

int some_weird_function(Cell *) { return 0; }
int other_weird_function(Cell *) { return 1; }

// [foobar_match]
struct FoobarMatch
{
	Cell *ff = nullptr;
	Cell *mul = nullptr;
	int width = {};
};
// [/foobar_match]

struct Foobar : MatchPattern<Foobar, FoobarMatch>
{
	vector<Cell*> ff_cells = {};
	MatchIndex<SigSpec> mul_index = {};

	Foobar(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &Foobar::match_ff)
	{
		for (auto cell : cells) {
			if (cell->type == ID($dff))
				ff_cells.push_back(cell);
			if (cell->type == ID($mul) && nusers(port(cell, ID::Y)) == 2)
				mul_index.add(port(cell, ID::Y), cell);
		}
	}
	// [/foobar_decl]

	// [udata]
	int min_data_width = {};
	int max_data_width = {};
	// [/udata]

	void match_ff(const Match &m)
	{
		match_each(m, ff_cells, &Match::ff, &Foobar::match_mul);
	}

	// [match_mul]
	void match_mul(const Match &m)
	{
		if (m.ff) {
			MatchFrame frame(ctx);
			for (Cell *mul : mul_index.find(port(m.ff, ID::D))) {
				if (blacklisted(mul))
					continue;
				if (!(some_weird_function(mul) < other_weird_function(m.ff)))
					continue;
				Match n = m;
				n.mul = mul;
				frame.enter(mul);
				code_width(n);
				if (frame.leave())
					return;
			}
		}
		Match n = m;
		n.mul = nullptr;
		code_width(n);
	}
	// [/match_mul]

	// [code_width]
	void code_width(const Match &m)
	{
		Match n = m;
		n.width = GetSize(port(n.ff, ID::Q));
		code_check(n);
	}
	// [/code_width]

	// [code_check]
	void code_check(const Match &m)
	{
		if (m.width < min_data_width || m.width > max_data_width)
			return;
		accept(m);
	}
	// [/code_check]
};

// [foobar_callback]
void foobar_callback(Foobar &pm, const Foobar::Match &st)
{
	log("found matching 'ff' cell in %s: %s\n", pm.module, st.ff);
	if (st.mul)
		log("          with 'mul' cell: %s\n", st.mul);
}
// [/foobar_callback]

void blacklist_ff(Foobar &pm, const Foobar::Match &st)
{
	pm.blacklist(st.ff);
}

Module *foobar_module(Design &design)
{
	Module *module = design.addModule("\\top");
	Wire *clk = module->addWire("\\clk");
	Wire *a = module->addWire("\\a", 4);
	Wire *b = module->addWire("\\b", 4);
	Wire *e = module->addWire("\\e", 8);
	Wire *p = module->addWire("\\p", 8);
	Wire *q1 = module->addWire("\\q1", 8);
	Wire *q2 = module->addWire("\\q2", 8);
	for (Wire *w : {clk, a, b, e})
		w->port_input = true;
	for (Wire *w : {q1, q2})
		w->port_output = true;
	module->fixup_ports();
	module->addMul("\\mul", a, b, p);
	module->addDff("\\ff1", clk, p, q1);
	module->addDff("\\ff2", clk, e, q2);
	return module;
}

TEST(MatcherDocTest, foobar)
{
	Design design;
	Module *module = foobar_module(design);

	// [setup]
	MatchContext ctx(module);
	Foobar pm(ctx, module->selected_cells());
	// [/setup]

	pm.min_data_width = 1;
	pm.max_data_width = 32;
	// ff1 with and without the optional mul, ff2 without
	EXPECT_EQ(pm.run(), 3);

	// [run]
	pm.run(foobar_callback);
	// [/run]
	EXPECT_EQ(pm.accept_cnt, 3);

	pm.max_data_width = 4;
	EXPECT_EQ(pm.run(), 0);
}

TEST(MatcherDocTest, foobarBlacklist)
{
	Design design;
	Module *module = foobar_module(design);
	MatchContext ctx(module);
	Foobar pm(ctx, module->selected_cells());
	pm.max_data_width = 32;
	Cell *mul = module->cell("\\mul");

	// [blacklist]
	pm.blacklist(mul);
	// [/blacklist]
	EXPECT_EQ(pm.run(), 2);
}

TEST(MatcherDocTest, foobarBlacklistInCallback)
{
	Design design;
	Module *module = foobar_module(design);
	MatchContext ctx(module);
	Foobar pm(ctx, module->selected_cells());
	pm.max_data_width = 32;
	// blacklisting ff1 after its match with mul skips its match without mul
	EXPECT_EQ(pm.run(blacklist_ff), 2);
}

struct EqPmuxMatch
{
	Cell *eq = nullptr;
	Cell *pmux = nullptr;
	int pmux_slice = {};
	Cell *ne = nullptr;
	IdString ne_ab = {};
	IdString ne_ba = {};
};

struct EqPmux : MatchPattern<EqPmux, EqPmuxMatch>
{
	vector<Match> found = {};
	vector<Cell*> eq_cells = {};

	// [pmux_slice]
	struct PmuxSlice
	{
		Cell *cell = nullptr;
		int idx = {};
	};

	MatchIndex<SigBit, PmuxSlice> pmux_index = {};
	// [/pmux_slice]

	// [ne_choice]
	struct NeChoice
	{
		Cell *cell = nullptr;
		IdString AB = {};
		IdString BA = {};
	};

	MatchIndex<std::tuple<SigSpec, SigSpec>, NeChoice> ne_index = {};
	// [/ne_choice]

	EqPmux(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &EqPmux::match_eq)
	{
		for (auto cell : cells) {
			if (cell->type == ID($pmux))
				for (int idx = 0; idx < GetSize(port(cell, ID::S)); idx++)
					pmux_index.add(port(cell, ID::S)[idx], {cell, idx});
			if (cell->type == ID($ne))
				for (IdString AB : {ID::A, ID::B}) {
					IdString BA = AB == ID::A ? ID::B : ID::A;
					ne_index.add({port(cell, AB), port(cell, BA)}, {cell, AB, BA});
				}
			if (cell->type == ID($eq))
				eq_cells.push_back(cell);
		}
	}

	void match_eq(const Match &m)
	{
		match_each(m, eq_cells, &Match::eq, &EqPmux::match_pmux);
	}

	// [match_pmux]
	void match_pmux(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[pmux, idx] : pmux_index.find(port(m.eq, ID::Y))) {
			if (blacklisted(pmux))
				continue;
			Match n = m;
			n.pmux = pmux;
			n.pmux_slice = idx;
			frame.enter(pmux);
			match_ne(n);
			if (frame.leave())
				return;
		}
	}
	// [/match_pmux]

	// [match_ne]
	void match_ne(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[ne, AB, BA] : ne_index.find({port(m.eq, ID::A), port(m.eq, ID::B)})) {
			if (blacklisted(ne))
				continue;
			Match n = m;
			n.ne = ne;
			n.ne_ab = AB;
			n.ne_ba = BA;
			frame.enter(ne);
			accept(n);
			if (frame.leave())
				return;
		}
	}
	// [/match_ne]
};

void record_eqpmux(EqPmux &pm, const EqPmux::Match &st)
{
	pm.found.push_back(st);
}

TEST(MatcherDocTest, eqpmux)
{
	Design design;
	Module *module = design.addModule("\\top");
	Wire *a = module->addWire("\\a", 4);
	Wire *b = module->addWire("\\b", 4);
	Wire *c = module->addWire("\\c", 4);
	Wire *s0 = module->addWire("\\s0");
	Wire *s1 = module->addWire("\\s1");
	Wire *t = module->addWire("\\t");
	Wire *pa = module->addWire("\\pa", 4);
	Wire *pb = module->addWire("\\pb", 8);
	Wire *py = module->addWire("\\py", 4);
	SigSpec s = s1;
	s.append(s0);
	module->addEq("\\eq", a, b, s0);
	module->addNe("\\ne", b, a, s1);
	module->addPmux("\\pmux", pa, pb, s, py);
	module->addEq("\\eq_unused", a, c, t);

	MatchContext ctx(module);
	EqPmux pm(ctx, module->selected_cells());
	EXPECT_EQ(pm.run(record_eqpmux), 1);
	ASSERT_EQ(GetSize(pm.found), 1);
	EXPECT_EQ(pm.found[0].pmux_slice, 1);
	EXPECT_EQ(pm.found[0].ne_ab, ID::B);
	EXPECT_EQ(pm.found[0].ne_ba, ID::A);
}

struct AndTreeMatch
{
	Cell *root = nullptr;
	Cell *next = nullptr;
	IdString portAB = {};
};

struct AndTree : MatchPattern<AndTree, AndTreeMatch>
{
	vector<Cell*> stack = {};
	SigSpec leaves = {};
	dict<Cell*, SigSpec> found = {};

	vector<Cell*> and_cells = {};
	MatchIndex<SigSpec> and_index = {};

	AndTree(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &AndTree::match_root)
	{
		for (auto cell : cells) {
			if (cell->type == ID($and))
				and_cells.push_back(cell);
			if (cell->type == ID($and) && nusers(port(cell, ID::Y)) == 2)
				and_index.add(port(cell, ID::Y), cell);
		}
	}

	void match_root(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *root : and_cells) {
			if (blacklisted(root))
				continue;
			Match n = m;
			n.root = root;
			n.next = root;
			frame.enter(root);
			code_root(n);
			if (frame.leave())
				return;
		}
	}

	void code_root(const Match &m)
	{
		leaves = {};
		code_extend(m);
		if (unwinding())
			return;
		accept(m);
	}

	// [code_extend]
	void code_extend(const Match &m)
	{
		code_extend_body(m);
		if (m.next)
			stack.pop_back();
	}
	// [/code_extend]

	// [code_extend_body]
	void code_extend_body(const Match &m)
	{
		if (!m.next) {
			leaves.append(port(stack.back(), m.portAB));
			return;
		}
		stack.push_back(m.next);
		Match n = m;
		n.portAB = ID::A;
		tail(n);
		if (unwinding())
			return;
		n.portAB = ID::B;
		tail(n);
	}
	// [/code_extend_body]

	// [tail]
	void tail(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *next : and_index.find(port(stack.back(), m.portAB))) {
			if (blacklisted(next))
				continue;
			found_any_match = true;
			Match n = m;
			n.next = next;
			frame.enter(next);
			code_extend(n);
			if (frame.leave())
				return;
		}

		if (!found_any_match) {
			Match n = m;
			n.next = nullptr;
			code_extend(n);
		}

		if (should_generate(found_any_match, 10, 0)) {
			SigSpec Y = port(stack.back(), m.portAB);
			SigSpec A = module->addWire(NEW_ID, GetSize(Y));
			SigSpec B = module->addWire(NEW_ID, GetSize(Y));
			module->addAnd(NEW_ID, A, B, Y);
		}
	}
	// [/tail]
};

void record_tree(AndTree &pm, const AndTree::Match &st)
{
	pm.found[st.root] = pm.leaves;
}

void finish_tree(AndTree &pm, const AndTree::Match &)
{
	pm.finish();
}

Module *and_tree_module(Design &design)
{
	Module *module = design.addModule("\\top");
	Wire *a = module->addWire("\\a");
	Wire *b = module->addWire("\\b");
	Wire *c = module->addWire("\\c");
	Wire *d = module->addWire("\\d");
	Wire *x = module->addWire("\\x");
	Wire *y = module->addWire("\\y");
	Wire *z = module->addWire("\\z");
	for (Wire *w : {a, b, c, d})
		w->port_input = true;
	z->port_output = true;
	module->fixup_ports();
	module->addAnd("\\and1", a, b, x);
	module->addAnd("\\and2", c, d, y);
	module->addAnd("\\and3", x, y, z);
	return module;
}

TEST(MatcherDocTest, andTree)
{
	Design design;
	Module *module = and_tree_module(design);
	MatchContext ctx(module);
	AndTree pm(ctx, module->selected_cells());
	EXPECT_EQ(pm.run(record_tree), 3);
	EXPECT_TRUE(pm.stack.empty());

	pool<SigBit> abcd = {};
	for (auto name : {"\\a", "\\b", "\\c", "\\d"})
		abcd.insert(SigBit(module->wire(name)));
	EXPECT_EQ(pm.found.at(module->cell("\\and3")).to_sigbit_pool(), abcd);
	EXPECT_EQ(GetSize(pm.found.at(module->cell("\\and1"))), 2);
}

TEST(MatcherDocTest, andTreeFinish)
{
	Design design;
	Module *module = and_tree_module(design);
	MatchContext ctx(module);
	AndTree pm(ctx, module->selected_cells());
	EXPECT_EQ(pm.run(finish_tree), 1);
	EXPECT_TRUE(pm.stack.empty());
}

TEST(MatcherDocTest, andTreeGenerate)
{
	Design design;
	Module *module = and_tree_module(design);
	MatchContext ctx(module);
	AndTree pm(ctx, module->selected_cells());
	pm.run();
	EXPECT_EQ(GetSize(module->cells()), 3);

	ctx.generate_mode = true;
	for (int i = 0; i < 100 && GetSize(module->cells()) == 3; i++)
		pm.run();
	EXPECT_GT(GetSize(module->cells()), 3);
}

}

YOSYS_NAMESPACE_END
