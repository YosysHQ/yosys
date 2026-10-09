#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

TEST(PooledNameTest, OwnPool)
{
	TwinePool pool;
	IdString pub = pool.add(std::string("\\zz_alpha"));
	IdString priv = pool.add(std::string("$zz_beta"));

	PooledName a(&pool, pub);
	PooledName b(&pool, priv);

	EXPECT_EQ(a.str(), "\\zz_alpha");
	EXPECT_EQ(a.unescape(), "zz_alpha");
	EXPECT_TRUE(a.isPublic());
	EXPECT_EQ(b.str(), "$zz_beta");
	EXPECT_EQ(b.unescape(), "$zz_beta");
	EXPECT_FALSE(b.isPublic());
}

TEST(PooledNameTest, DivergedPools)
{
	TwinePool pool_a;
	TwinePool pool_b;
	pool_b.add(std::string("\\zz_filler"));

	IdString in_a = pool_a.add(std::string("\\zz_shared"));
	IdString in_b = pool_b.add(std::string("\\zz_shared"));
	ASSERT_NE(in_a, in_b);

	PooledName a(&pool_a, in_a);
	PooledName b(&pool_b, in_b);

	EXPECT_EQ(a.str(), b.str());
	EXPECT_NE(a.ref(), b.ref());
	EXPECT_FALSE(a == b);
}

TEST(PooledNameTest, PoollessConstids)
{
	PooledName kind(ID($state));
	EXPECT_EQ(kind.str(), "$state");
	EXPECT_EQ(kind.unescape(), "$state");
	EXPECT_TRUE(kind == ID($state));
}

TEST(PooledNameTest, PoollessLookup)
{
	TwinePool pool;
	IdString ref = pool.add(std::string("\\zz_gamma"));

	dict<PooledName, int> by_name;
	by_name[PooledName(&pool, ref)] = 7;

	EXPECT_EQ(by_name.at(PooledName(ref)), 7);
	EXPECT_EQ(by_name.at(PooledName(&pool, ref)), 7);
}

TEST(PooledNameTest, FromMasqs)
{
	Design design;
	Module *mod = design.addModule(std::string("\\zz_top"));
	Wire *w = mod->addWire(std::string("\\zz_wire"), 1);
	Cell *cell = mod->addCell(std::string("\\zz_cell"), ID($and));

	EXPECT_EQ(PooledName(mod->name).str(), "\\zz_top");
	EXPECT_EQ(PooledName(w->name).str(), "\\zz_wire");
	EXPECT_EQ(PooledName(cell->name).unescape(), "zz_cell");
	EXPECT_EQ(PooledName(cell->type).str(), "$and");
}

TEST(PooledNameTest, NullName)
{
	PooledName none;
	EXPECT_TRUE(none.empty());
	EXPECT_EQ(none.str(), "");
	EXPECT_EQ(none.unescape(), "");
}

YOSYS_NAMESPACE_END
