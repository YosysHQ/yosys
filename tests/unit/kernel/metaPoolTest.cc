#include <gtest/gtest.h>

#include "kernel/metadata/metapool.h"

YOSYS_NAMESPACE_BEGIN

TEST(MetaPoolTest, HdlnameRoundTrips)
{
	TwinePool twines;
	MetaPool metas(twines);
	MetaRef ref = metas.with_hdlname(MetaRef::Null, "a b c");

	EXPECT_TRUE(ref.has_hdlname());
	EXPECT_FALSE(ref.has_scopename());
	EXPECT_EQ(metas.hdlname(ref), "a b c");
	EXPECT_EQ(metas.scopename(ref), "");
	EXPECT_EQ(metas.with_hdlname(MetaRef::Null, "a b c"), ref);
}

TEST(MetaPoolTest, NamesShareTheirScope)
{
	TwinePool twines;
	MetaPool metas(twines);
	MetaRef c = metas.with_hdlname(MetaRef::Null, "a b c");
	MetaRef d = metas.with_hdlname(MetaRef::Null, "a b d");

	EXPECT_EQ(metas[c].scope, metas[d].scope);
	EXPECT_NE(metas[c].hdlname, metas[d].hdlname);
}

TEST(MetaPoolTest, SingleNameLivesInRootScope)
{
	TwinePool twines;
	MetaPool metas(twines);
	MetaRef ref = metas.with_hdlname(MetaRef::Null, "x");

	EXPECT_EQ(metas.hdlname(ref), "x");
	EXPECT_EQ(metas.without_hdlname(ref), MetaRef::Null);
}

TEST(MetaPoolTest, ScopenameOnlyWithoutHdlname)
{
	TwinePool twines;
	MetaPool metas(twines);
	MetaRef scope = metas.with_scopename(MetaRef::Null, "a b");
	MetaRef named = metas.with_hdlname(MetaRef::Null, "a b c");

	EXPECT_TRUE(scope.has_scopename());
	EXPECT_EQ(metas.scopename(scope), "a b");
	EXPECT_EQ(metas.with_scopename(named, "q"), named);
	EXPECT_EQ(metas.without_hdlname(named), scope);
	EXPECT_EQ(metas.with_hdlname(named, ""), MetaRef::Null);
}

TEST(MetaPoolTest, TransferMovesIdentity)
{
	TwinePool twines;
	MetaPool metas(twines);
	MetaRef target = metas.with_hdlname(MetaRef::Null, "t");
	MetaRef source = metas.with_hdlname(MetaRef::Null, "a s");
	MetaRef moved = metas.transfer(target, source);

	EXPECT_EQ(metas.hdlname(moved), "a s");
	ASSERT_EQ(metas[moved].absorbed_hdlnames.size(), 1u);
	EXPECT_EQ(metas[moved].absorbed_hdlnames[0], metas[target].hdlname);
	EXPECT_EQ(metas.transfer(MetaRef::Null, source), source);
}

TEST(MetaPoolTest, AbsorbKeepsIdentity)
{
	TwinePool twines;
	MetaPool metas(twines);
	MetaRef target = metas.with_hdlname(MetaRef::Null, "t");
	MetaRef source = metas.with_hdlname(MetaRef::Null, "a s");
	MetaRef scope = metas.with_scopename(MetaRef::Null, "a");
	MetaRef absorbed = metas.absorb(metas.absorb(target, source), scope);

	EXPECT_EQ(metas.hdlname(absorbed), "t");
	ASSERT_EQ(metas[absorbed].absorbed_hdlnames.size(), 1u);
	EXPECT_EQ(metas[absorbed].absorbed_hdlnames[0], metas[source].hdlname);
	ASSERT_EQ(metas[absorbed].absorbed_scopes.size(), 1u);
	EXPECT_EQ(metas[absorbed].absorbed_scopes[0], metas[scope].scope);
	EXPECT_EQ(metas.absorb(absorbed, source), absorbed);
}

TEST(MetaPoolTest, CopyFromReinterns)
{
	TwinePool twines_a, twines_b;
	MetaPool a(twines_a), b(twines_b);
	b.with_hdlname(MetaRef::Null, "other");
	MetaRef ref = a.absorb(a.with_hdlname(MetaRef::Null, "a b"), a.with_scopename(MetaRef::Null, "c"));
	MetaRef copied = b.copy_from(a, ref);

	EXPECT_EQ(b.hdlname(copied), "a b");
	EXPECT_EQ(b[copied].absorbed_scopes.size(), 1u);
}

YOSYS_NAMESPACE_END
