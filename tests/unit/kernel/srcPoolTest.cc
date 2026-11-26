#include <gtest/gtest.h>

#include "kernel/log.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

TEST(SrcPoolTest, MergeIsUnion)
{
	TwinePool twines;
	SrcPool srcs(twines);
	SrcRef a = srcs.add_parsed("top.v:1.2-1.3");
	SrcRef b = srcs.add_parsed("top.v:2.2-2.3");
	SrcRef both = srcs.merge(a, b);

	EXPECT_EQ(srcs.add_parsed("top.v:1.2-1.3"), a);
	EXPECT_EQ(srcs.merge(b, a), both);
	EXPECT_EQ(srcs.merge(both, a), both);
	EXPECT_EQ(srcs.add_parsed("top.v:2.2-2.3|top.v:1.2-1.3"), both);
}

TEST(SrcPoolTest, StructuredMatchesParse)
{
	TwinePool twines;
	SrcPool srcs(twines);
	IdString top = srcs.file("top.v");
	IdString sub = srcs.file("sub.v");
	IdString locs[] = {srcs.location(top, 10, 2, 10, 3), srcs.location(sub, 4, 5), srcs.location(top, 9)};

	EXPECT_EQ(srcs.add(locs[0]), srcs.add_parsed("top.v:10.2-10.3"));
	EXPECT_EQ(srcs.add(locs), srcs.add_parsed("top.v:9|top.v:10.2-10.3|sub.v:4.5"));
	EXPECT_EQ(srcs.str(srcs.add(locs)), "sub.v:4.5|top.v:9|top.v:10.2-10.3");
}

TEST(SrcPoolTest, CopyFromReinterns)
{
	TwinePool twines_a, twines_b;
	SrcPool a(twines_a), b(twines_b);
	b.add_parsed("other.v:9.9-9.9");
	SrcRef ref = a.add_parsed("top.v:1.2-1.3");

	EXPECT_EQ(b.str(b.copy_from(a, ref)), "top.v:1.2-1.3");
}

#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
TEST(SrcPoolTest, ForeignHandleDies)
{
	TwinePool twines_a, twines_b;
	SrcPool a(twines_a), b(twines_b);
	SrcRef ref = a.add_parsed("top.v:1.2-1.3");
	b.add_parsed("top.v:1.2-1.3");

	EXPECT_DEATH({ logger().add_sink<ConsoleLogSink>(); b.str(ref); }, "ref.serial == 0");
}

TEST(SrcPoolTest, CollectedHandleDies)
{
	RTLIL::Design design;
	SrcRef ref = design.srcs().add_parsed("top.v:1.2-1.3");
	design.gc_twines();

	EXPECT_DEATH({ logger().add_sink<ConsoleLogSink>(); design.srcs().str(ref); }, "is_live\\(ref\\)");
}
#endif

YOSYS_NAMESPACE_END
