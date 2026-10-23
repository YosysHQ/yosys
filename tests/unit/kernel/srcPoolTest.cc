#include <gtest/gtest.h>

#include "kernel/log.h"
#include "kernel/srcpool.h"

YOSYS_NAMESPACE_BEGIN

TEST(SrcPoolTest, MergeIsUnion)
{
	TwinePool twines;
	SrcPool srcs(twines);
	SrcRef a = srcs.add("top.v:1.2-1.3");
	SrcRef b = srcs.add("top.v:2.2-2.3");
	SrcRef both = srcs.merge(a, b);

	EXPECT_EQ(srcs.add("top.v:1.2-1.3"), a);
	EXPECT_EQ(srcs.merge(both, a), both);
	EXPECT_EQ(srcs.add("top.v:2.2-2.3|top.v:1.2-1.3"), both);
}

TEST(SrcPoolTest, CopyFromReinterns)
{
	TwinePool twines_a, twines_b;
	SrcPool a(twines_a), b(twines_b);
	b.add("other.v:9.9-9.9");
	SrcRef ref = a.add("top.v:1.2-1.3");

	EXPECT_EQ(b.str(b.copy_from(a, ref)), "top.v:1.2-1.3");
}

#ifdef YOSYS_ENABLE_INDEX_PROVENANCE
TEST(SrcPoolTest, ForeignHandleDies)
{
	TwinePool twines_a, twines_b;
	SrcPool a(twines_a), b(twines_b);
	SrcRef ref = a.add("top.v:1.2-1.3");
	b.add("top.v:1.2-1.3");

	EXPECT_DEATH({ logger().add_sink<ConsoleLogSink>(); b.str(ref); }, "ref.serial == 0");
}

TEST(SrcPoolTest, CollectedHandleDies)
{
	TwinePool twines;
	SrcPool srcs(twines);
	SrcRef ref = srcs.add("top.v:1.2-1.3");
	srcs.gc(SrcPool::Marks{});

	EXPECT_DEATH({ logger().add_sink<ConsoleLogSink>(); srcs.str(ref); }, "is_live\\(ref\\)");
}
#endif

YOSYS_NAMESPACE_END
