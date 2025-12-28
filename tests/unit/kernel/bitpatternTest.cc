#include <gtest/gtest.h>

#include "kernel/bitpattern.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

TEST(BitpatternTest, has)
{
    SigSpec _aaa = {RTLIL::Sa, RTLIL::Sa, RTLIL::Sa};
    SigSpec _01a = {RTLIL::S0, RTLIL::S1, RTLIL::Sa};
    SigSpec _011 = {RTLIL::S0, RTLIL::S1, RTLIL::S1};
    SigSpec _111 = {RTLIL::S1, RTLIL::S1, RTLIL::S1};

    EXPECT_TRUE(BitPatternPool(_aaa).has_any(_01a));
    EXPECT_TRUE(BitPatternPool(_01a).has_any(_01a));
    // 011 overlaps with 01a
    EXPECT_TRUE(BitPatternPool(_011).has_any(_01a));
    // overlap is symmetric
    EXPECT_TRUE(BitPatternPool(_01a).has_any(_011));
    EXPECT_FALSE(BitPatternPool(_111).has_any(_01a));

	EXPECT_TRUE(BitPatternPool(_aaa).has_all(_01a));
	EXPECT_TRUE(BitPatternPool(_01a).has_all(_01a));
    // 011 is covered by 01a
    EXPECT_TRUE(BitPatternPool(_01a).has_all(_011));
    // 01a is not covered by 011
    EXPECT_FALSE(BitPatternPool(_011).has_all(_01a));
    EXPECT_FALSE(BitPatternPool(_111).has_all(_01a));
}

YOSYS_NAMESPACE_END
