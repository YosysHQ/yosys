#include <gtest/gtest.h>

#include "kernel/io.h"

YOSYS_NAMESPACE_BEGIN

TEST(KernelStringfTest, integerTruncation)
{
	EXPECT_EQ(stringf("%d", 1LL << 32), "0");
	EXPECT_EQ(stringf("%u", 1LL << 32), "0");
	EXPECT_EQ(stringf("%x", 0xff12345678LL), "12345678");
	EXPECT_EQ(stringf("%hu", 0xff12345678LL), "22136");
}

TEST(KernelStringfTest, charFormat)
{
        EXPECT_EQ(stringf("%c", 256), std::string_view("\0", 1));
        EXPECT_EQ(stringf("%c", -1), "\377");
}

TEST(KernelStringfTest, floatFormat)
{
	EXPECT_EQ(stringf("%g", 1.0), "1");
}

TEST(KernelStringfTest, intToFloat)
{
        EXPECT_EQ(stringf("%g", 1), "1");
}

TEST(KernelStringfTest, floatToInt)
{
        EXPECT_EQ(stringf("%d", 1.0), "1");
        EXPECT_EQ(stringf("%d", -1.6), "-1");
}

TEST(KernelStringfTest, stringParam)
{
        EXPECT_EQ(stringf("%s", std::string("hello")), "hello");
}

TEST(KernelStringfTest, stringViewParam)
{
        EXPECT_EQ(stringf("%s", std::string_view("hello")), "hello");
}

TEST(KernelStringfTest, escapePercent)
{
	EXPECT_EQ(stringf("%%"), "%");
}

TEST(KernelStringfTest, trailingPercent)
{
	EXPECT_EQ(stringf("%"), "%");
}

TEST(KernelStringfTest, dynamicWidth)
{
        EXPECT_EQ(stringf("%*s", 8, "hello"), "   hello");
}

TEST(KernelStringfTest, dynamicPrecision)
{
        EXPECT_EQ(stringf("%.*f", 4, 1.0), "1.0000");
}

TEST(KernelStringfTest, dynamicWidthAndPrecision)
{
        EXPECT_EQ(stringf("%*.*f", 8, 4, 1.0), "  1.0000");
}

TEST(KernelStringfTest, dynamicPrecisionInt)
{
        EXPECT_EQ(stringf("%.*d", 4, 7), "0007");
}

TEST(KernelStringfTest, dynamicWidthAndPrecisionInt)
{
        EXPECT_EQ(stringf("%*.*d", 8, 4, 7), "    0007");
}

YOSYS_NAMESPACE_END
