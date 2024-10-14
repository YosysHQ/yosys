#include <gtest/gtest.h>
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

namespace RTLIL {

	class KernelRtlilTest : public testing::Test {};

	TEST_F(KernelRtlilTest, ConstAssignCompare)
	{
		Const c1;
		Const c2;
		c2 = c1;
		Const c3(c2);
		EXPECT_TRUE(c2 == c3);
		EXPECT_FALSE(c2 < c3);
	}

	TEST_F(KernelRtlilTest, ConstStr) {
		// We have multiple distinct sections since it's annoying
		// to list multiple testcases as friends of Const in kernel/rtlil.h
		{
			std::string foo = "foo";
			Const c1 = foo;
			Const c2;
			c2 = c1;
			Const c3(c2);
			EXPECT_TRUE(c1.is_str());
			EXPECT_TRUE(c2.is_str());
			EXPECT_TRUE(c3.is_str());
		}

		{
			// A binary constant is bitvec backed
			Const cb1(0, 10);
			Const cb2(1, 10);
			Const cb3(cb2);
			std::vector<bool> v1 {false, true};
			std::vector<State> v2 {State::S0, State::S1};
			Const cb4(v1);
			Const cb5(v2);
			EXPECT_TRUE(cb4 == cb5);
			EXPECT_TRUE(cb1.is_bits());
			EXPECT_TRUE(cb2.is_bits());
			EXPECT_TRUE(cb3.is_bits());
			EXPECT_TRUE(cb4.is_bits());
			EXPECT_TRUE(cb5.is_bits());
			EXPECT_EQ(cb1.size(), 10);
			EXPECT_EQ(cb2.size(), 10);
			EXPECT_EQ(cb3.size(), 10);
		}

		{
			// A string constructed Const starts off packed
			std::string foo = "foo";
			Const cs1 = foo;
			EXPECT_TRUE(cs1.is_str());

			// It can be iterated without mutating
			int i = 0;
			for (auto bit : cs1) {
				i += bit;
			}
			EXPECT_EQ(i, 16);
			EXPECT_TRUE(cs1.is_str());

			// It can be mutated with the bits() view
			// and decays into unpacked
			for (auto& bit : cs1.bits()) {
				bit = State::Sx;
			}
			EXPECT_TRUE(cs1.is_bits());
		}

	}
}

YOSYS_NAMESPACE_END
