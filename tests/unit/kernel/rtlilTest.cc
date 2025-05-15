#include <gtest/gtest.h>
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

namespace RTLIL {

	struct SafePrintToStringParamName {
		template <class ParamType>
		std::string operator()(const testing::TestParamInfo<ParamType>& info) const {
			std::string name = testing::PrintToString(info.param);
			for (auto &c : name)
				if (!('0' <= c && c <= '9') && !('a' <= c && c <= 'z') && !('A' <= c && c <= 'Z')  ) c = '_';
			return name;
		}
	};

	class KernelRtlilTest : public testing::Test {
	protected:
		KernelRtlilTest() {
			if (log_files.empty()) log_files.emplace_back(stdout);
		}
	};

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

	class WireRtlVsHdlIndexConversionTest :
		public KernelRtlilTest,
		public testing::WithParamInterface<std::tuple<bool, int, int>>
	{};

	INSTANTIATE_TEST_SUITE_P(
		WireRtlVsHdlIndexConversionInstance,
		WireRtlVsHdlIndexConversionTest,
		testing::Values(
			std::make_tuple(false, 0, 10),
			std::make_tuple(true, 0, 10),
			std::make_tuple(false, 4, 10),
			std::make_tuple(true, 4, 10),
			std::make_tuple(false, -4, 10),
			std::make_tuple(true, -4, 10),
			std::make_tuple(false, 0, 1),
			std::make_tuple(true, 0, 1),
			std::make_tuple(false, 4, 1),
			std::make_tuple(true, 4, 1),
			std::make_tuple(false, -4, 1),
			std::make_tuple(true, -4, 1)
		),
		SafePrintToStringParamName()
	);

	TEST_P(WireRtlVsHdlIndexConversionTest, WireRtlVsHdlIndexConversion) {
		std::unique_ptr<Module> mod = std::make_unique<Module>();
		Wire *wire = mod->addWire(ID(test), 10);

		auto [upto, start_offset, width] = GetParam();

		wire->upto = upto;
		wire->start_offset = start_offset;
		wire->width = width;

		int smallest = INT_MAX;
		int largest = INT_MIN;

		for (int i = 0; i < wire->width; i++) {
			int j = wire->to_hdl_index(i);
			smallest = std::min(smallest, j);
			largest = std::max(largest, j);
			EXPECT_EQ(
				std::make_pair(wire->from_hdl_index(j), j),
				std::make_pair(i, wire->to_hdl_index(i))
			);
		}

		EXPECT_EQ(smallest, start_offset);
		EXPECT_EQ(largest, start_offset + wire->width - 1);

		for (int i = 1; i < wire->width; i++) {
			EXPECT_EQ(
				wire->to_hdl_index(i) - wire->to_hdl_index(i - 1),
				upto ? -1 : 1
			);
		}

		for (int j = smallest; j < largest; j++) {
			int i = wire->from_hdl_index(j);
			EXPECT_EQ(
				std::make_pair(wire->from_hdl_index(j), j),
				std::make_pair(i, wire->to_hdl_index(i))
			);
		}

		for (int i = -10; i < 0; i++)
			EXPECT_EQ(wire->to_hdl_index(i), INT_MIN);
		for (int i = wire->width; i < wire->width + 10; i++)
			EXPECT_EQ(wire->to_hdl_index(i), INT_MIN);
		for (int j = smallest - 10; j < smallest; j++)
			EXPECT_EQ(wire->from_hdl_index(j), INT_MIN);
		for (int j = largest + 1; j < largest + 11; j++)
			EXPECT_EQ(wire->from_hdl_index(j), INT_MIN);
	}

}

YOSYS_NAMESPACE_END
