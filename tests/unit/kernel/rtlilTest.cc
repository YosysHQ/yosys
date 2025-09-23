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
		virtual void SetUp() override {
			IdString::ensure_prepopulated();
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

			// It can be mutated via bit iteration and decays into unpacked
			// when an non-defined bit is set.
			for (auto b : cs1) {
				b = State::Sx;
			}
			EXPECT_TRUE(cs1.is_bits());
		}

		{
			Const c(0x12345678);
			EXPECT_TRUE(c.is_str());
			EXPECT_EQ(c.as_int(), 0x12345678);
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(0xab, 8);
			EXPECT_TRUE(c.is_str());
			EXPECT_EQ(c.as_int(), 0xab);
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(0x12345678, 80);
			EXPECT_TRUE(c.is_str());
			EXPECT_EQ(c.as_int(), 0x12345678);
			EXPECT_EQ(c[79], S0);
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(-1, 80);
			EXPECT_TRUE(c.is_str());
			EXPECT_EQ(c.as_int(), -1);
			EXPECT_EQ(c[79], S1);
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(1 << 24);
			EXPECT_TRUE(c.is_str());
			EXPECT_TRUE(c.as_bool());
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(0x2, 8);
			EXPECT_TRUE(c.is_str());
			EXPECT_EQ(c.as_string(), "00000010");
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(" ");
			EXPECT_TRUE(c.is_str());
			EXPECT_EQ(c.decode_string(), " ");
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(" ");
			EXPECT_TRUE(c.is_str());
			EXPECT_EQ(c.decode_string(), " ");
			EXPECT_TRUE(c.is_str());
		}

		{
			std::vector<State> v = {S0, S0, S0, S0, S0, S1, S0, S0};
			Const c(v);
			EXPECT_EQ(c.decode_string(), " ");
		}

		{
			std::vector<State> v = {S0, S0, S0, S0, S0, S1, S0, Sx};
			Const c(v);
			EXPECT_EQ(c.decode_string(), " ");
		}

		{
			Const c(" ");
			EXPECT_TRUE(c.is_str());
			EXPECT_FALSE(c.is_fully_zero());
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(" ");
			EXPECT_TRUE(c.is_str());
			EXPECT_FALSE(c.is_fully_ones());
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(" ");
			EXPECT_TRUE(c.is_str());
			EXPECT_TRUE(c.is_fully_def());
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(" ");
			EXPECT_TRUE(c.is_str());
			EXPECT_FALSE(c.is_fully_undef());
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(" ");
			EXPECT_TRUE(c.is_str());
			EXPECT_FALSE(c.is_fully_undef_x_only());
			EXPECT_TRUE(c.is_str());
		}

		{
			Const c(" ");
			EXPECT_TRUE(c.is_str());
			int pos;
			EXPECT_TRUE(c.is_onehot(&pos));
			EXPECT_EQ(pos, 5);
			EXPECT_TRUE(c.is_str());
		}
	}

	TEST_F(KernelRtlilTest, ConstConstIteratorWorks) {
		const Const c(0x2, 2);
		Const::const_iterator it = c.begin();
		ASSERT_NE(it, c.end());
		EXPECT_EQ(*it, State::S0);
		++it;
		ASSERT_NE(it, c.end());
		EXPECT_EQ(*it, State::S1);
		++it;
		EXPECT_EQ(it, c.end());
	}

	TEST_F(KernelRtlilTest, ConstConstIteratorPreincrement) {
		const Const c(0x2, 2);
		Const::const_iterator it = c.begin();
		EXPECT_EQ(*++it, State::S1);
	}

	TEST_F(KernelRtlilTest, ConstConstIteratorPostincrement) {
		const Const c(0x2, 2);
		Const::const_iterator it = c.begin();
		EXPECT_EQ(*it++, State::S0);
	}

	TEST_F(KernelRtlilTest, ConstIteratorWorks) {
		Const c(0x2, 2);
		Const::iterator it = c.begin();
		ASSERT_NE(it, c.end());
		EXPECT_EQ(*it, State::S0);
		++it;
		ASSERT_NE(it, c.end());
		EXPECT_EQ(*it, State::S1);
		++it;
		ASSERT_EQ(it, c.end());
	}

	TEST_F(KernelRtlilTest, ConstIteratorPreincrement) {
		Const c(0x2, 2);
		Const::iterator it = c.begin();
		EXPECT_EQ(*++it, State::S1);
	}

	TEST_F(KernelRtlilTest, ConstIteratorPostincrement) {
		Const c(0x2, 2);
		Const::iterator it = c.begin();
		EXPECT_EQ(*it++, State::S0);
	}

	TEST_F(KernelRtlilTest, ConstIteratorWriteWorks) {
		Const c(0x2, 2);
		Const::iterator it = c.begin();
		EXPECT_EQ(*it, State::S0);
		*it = State::S1;
		EXPECT_EQ(*it, State::S1);
	}

	TEST_F(KernelRtlilTest, ConstBuilder) {
		Const::Builder b;
		EXPECT_EQ(GetSize(b), 0);
		b.push_back(S0);
		EXPECT_EQ(GetSize(b), 1);
		b.push_back(S1);
		EXPECT_EQ(GetSize(b), 2);
		EXPECT_EQ(b.build(), Const(0x2, 2));
	}

	TEST_F(KernelRtlilTest, ConstSet) {
		Const c(0x2, 2);
		c.set(0, S1);
		EXPECT_EQ(c, Const(0x3, 2));
	}

	TEST_F(KernelRtlilTest, ConstResize) {
		Const c(0x2, 2);
		c.resize(4, S1);
		EXPECT_EQ(c, Const(0xe, 4));
	}

	TEST_F(KernelRtlilTest, ConstEqualStr) {
		EXPECT_EQ(Const("abc"), Const("abc"));
		EXPECT_NE(Const("abc"), Const("def"));
	}

	TEST_F(KernelRtlilTest, ConstEqualBits) {
		std::vector<State> v1 = {S0, S1};
		std::vector<State> v2 = {S1, S0};
		EXPECT_EQ(Const(v1), Const(v1));
		EXPECT_NE(Const(v1), Const(v2));
	}

	TEST_F(KernelRtlilTest, ConstEqualStrBits) {
		std::vector<State> v1 = {S0, S0, S0, S0, S0, S1, S0, S0};
		EXPECT_EQ(Const(v1), Const(" "));
		EXPECT_NE(Const(v1), Const("a"));
	}

	static Hasher::hash_t hash(const Const &c) {
		Hasher h;
		h = c.hash_into(h);
		return h.yield();
	}

	TEST_F(KernelRtlilTest, ConstEqualHashStrBits) {
		std::vector<State> v1 = {S0, S0, S0, S0, S0, S1, S0, S0};
		EXPECT_EQ(hash(Const(v1)), hash(Const(" ")));
		EXPECT_NE(hash(Const(v1)), hash(Const("a")));
	}

	TEST_F(KernelRtlilTest, ConstIsFullyZero) {
		EXPECT_TRUE(Const(0, 8).is_fully_zero());
		EXPECT_FALSE(Const(8, 8).is_fully_zero());
		EXPECT_TRUE(Const().is_fully_zero());
	}

	TEST_F(KernelRtlilTest, ConstIsFullyOnes) {
		EXPECT_TRUE(Const(0xf, 4).is_fully_ones());
		EXPECT_FALSE(Const(3, 4).is_fully_ones());
		EXPECT_TRUE(Const().is_fully_ones());
	}

	TEST_F(KernelRtlilTest, ConstIsFullyDef) {
		EXPECT_TRUE(Const(0xf, 4).is_fully_def());
		std::vector<State> v1 = {S0, Sx};
		EXPECT_FALSE(Const(v1).is_fully_def());
		EXPECT_TRUE(Const().is_fully_def());
	}

	TEST_F(KernelRtlilTest, ConstIsFullyUndef) {
		std::vector<State> v1 = {S0, Sx};
		EXPECT_FALSE(Const(v1).is_fully_undef());
		EXPECT_TRUE(Const(Sz, 2).is_fully_undef());
		EXPECT_TRUE(Const().is_fully_undef());
	}

	TEST_F(KernelRtlilTest, ConstIsFullyUndefXOnly) {
		std::vector<State> v1 = {Sx, Sz};
		EXPECT_FALSE(Const(v1).is_fully_undef_x_only());
		EXPECT_TRUE(Const(Sx, 2).is_fully_undef_x_only());
		EXPECT_TRUE(Const().is_fully_undef_x_only());
	}

	TEST_F(KernelRtlilTest, ConstIsOnehot) {
		int pos;
		EXPECT_TRUE(Const(0x80, 8).is_onehot(&pos));
		EXPECT_EQ(pos, 7);
		EXPECT_FALSE(Const(0x82, 8).is_onehot(&pos));
		EXPECT_FALSE(Const(0, 8).is_onehot(&pos));
		EXPECT_TRUE(Const(1, 1).is_onehot(&pos));
		EXPECT_EQ(pos, 0);
		EXPECT_FALSE(Const(Sx, 1).is_onehot(&pos));
		std::vector<State> v1 = {Sx, S1};
		EXPECT_FALSE(Const(v1).is_onehot(&pos));
		EXPECT_FALSE(Const().is_onehot(&pos));
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
