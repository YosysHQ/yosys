#include <gtest/gtest.h>
#include "passes/opt/opt_dff_comp.h"

YOSYS_NAMESPACE_BEGIN

class FindComplementaryPatternVarTest : public ::testing::Test {
protected:
	RTLIL::Design *design;
	RTLIL::Module *module;
	RTLIL::Wire *wire_a;
	RTLIL::Wire *wire_b;
	RTLIL::Wire *wire_c;
	RTLIL::Wire *bus;

	void SetUp() override {
		design = new RTLIL::Design;
		module = design->addModule(ID(test_module));
		wire_a = module->addWire(ID(a));
		wire_b = module->addWire(ID(b));
		wire_c = module->addWire(ID(c));
		bus = module->addWire(ID(bus), 4);
	}

	void TearDown() override {
		delete design;
	}

	RTLIL::SigBit bit(RTLIL::Wire *w, int offset = 0) {
		return RTLIL::SigBit(w, offset);
	}
};

TEST_F(FindComplementaryPatternVarTest, EmptyPatterns) {
	pattern_t left, right;

	auto result = find_complementary_pattern_var(left, right);
	EXPECT_FALSE(result.has_value());
}

TEST_F(FindComplementaryPatternVarTest, IdenticalSingleVar) {
	pattern_t left, right;
	left[bit(wire_a)] = true;
	right[bit(wire_a)] = true;

	auto result = find_complementary_pattern_var(left, right);
	EXPECT_FALSE(result.has_value());
}

TEST_F(FindComplementaryPatternVarTest, ComplementarySingleVar) {
	pattern_t left, right;
	left[bit(wire_a)] = true;
	right[bit(wire_a)] = false;

	auto result = find_complementary_pattern_var(left, right);
	ASSERT_TRUE(result.has_value());
	EXPECT_EQ(result.value(), bit(wire_a));
}

TEST_F(FindComplementaryPatternVarTest, MissingKeyInRight) {
	pattern_t left, right;
	left[bit(wire_a)] = true;
	left[bit(wire_b)] = false;
	right[bit(wire_a)] = true;

	auto result = find_complementary_pattern_var(left, right);
	EXPECT_FALSE(result.has_value());
}

TEST_F(FindComplementaryPatternVarTest, TwoVarsOneComplementary) {
	pattern_t left, right;
	left[bit(wire_a)] = true;
	left[bit(wire_b)] = false;
	right[bit(wire_a)] = true;
	right[bit(wire_b)] = true;

	auto result = find_complementary_pattern_var(left, right);
	ASSERT_TRUE(result.has_value());
	EXPECT_EQ(result.value(), bit(wire_b));
}

TEST_F(FindComplementaryPatternVarTest, TwoVarsBothComplementary) {
	pattern_t left, right;
	left[bit(wire_a)] = true;
	left[bit(wire_b)] = false;
	right[bit(wire_a)] = false;
	right[bit(wire_b)] = true;

	auto result = find_complementary_pattern_var(left, right);
	EXPECT_FALSE(result.has_value());
}

TEST_F(FindComplementaryPatternVarTest, LeftSubsetOfRight) {
	pattern_t left, right;
	left[bit(wire_a)] = true;
	left[bit(wire_b)] = false;
	right[bit(wire_a)] = true;
	right[bit(wire_b)] = true;
	right[bit(wire_c)] = false;

	auto result = find_complementary_pattern_var(left, right);
	ASSERT_TRUE(result.has_value());
	EXPECT_EQ(result.value(), bit(wire_b));
}

TEST_F(FindComplementaryPatternVarTest, ThreeVarsAllSame) {
	pattern_t left, right;
	left[bit(wire_a)] = true;
	left[bit(wire_b)] = false;
	left[bit(wire_c)] = true;
	right[bit(wire_a)] = true;
	right[bit(wire_b)] = false;
	right[bit(wire_c)] = true;

	auto result = find_complementary_pattern_var(left, right);
	EXPECT_FALSE(result.has_value());
}

TEST_F(FindComplementaryPatternVarTest, PracticalPatternSimplification) {
	pattern_t pattern1, pattern2;
	pattern1[bit(bus, 0)] = true;
	pattern1[bit(bus, 1)] = true;
	pattern2[bit(bus, 0)] = true;
	pattern2[bit(bus, 1)] = false;

	auto result = find_complementary_pattern_var(pattern1, pattern2);
	ASSERT_TRUE(result.has_value());
	EXPECT_EQ(result.value(), bit(bus, 1));

	// Swapped args
	auto result2 = find_complementary_pattern_var(pattern2, pattern1);
	ASSERT_TRUE(result2.has_value());
	EXPECT_EQ(result2.value(), bit(bus, 1));
}

TEST_F(FindComplementaryPatternVarTest, MuxTreeClockEnableDetection) {
	pattern_t feedback_path1, feedback_path2;
	feedback_path1[bit(wire_a)] = true;
	feedback_path1[bit(wire_b)] = true;
	feedback_path2[bit(wire_a)] = true;
	feedback_path2[bit(wire_b)] = false;

	auto comp = find_complementary_pattern_var(feedback_path1, feedback_path2);
	ASSERT_TRUE(comp.has_value());
	EXPECT_EQ(comp.value(), bit(wire_b));

	pattern_t simplified = feedback_path1;
	simplified.erase(comp.value());

	EXPECT_EQ(simplified.size(), 1);
	EXPECT_TRUE(simplified.count(bit(wire_a)));
	EXPECT_TRUE(simplified[bit(wire_a)]);
}

TEST_F(FindComplementaryPatternVarTest, AsymmetricPatterns) {
	pattern_t left, right;
	left[bit(wire_a)] = true;
	right[bit(wire_a)] = false;
	right[bit(wire_b)] = true;
	right[bit(wire_c)] = false;

	auto result = find_complementary_pattern_var(left, right);
	ASSERT_TRUE(result.has_value());
	EXPECT_EQ(result.value(), bit(wire_a));
}

TEST_F(FindComplementaryPatternVarTest, WireOffsetDistinction) {
	pattern_t left, right;
	left[bit(bus, 0)] = true;
	left[bit(bus, 1)] = false;
	right[bit(bus, 0)] = true;
	right[bit(bus, 1)] = true;
	right[bit(bus, 2)] = false;

	auto result = find_complementary_pattern_var(left, right);
	ASSERT_TRUE(result.has_value());
	EXPECT_EQ(result.value(), bit(bus, 1));
}

YOSYS_NAMESPACE_END
