#include <gtest/gtest.h>

#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

// Test fixture with helper functions
class SigSpecRemove2Test : public ::testing::Test {
protected:
	Design* d;
	Module* m;

	void SetUp() override {
		d = new Design;
		m = d->addModule("$test");
	}

	void TearDown() override {
		delete d;
	}

	// Create n wires with given width
	std::vector<Wire*> createWires(int count, int width = 4) {
		std::vector<Wire*> wires;
		for (int i = 0; i < count; i++) {
			Wire* w = m->addWire(stringf("$w%d", i), width);
			wires.push_back(w);
		}
		return wires;
	}

	// Append all wires to a SigSpec
	SigSpec wiresAsSigSpec(const std::vector<Wire*>& wires) {
		SigSpec sig;
		for (auto w : wires)
			sig.append(w);
		return sig;
	}

	// Create a SigSpec of constants
	SigSpec constsAsSigSpec(int count, int width = 4) {
		SigSpec sig;
		for (int i = 0; i < count; i++)
			sig.append(Const(i, width));
		return sig;
	}

	// Convert wires to pool of SigBits
	pool<SigBit> wiresToPool(const std::vector<Wire*>& wires) {
		pool<SigBit> pool;
		for (auto w : wires)
			for (auto &bit : SigSpec(w))
				pool.insert(bit);
		return pool;
	}

	// Convert wires to set of SigBits
	std::set<SigBit> wiresToSet(const std::vector<Wire*>& wires) {
		std::set<SigBit> set;
		for (auto w : wires)
			for (auto &bit : SigSpec(w))
				set.insert(bit);
		return set;
	}
};

TEST_F(SigSpecRemove2Test, WithSigSpecPattern)
{
	auto wires = createWires(4);
	SigSpec sig = wiresAsSigSpec(wires);
	SigSpec pattern(wires[1]);  // Remove w2
	SigSpec other = constsAsSigSpec(4);

	EXPECT_EQ(sig.size(), 16);
	sig.remove2(pattern, &other);
	EXPECT_EQ(sig.size(), 12);
	EXPECT_EQ(other.size(), 12);

	// Verify correct wires remain (w1, w3, w4)
	SigSpec expected;
	expected.append(wires[0]);
	expected.append(wires[2]);
	expected.append(wires[3]);
	EXPECT_EQ(sig, expected);
}

TEST_F(SigSpecRemove2Test, WithPoolPattern)
{
	auto wires = createWires(3);
	SigSpec sig = wiresAsSigSpec(wires);
	auto pattern = wiresToPool({wires[1]});
	SigSpec other = constsAsSigSpec(3);

	EXPECT_EQ(sig.size(), 12);
	sig.remove2(pattern, &other);
	EXPECT_EQ(sig.size(), 8);
	EXPECT_EQ(other.size(), 8);

	// Verify correct wires remain (w0, w2)
	SigSpec expected;
	expected.append(wires[0]);
	expected.append(wires[2]);
	EXPECT_EQ(sig, expected);
}

TEST_F(SigSpecRemove2Test, WithSetPattern)
{
	auto wires = createWires(3);
	SigSpec sig = wiresAsSigSpec(wires);
	auto pattern = wiresToSet({wires[1]});
	SigSpec other = constsAsSigSpec(3);

	EXPECT_EQ(sig.size(), 12);
	sig.remove2(pattern, &other);
	EXPECT_EQ(sig.size(), 8);
	EXPECT_EQ(other.size(), 8);

	// Verify correct wires remain (w0, w2)
	SigSpec expected;
	expected.append(wires[0]);
	expected.append(wires[2]);
	EXPECT_EQ(sig, expected);
}

TEST_F(SigSpecRemove2Test, ManyElements)
{
	const int num_wires = 100;
	auto wires = createWires(num_wires);
	SigSpec sig = wiresAsSigSpec(wires);

	// Remove every other wire
	std::vector<Wire*> to_remove;
	for (int i = 0; i < num_wires; i += 2)
		to_remove.push_back(wires[i]);
	auto pattern = wiresToPool(to_remove);

	EXPECT_EQ(sig.size(), num_wires * 4);
	sig.remove2(pattern, nullptr);
	EXPECT_EQ(sig.size(), (num_wires / 2) * 4);

	// Verify odd-indexed wires remain (w1, w3, w5, ..., w99)
	SigSpec expected;
	for (int i = 1; i < num_wires; i += 2)
		expected.append(wires[i]);
	EXPECT_EQ(sig, expected);
}

// Test remove2 with very large dataset to check scaling
TEST_F(SigSpecRemove2Test, VeryLargeScalingTest)
{
	const int num_wires = 50000;
	auto wires = createWires(num_wires);
	SigSpec sig = wiresAsSigSpec(wires);
	SigSpec other = constsAsSigSpec(num_wires);

	// Create pattern with many chunks (one per wire)
	SigSpec pattern;
	for (int i = 0; i < num_wires; i += 2)
		pattern.append(wires[i]);

	EXPECT_EQ(sig.size(), num_wires * 4);
	sig.remove2(pattern, &other);
	EXPECT_EQ(sig.size(), (num_wires / 2) * 4);
	EXPECT_EQ(other.size(), (num_wires / 2) * 4);

	// Spot-check: odd-indexed wires should remain at expected positions
	for (int i = 0; i < num_wires / 2; i++) {
		EXPECT_EQ(sig[i * 4 + 0].wire, wires[i * 2 + 1]);
		EXPECT_EQ(sig[i * 4 + 1].wire, wires[i * 2 + 1]);
		EXPECT_EQ(sig[i * 4 + 2].wire, wires[i * 2 + 1]);
		EXPECT_EQ(sig[i * 4 + 3].wire, wires[i * 2 + 1]);
	}
}

// Test multiple sequential removals (simulates removeSignalFromCaseTree)
TEST_F(SigSpecRemove2Test, MultipleSequentialRemovals)
{
	const int num_wires = 512;
	auto wires = createWires(num_wires);

	// Create many actions, each with one wire
	std::vector<SigSpec> actions;
	for (auto w : wires)
		actions.push_back(SigSpec(w));

	// Remove half the wires from all actions
	for (int i = 0; i < num_wires / 2; i++) {
		SigSpec pattern(wires[i]);
		for (auto &action : actions)
			if (action.size() > 0)
				action.remove2(pattern, nullptr);
	}

	// Verify correct actions were cleared
	for (int i = 0; i < num_wires; i++) {
		EXPECT_EQ(actions[i].size(), i < num_wires / 2 ? 0 : 4);
	}

	// Verify remaining actions contain the correct wires
	for (int i = num_wires / 2; i < num_wires; i++) {
		SigSpec expected(wires[i]);
		EXPECT_EQ(actions[i], expected);
	}
}

// Test remove2 with very large dataset to check scaling
TEST_F(SigSpecRemove2Test, PoolOverloadLargeDataset)
{
	const int num_wires = 50000;
	auto wires = createWires(num_wires, 1);
	SigSpec sig = wiresAsSigSpec(wires);
	SigSpec other = constsAsSigSpec(num_wires, 1);

	// Remove half
	pool<SigBit> pattern;
	for (int i = 0; i < num_wires; i += 2)
		pattern.insert(SigBit(wires[i], 0));

	EXPECT_EQ(sig.size(), num_wires);
	sig.remove2(pattern, &other);
	EXPECT_EQ(sig.size(), num_wires / 2);
	EXPECT_EQ(other.size(), num_wires / 2);

	// Spot-check: odd-indexed wires should remain
	for (int i = 0; i < num_wires / 2; i++) {
		EXPECT_EQ(sig[i].wire, wires[i * 2 + 1]);
	}
}

// Test set overload (same perf characteristics as pool)
TEST_F(SigSpecRemove2Test, SetOverloadLargeDataset)
{
	const int num_wires = 50000;
	auto wires = createWires(num_wires, 1);
	SigSpec sig = wiresAsSigSpec(wires);
	SigSpec other = constsAsSigSpec(num_wires, 1);

	// Remove half
	std::set<SigBit> pattern;
	for (int i = 0; i < num_wires; i += 2)
		pattern.insert(SigBit(wires[i], 0));

	EXPECT_EQ(sig.size(), num_wires);
	sig.remove2(pattern, &other);
	EXPECT_EQ(sig.size(), num_wires / 2);
	EXPECT_EQ(other.size(), num_wires / 2);

	// Spot-check: odd-indexed wires should remain
	for (int i = 0; i < num_wires / 2; i++) {
		EXPECT_EQ(sig[i].wire, wires[i * 2 + 1]);
	}
}

// Worst case: remove almost all elements
TEST_F(SigSpecRemove2Test, RemoveAlmostAllElements)
{
	const int num_wires = 10000;
	auto wires = createWires(num_wires, 1);
	SigSpec sig = wiresAsSigSpec(wires);

	// Remove all but last
	pool<SigBit> pattern;
	for (int i = 0; i < num_wires - 1; i++)
		pattern.insert(SigBit(wires[i], 0));

	EXPECT_EQ(sig.size(), num_wires);
	sig.remove2(pattern, nullptr);
	EXPECT_EQ(sig.size(), 1);
	EXPECT_EQ(sig[0].wire, wires[num_wires - 1]);
}

TEST_F(SigSpecRemove2Test, EmptyPattern)
{
	auto wires = createWires(1);
	SigSpec sig(wires[0]);
	pool<SigBit> empty_pattern;

	EXPECT_EQ(sig.size(), 4);
	sig.remove2(empty_pattern, nullptr);
	EXPECT_EQ(sig.size(), 4);

	// Verify the wire is unchanged
	SigSpec expected(wires[0]);
	EXPECT_EQ(sig, expected);
}

// Test that NULL wire bits (constants) are not removed
TEST_F(SigSpecRemove2Test, NullWireBitsStay)
{
	auto wires = createWires(1);
	SigSpec sig;
	sig.append(wires[0]);
	sig.append(Const(15, 4));

	// Try to remove the constants
	pool<SigBit> pattern;
	SigSpec const_spec(Const(15, 4));
	for (auto &bit : const_spec)
		pattern.insert(bit);

	EXPECT_EQ(sig.size(), 8);
	sig.remove2(pattern, nullptr);
	EXPECT_EQ(sig.size(), 8);  // Constants stay

	// Verify original content is preserved
	SigSpec expected;
	expected.append(wires[0]);
	expected.append(Const(15, 4));
	EXPECT_EQ(sig, expected);
}

TEST_F(SigSpecRemove2Test, PartialBitRemoval)
{
	Wire* w = m->addWire("$w1", 8);
	SigSpec sig(w);

	// Remove bits 2-5
	pool<SigBit> pattern;
	for (int i = 2; i < 6; i++)
		pattern.insert(SigBit(w, i));

	EXPECT_EQ(sig.size(), 8);
	sig.remove2(pattern, nullptr);
	EXPECT_EQ(sig.size(), 4);

	// Verify only bits 0,1,6,7 remain
	EXPECT_EQ(sig[0], SigBit(w, 0));
	EXPECT_EQ(sig[1], SigBit(w, 1));
	EXPECT_EQ(sig[2], SigBit(w, 6));
	EXPECT_EQ(sig[3], SigBit(w, 7));
}

YOSYS_NAMESPACE_END
