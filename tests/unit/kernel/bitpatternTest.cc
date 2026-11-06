#include <gtest/gtest.h>

#include <algorithm>

#include "kernel/bitpattern.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

TEST(BitpatternTest, has)
{
    SigSpec _aaa = {RTLIL::Sa, RTLIL::Sa, RTLIL::Sa};
    SigSpec _01a = {RTLIL::S0, RTLIL::S1, RTLIL::Sa};
    SigSpec _011 = {RTLIL::S0, RTLIL::S1, RTLIL::S1};
    SigSpec _111 = {RTLIL::S1, RTLIL::S1, RTLIL::S1};
    SigSpec _01x = {RTLIL::S0, RTLIL::S1, RTLIL::Sx};
    SigSpec _01z = {RTLIL::S0, RTLIL::S1, RTLIL::Sz};

    EXPECT_TRUE(BitPatternPool(_aaa).has_any(_01a));
    EXPECT_TRUE(BitPatternPool(_01a).has_any(_01a));
    // 011 overlaps with 01a
    EXPECT_TRUE(BitPatternPool(_011).has_any(_01a));
    // overlap is symmetric
    EXPECT_TRUE(BitPatternPool(_01a).has_any(_011));
    EXPECT_FALSE(BitPatternPool(_111).has_any(_01a));
    // overlaps nothing
    EXPECT_FALSE(BitPatternPool(_011).has_any(_01x));
    EXPECT_FALSE(BitPatternPool(_011).has_any(_01z));
    EXPECT_FALSE(BitPatternPool(_aaa).has_any(_01x));

	EXPECT_TRUE(BitPatternPool(_aaa).has_all(_01a));
	EXPECT_TRUE(BitPatternPool(_01a).has_all(_01a));
    // 011 is covered by 01a
    EXPECT_TRUE(BitPatternPool(_01a).has_all(_011));
    // 01a is not covered by 011
    EXPECT_FALSE(BitPatternPool(_011).has_all(_01a));
    EXPECT_FALSE(BitPatternPool(_111).has_all(_01a));
    // trivially covered by any pool
    EXPECT_TRUE(BitPatternPool(_011).has_all(_01x));
    EXPECT_TRUE(BitPatternPool(_011).has_all(_01z));
    EXPECT_TRUE(BitPatternPool(_111).has_all(_01x));
}

namespace detail
{

// casez items 0, 0..01, 0..01?, ..., 1?..?.
std::vector<SigSpec> priority_items(int width)
{
	std::vector<SigSpec> items = {SigSpec(RTLIL::S0, width)};
	for (int one = 0; one < width; one++) {
		SigSpec item(RTLIL::Sa, width);
		for (int i = one; i < width; i++)
			item[i] = i == one ? RTLIL::S1 : RTLIL::S0;
		items.push_back(item);
	}
	return items;
}

// item x = (sel == x && data[x]), sel low or high
std::vector<SigSpec> mux_items(bool sel_low)
{
	int sel_lsb = sel_low ? 0 : 16;
	int data_lsb = sel_low ? 4 : 0;
	std::vector<SigSpec> items;
	for (int x = 0; x < 16; x++) {
		SigSpec item(RTLIL::Sa, 20);
		for (int i = 0; i < 4; i++)
			item[sel_lsb + i] = (x >> i) & 1 ? RTLIL::S1 : RTLIL::S0;
		item[data_lsb + x] = RTLIL::S1;
		items.push_back(item);
	}
	return items;
}

void expect_exact_mux(bool sel_low, int max_nodes)
{
	std::vector<SigSpec> items = mux_items(sel_low);
	BitPatternPool pool(20);
	pool.max_nodes = max_nodes;
	for (auto &item : items)
		EXPECT_TRUE(pool.take(item));
	EXPECT_FALSE(pool.gave_up);
	EXPECT_FALSE(pool.take(items[0]));
	EXPECT_FALSE(pool.has_any(items[0]));
	EXPECT_TRUE(pool.has_all(SigSpec(RTLIL::S0, 20)));
	EXPECT_FALSE(pool.empty());
}

} // namespace detail

TEST(BitpatternTest, priority_encoder)
{
	std::vector<SigSpec> items = detail::priority_items(64);
	for (int pass = 0; pass < 2; pass++) {
		BitPatternPool pool(64);
		for (auto &item : items) {
			EXPECT_FALSE(pool.empty());
			EXPECT_TRUE(pool.has_all(item));
			EXPECT_TRUE(pool.take(item));
			EXPECT_FALSE(pool.has_any(item));
			EXPECT_FALSE(pool.take(item));
		}
		EXPECT_TRUE(pool.empty());
		std::reverse(items.begin(), items.end());
	}
}

TEST(BitpatternTest, flips_bit_order)
{
	detail::expect_exact_mux(true, 128);
}

TEST(BitpatternTest, retries_msb_first)
{
	detail::expect_exact_mux(false, 128);
}

TEST(BitpatternTest, gives_up_conservatively)
{
	std::vector<SigSpec> items = detail::priority_items(4);
	BitPatternPool pool(4);
	pool.max_nodes = 4;
	EXPECT_TRUE(pool.take(items[0]));
	EXPECT_TRUE(pool.gave_up);
	EXPECT_TRUE(pool.take(items[0]));
	EXPECT_TRUE(pool.has_any(items[0]));
	EXPECT_FALSE(pool.has_all(items[1]));
	for (auto &item : items)
		pool.take(item);
	EXPECT_FALSE(pool.empty());
	EXPECT_TRUE(pool.take_all());
	EXPECT_TRUE(pool.empty());
	EXPECT_FALSE(pool.take(items[1]));
}

YOSYS_NAMESPACE_END
