#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

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

TEST(BitpatternTest, take)
{
	SigSpec _aa = {RTLIL::Sa, RTLIL::Sa};
	SigSpec _0a = {RTLIL::S0, RTLIL::Sa};
	SigSpec _a1 = {RTLIL::Sa, RTLIL::S1};
	SigSpec _10 = {RTLIL::S1, RTLIL::S0};
	SigSpec _11 = {RTLIL::S1, RTLIL::S1};

	BitPatternPool pool(_aa);
	EXPECT_FALSE(pool.empty());
	EXPECT_TRUE(pool.take(_0a));
	EXPECT_FALSE(pool.take(_0a));
	EXPECT_TRUE(pool.has_all(_10));
	EXPECT_TRUE(pool.take(_a1));
	EXPECT_FALSE(pool.has_all(_a1));
	EXPECT_FALSE(pool.take(_11));
	EXPECT_FALSE(pool.empty());
	EXPECT_TRUE(pool.has_any(_10));
	EXPECT_TRUE(pool.take(_10));
	EXPECT_TRUE(pool.empty());
	EXPECT_FALSE(pool.take_all());

	BitPatternPool restricted(_0a);
	EXPECT_FALSE(restricted.has_any(_10));
	EXPECT_FALSE(restricted.has_all(_a1));
	EXPECT_TRUE(restricted.take(_a1));
	EXPECT_FALSE(restricted.empty());
	EXPECT_TRUE(restricted.take_all());
	EXPECT_TRUE(restricted.empty());
	EXPECT_FALSE(restricted.has_any(_0a));

	BitPatternPool nothing{SigSpec()};
	EXPECT_TRUE(nothing.empty());
	EXPECT_FALSE(nothing.take(SigSpec()));
	EXPECT_FALSE(nothing.take_all());
}

namespace {

struct ReferencePool
{
	int width;
	std::vector<bool> uncovered;

	ReferencePool(const SigSpec &sig) : width(sig.size()), uncovered(size_t(1) << width, true)
	{
		for (size_t v = 0; v < uncovered.size(); v++)
			for (int i = 0; i < width; i++)
				if (sig[i].wire == nullptr && sig[i].data <= RTLIL::State::S1 &&
						(sig[i].data == RTLIL::State::S1) != bool((v >> i) & 1))
					uncovered[v] = false;
	}

	static bool matches(const SigSpec &sig, size_t v)
	{
		for (int i = 0; i < sig.size(); i++) {
			RTLIL::State s = sig[i].data;
			if (s == RTLIL::State::Sx || s == RTLIL::State::Sz)
				return false;
			if (s <= RTLIL::State::S1 && (s == RTLIL::State::S1) != bool((v >> i) & 1))
				return false;
		}
		return true;
	}

	bool has_any(const SigSpec &sig)
	{
		for (size_t v = 0; v < uncovered.size(); v++)
			if (uncovered[v] && matches(sig, v))
				return true;
		return false;
	}

	bool has_all(const SigSpec &sig)
	{
		for (size_t v = 0; v < uncovered.size(); v++)
			if (!uncovered[v] && matches(sig, v))
				return false;
		return true;
	}

	bool take(const SigSpec &sig)
	{
		bool result = has_any(sig);
		for (size_t v = 0; v < uncovered.size(); v++)
			if (matches(sig, v))
				uncovered[v] = false;
		return result;
	}

	bool empty()
	{
		for (bool u : uncovered)
			if (u)
				return false;
		return true;
	}

	bool take_all()
	{
		bool result = !empty();
		std::fill(uncovered.begin(), uncovered.end(), false);
		return result;
	}
};

// Numerical Recipes LCG, top 24 bits; fixed seeds keep the shapes reproducible
uint32_t next_rand(uint32_t &state)
{
	state = state * 1664525u + 1013904223u;
	return state >> 8;
}

SigSpec random_pattern(uint32_t &rng, int width, int wildcard_percent, int xz_percent)
{
	std::vector<RTLIL::State> bits(width);
	for (int i = 0; i < width; i++) {
		uint32_t r = next_rand(rng) % 100;
		if (r < uint32_t(xz_percent))
			bits[i] = next_rand(rng) & 1 ? RTLIL::State::Sx : RTLIL::State::Sz;
		else if (r < uint32_t(xz_percent + wildcard_percent))
			bits[i] = RTLIL::State::Sa;
		else
			bits[i] = next_rand(rng) & 1 ? RTLIL::State::S1 : RTLIL::State::S0;
	}
	return SigSpec(Const(bits));
}

}

TEST(BitpatternTest, differential)
{
	uint32_t rng = 1;
	for (int round = 0; round < 400; round++) {
		int width = 1 + next_rand(rng) % 10;
		int wildcard_percent = (next_rand(rng) % 3) * 40;
		int xz_percent = next_rand(rng) % 4 == 0 ? 3 : 0;
		SigSpec universe = random_pattern(rng, width, next_rand(rng) % 2 ? 100 : 60, 0);

		BitPatternPool pool(universe);
		ReferencePool ref(universe);
		int steps = 2 + next_rand(rng) % (3 * width + 1);
		for (int step = 0; step < steps; step++) {
			SigSpec pat = random_pattern(rng, width, wildcard_percent, xz_percent);
			std::string what = log_signal(pat);
			switch (next_rand(rng) % 6) {
			case 0:
				ASSERT_EQ(pool.has_any(pat), ref.has_any(pat)) << "has_any " << what << " universe " << log_signal(universe);
				break;
			case 1:
				ASSERT_EQ(pool.has_all(pat), ref.has_all(pat)) << "has_all " << what << " universe " << log_signal(universe);
				break;
			case 2:
				ASSERT_EQ(pool.empty(), ref.empty()) << "empty, universe " << log_signal(universe);
				break;
			case 3:
				if (next_rand(rng) % 8 == 0) {
					ASSERT_EQ(pool.take_all(), ref.take_all()) << "take_all, universe " << log_signal(universe);
					break;
				}
				[[fallthrough]];
			default:
				ASSERT_EQ(pool.take(pat), ref.take(pat)) << "take " << what << " universe " << log_signal(universe);
				break;
			}
		}
		ASSERT_EQ(pool.empty(), ref.empty()) << "final empty, universe " << log_signal(universe);
	}
}

YOSYS_NAMESPACE_END
