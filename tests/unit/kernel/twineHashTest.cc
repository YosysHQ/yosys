#include <gtest/gtest.h>

#include <chrono>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

// A name reached through a suffix chain must hash the same as the identical
// name interned as a single leaf, otherwise TwineSearch misses it.
TEST(TwineHashTest, Fragmentation)
{
	TwinePool pool;
	DeepTwineHash hash{&pool};

	IdString flat = pool.add(std::string("$abcdefghij"));
	IdString base = pool.add(std::string("$abcde"));
	IdString split = pool.add(TwineSpec::Suffix{base, "fghij"});

	EXPECT_EQ(hash(flat.untag()), hash(split.untag()));
	EXPECT_EQ(hash(flat.untag()), hash(std::string_view("$abcdefghij")));
}

// The 8-byte buffering must not leak fragment boundaries at any offset.
TEST(TwineHashTest, SplitPoints)
{
	const std::string content = "$0123456789abcdefghijklmnopqr";

	TwinePool pool;
	DeepTwineHash hash{&pool};
	const size_t want = hash(std::string_view(content));

	for (size_t cut = 1; cut < content.size(); cut++) {
		IdString base = pool.add(content.substr(0, cut));
		IdString split = pool.add(TwineSpec::Suffix{base, content.substr(cut)});
		EXPECT_EQ(hash(split.untag()), want) << "split after " << cut;
	}
}

TEST(TwineHashTest, DistinctContent)
{
	TwinePool twines;
	DeepTwineHash hash{&twines};

	std::set<size_t> seen;
	for (int i = 0; i < 4096; i++) {
		IdString ref = twines.add(stringf("$name%d", i));
		seen.insert(hash(ref.untag()));
	}
	EXPECT_GT(seen.size(), 4000u);
}

// Not an assertion of speed, but a harness: reports how long interning and
// rehashing a large pool takes so the cost of the hashing path is visible.
TEST(TwineHashTest, BenchmarkIntern)
{
	constexpr int kNames = 40000;

	TwinePool pool;
	auto t0 = std::chrono::steady_clock::now();
	IdString prefix = pool.add(std::string("$bench"));
	std::vector<IdString> refs;
	refs.reserve(kNames);
	for (int i = 0; i < kNames; i++)
		refs.push_back(pool.add(TwineSpec::Suffix{prefix, stringf("$%d", i)}));
	auto t1 = std::chrono::steady_clock::now();

	TwineSearch search(&pool);
	auto t2 = std::chrono::steady_clock::now();

	for (int i = 0; i < kNames; i++)
		ASSERT_EQ(search.find(pool.str(refs[i])), refs[i]) << "at " << i;
	auto t3 = std::chrono::steady_clock::now();

	auto ms = [](auto a, auto b) {
		return std::chrono::duration_cast<std::chrono::microseconds>(b - a).count() / 1000.0;
	};
	RecordProperty("intern_ms", std::to_string(ms(t0, t1)));
	RecordProperty("search_build_ms", std::to_string(ms(t1, t2)));
	RecordProperty("search_find_ms", std::to_string(ms(t2, t3)));
	std::cerr << "[ BENCH    ] intern " << ms(t0, t1) << " ms, TwineSearch build "
		  << ms(t1, t2) << " ms, " << kNames << " finds " << ms(t2, t3) << " ms\n";
}

} // namespace

YOSYS_NAMESPACE_END
