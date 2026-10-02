#include <gtest/gtest.h>

#include <chrono>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

TEST(TwineHashTest, Fragmentation)
{
	TwinePool pool;

	IdString flat = pool.add(std::string("$abcdefghij"));
	IdString base = pool.add(std::string("$abcde"));
	IdString split = pool.add(TwineSpec::Suffix{base, "fghij"});

	EXPECT_EQ(flat, split);
	EXPECT_EQ(pool[flat].hash(), TwineNode::extend_hash(0, "$abcdefghij"));
}

TEST(TwineHashTest, SplitPoints)
{
	const std::string content = "$0123456789abcdefghijklmnopqr";
	const uint64_t want = TwineNode::extend_hash(0, content);

	TwinePool pool;
	IdString first;
	for (size_t cut = 1; cut < content.size(); cut++) {
		IdString base = pool.add(content.substr(0, cut));
		IdString split = pool.add(TwineSpec::Suffix{base, content.substr(cut)});
		if (first == IdString::Null)
			first = split;
		EXPECT_EQ(split, first) << "split after " << cut;
		EXPECT_EQ(pool[split].hash(), want) << "split after " << cut;
	}
}

TEST(TwineHashTest, DistinctContent)
{
	TwinePool twines;

	std::set<uint64_t> seen;
	for (int i = 0; i < 4096; i++) {
		IdString ref = twines.add(stringf("$name%d", i));
		seen.insert(twines[ref].hash());
	}
	EXPECT_GT(seen.size(), 4000u);
}

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

	for (int i = 0; i < kNames; i++)
		ASSERT_EQ(pool.find(pool.str(refs[i])), refs[i]) << "at " << i;
	auto t2 = std::chrono::steady_clock::now();

	auto ms = [](auto a, auto b) {
		return std::chrono::duration_cast<std::chrono::microseconds>(b - a).count() / 1000.0;
	};
	RecordProperty("intern_ms", std::to_string(ms(t0, t1)));
	RecordProperty("find_ms", std::to_string(ms(t1, t2)));
	std::cerr << "[ BENCH    ] intern " << ms(t0, t1) << " ms, "
		  << kNames << " finds " << ms(t1, t2) << " ms\n";
}

}

YOSYS_NAMESPACE_END
