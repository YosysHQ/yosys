#include <gtest/gtest.h>

#include <chrono>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

std::vector<IdString> bench_refs(TwinePool &twines, int count)
{
	IdString prefix = twines.add(std::string("$sortbench"));
	std::vector<IdString> refs;
	refs.reserve(count);
	for (int i = 0; i < count; i++)
		refs.push_back(twines.add(Twine::Suffix{prefix, stringf("$%08d", (count - i) * 7919 % count)}));
	return refs;
}

TEST(TwineSortTest, RenderedOrder)
{
	TwinePool twines;
	std::vector<IdString> refs = {
		twines.add(std::string("$c")),
		twines.add(std::string("$a")),
		twines.add(std::string("$b")),
	};
	std::sort(refs.begin(), refs.end(), RTLIL::sort_by_id_str(twines));
	EXPECT_EQ(twines.str(refs[0]), "$a");
	EXPECT_EQ(twines.str(refs[1]), "$b");
	EXPECT_EQ(twines.str(refs[2]), "$c");
}

TEST(TwineSortTest, PublicOrder)
{
	TwinePool twines;
	IdString pub = twines.add(std::string("\\same"));
	IdString priv = pub.tag(false);

	ASSERT_EQ(twines.str(pub), "\\same");
	ASSERT_EQ(twines.str(priv), "same");

	RTLIL::sort_by_id_str less(twines);
	EXPECT_NE(less(pub, priv), less(priv, pub));
	EXPECT_TRUE(less(pub, priv));
}

TEST(TwineSortTest, WeakOrdering)
{
	TwinePool twines;
	std::vector<IdString> refs = bench_refs(twines, 500);
	RTLIL::sort_by_id_str less(twines);
	std::sort(refs.begin(), refs.end(), less);
	for (size_t i = 1; i < refs.size(); i++)
		ASSERT_FALSE(less(refs[i], refs[i - 1])) << "at " << i;
}

TEST(TwineSortTest, GeneralWalk)
{
	TwinePool twines;
	std::vector<IdString> refs;

	IdString a = twines.add(std::string("$alpha"));
	IdString b = twines.add(std::string("\\alpha"));
	IdString c = twines.add(std::string("$alphabet"));
	refs.insert(refs.end(), {a, b, c});

	IdString deep = a;
	for (int i = 0; i < 12; i++) {
		deep = twines.add(Twine::Suffix{deep, stringf(".lvl%d", i)});
		refs.push_back(deep);
		refs.push_back(deep.tag(true));
	}

	IdString other = twines.add(std::string("$alpha."));
	for (int i = 0; i < 12; i++) {
		other = twines.add(Twine::Suffix{other, stringf("lvl%d.", i)});
		refs.push_back(other);
	}

	RTLIL::sort_by_id_str less(twines);
	for (IdString x : refs)
		for (IdString y : refs) {
			bool want = twines.str(x) < twines.str(y);
			EXPECT_EQ(less(x, y), want)
				<< twines.str(x) << " vs " << twines.str(y);
		}
}

TEST(TwineSortTest, BenchmarkSort)
{
	constexpr int kNames = 50000;

	TwinePool twines;
	std::vector<IdString> refs = bench_refs(twines, kNames);

	auto t0 = std::chrono::steady_clock::now();
	std::sort(refs.begin(), refs.end(), RTLIL::sort_by_id_str(twines));
	auto t1 = std::chrono::steady_clock::now();

	size_t flattens = 0;
	std::vector<IdString> naive = bench_refs(twines, kNames);
	auto t2 = std::chrono::steady_clock::now();
	std::sort(naive.begin(), naive.end(), [&](IdString a, IdString b) {
		flattens += 2;
		return twines.str(a) < twines.str(b);
	});
	auto t3 = std::chrono::steady_clock::now();

	auto ms = [](auto a, auto b) {
		return std::chrono::duration_cast<std::chrono::microseconds>(b - a).count() / 1000.0;
	};
	std::cerr << "[ BENCH    ] " << kNames << " refs: walked " << ms(t0, t1)
		  << " ms vs per-comparison " << ms(t2, t3) << " ms ("
		  << flattens << " flattens vs " << kNames << ")\n";
	RecordProperty("walked_ms", std::to_string(ms(t0, t1)));
	RecordProperty("naive_ms", std::to_string(ms(t2, t3)));

	EXPECT_LT(ms(t0, t1), ms(t2, t3));
}

} // namespace

YOSYS_NAMESPACE_END
