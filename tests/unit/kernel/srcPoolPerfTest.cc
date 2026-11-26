#include <gtest/gtest.h>

#include <vector>

#include "kernel/srcpool.h"
#include "kernel/yosys.h"
#include "perfHelpers.h"

YOSYS_NAMESPACE_BEGIN

namespace {

uint32_t next_rand(uint32_t &state)
{
	state = state * 1664525u + 1013904223u;
	return state >> 8;
}

struct PhaseTimer {
	std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
	std::chrono::steady_clock::time_point start = begin;

	void stop(const char *name, size_t ops)
	{
		auto now = std::chrono::steady_clock::now();
		double phase_ms = ms(now - start);
		printf("[ PERF     ] %-14s ops=%-9zu total_ms=%-8.2f ns_per_op=%.1f\n",
				name, ops, phase_ms, 1e6 * phase_ms / (double)ops);
		start = now;
	}
};

}

TEST(SrcPoolPerf, opt_pass_merges)
{
	int location_count = env_int("YOSYS_SRCPOOL_PERF_LOCS", 20000);
	int rounds = env_int("YOSYS_SRCPOOL_PERF_ROUNDS", 5);
	int chain_length = env_int("YOSYS_SRCPOOL_PERF_CHAIN", 2000);
	const int file_count = 50;
	const int set_size = 16;

	ASSERT_GE(location_count, set_size);
	ASSERT_LE(chain_length, location_count);

	TwinePool twines = {};
	SrcPool srcs(twines);
	uint32_t rng = 12345;

	std::vector<IdString> files = {};
	for (int i = 0; i < file_count; i++)
		files.push_back(srcs.file(stringf("rtl/perf_block_%d.v", i)));

	std::vector<SrcRef> singles = {};
	for (int i = 0; i < location_count; i++) {
		int line = i / file_count + 1;
		singles.push_back(srcs.add(srcs.location(files[i % file_count], line, 5, line, 23)));
	}
	for (size_t i = singles.size(); i > 1; i--)
		std::swap(singles[i - 1], singles[next_rand(rng) % i]);

	int big_count = location_count / set_size;
	std::vector<SrcRef> bigs = {};
	std::vector<SrcRef> big_members = {};
	for (int i = 0; i < big_count; i++) {
		std::vector<SrcRef> parts = {};
		for (int j = 0; j < set_size; j++)
			parts.push_back(singles[next_rand(rng) % singles.size()]);
		bigs.push_back(srcs.merge(parts));
		big_members.push_back(parts[next_rand(rng) % parts.size()]);
	}

	std::vector<int> pair_a = {};
	std::vector<int> pair_b = {};
	for (int i = 0; i < location_count; i++) {
		pair_a.push_back(next_rand(rng) % location_count);
		pair_b.push_back(next_rand(rng) % location_count);
	}

	std::vector<int> big_a = {};
	std::vector<int> big_b = {};
	for (int i = 0; i < big_count; i++) {
		big_a.push_back(next_rand(rng) % big_count);
		big_b.push_back(next_rand(rng) % big_count);
	}

	size_t checksum = 0;
	size_t mismatches = 0;
	PhaseTimer timer = {};

	for (int round = 0; round < rounds; round++)
		for (SrcRef s : singles) {
			mismatches += !(srcs.merge(SrcRef::Null, s) == s);
			mismatches += !(srcs.merge(s, s) == s);
		}
	timer.stop("early_out", singles.size() * 2 * rounds);

	for (int round = 0; round < rounds; round++)
		for (int i = 0; i < big_count; i++) {
			mismatches += !(srcs.merge(bigs[i], big_members[i]) == bigs[i]);
			mismatches += !(srcs.merge(big_members[i], bigs[i]) == bigs[i]);
		}
	timer.stop("subset", (size_t)big_count * 2 * rounds);

	for (int i = 0; i < location_count; i++)
		checksum += srcs.locations(srcs.merge(singles[pair_a[i]], singles[pair_b[i]])).size();
	timer.stop("union_new", location_count);

	for (int round = 0; round < rounds; round++)
		for (int i = 0; i < location_count; i++)
			checksum += srcs.locations(srcs.merge(singles[pair_b[i]], singles[pair_a[i]])).size();
	timer.stop("union_existing", (size_t)location_count * rounds);

	for (int round = 0; round < rounds; round++)
		for (int i = 0; i < big_count; i++)
			checksum += srcs.locations(srcs.merge(bigs[big_a[i]], bigs[big_b[i]])).size();
	timer.stop("big_union", (size_t)big_count * rounds);

	SrcRef acc = SrcRef::Null;
	for (int i = 0; i < chain_length; i++)
		acc = srcs.merge(acc, singles[i]);
	timer.stop("chain", chain_length);

	EXPECT_EQ(mismatches, 0u);
	EXPECT_EQ(srcs.locations(acc).size(), (size_t)chain_length);

	printf("[ PERF     ] locs=%d rounds=%d chain=%d pool_size=%zu checksum=%zu total_ms=%.1f peak_rss_mb=%.1f\n",
			location_count, rounds, chain_length, srcs.size(), checksum,
			ms(std::chrono::steady_clock::now() - timer.begin), mb(peak_rss_bytes()));
	fflush(stdout);
}

YOSYS_NAMESPACE_END
