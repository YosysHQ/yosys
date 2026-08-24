#include <gtest/gtest.h>

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

#include <sys/resource.h>

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

int env_int(const char *name, int fallback)
{
	const char *value = getenv(name);
	if (value == nullptr || *value == 0)
		return fallback;
	return atoi(value);
}

size_t peak_rss_bytes()
{
	struct rusage ru;
	if (getrusage(RUSAGE_SELF, &ru) != 0)
		return 0;
	return (size_t)ru.ru_maxrss * 1024;
}

double ms(std::chrono::steady_clock::duration d)
{
	return std::chrono::duration<double, std::milli>(d).count();
}

uint32_t next_rand(uint32_t &state)
{
	state = state * 1664525u + 1013904223u;
	return state >> 8;
}

std::string padded(const char *stem, int index, int extra_chars)
{
	std::string name = stringf("\\%s_%d", stem, index);
	name += std::string(extra_chars, 'n');
	return name;
}

}

TEST(SigBitPerf, hash_and_sigmap_stress)
{
	int wire_count = env_int("YOSYS_SIGBIT_PERF_WIRES", 4000);
	int wire_width = env_int("YOSYS_SIGBIT_PERF_WIDTH", 16);
	int alias_every = env_int("YOSYS_SIGBIT_PERF_ALIAS", 4);
	int probe_rounds = env_int("YOSYS_SIGBIT_PERF_ROUNDS", 20);
	int name_padding = env_int("YOSYS_SIGBIT_PERF_NAMEPAD", 24);

	ASSERT_GE(wire_count, 2);
	ASSERT_GE(wire_width, 1);
	ASSERT_GE(alias_every, 2);
	ASSERT_GE(probe_rounds, 1);

	RTLIL::Design *design = new RTLIL::Design;
	RTLIL::Module *module = design->addModule(padded("sigbit_perf_module", 0, name_padding));

	std::vector<RTLIL::Wire *> wires;
	wires.reserve(wire_count);
	for (int i = 0; i < wire_count; i++)
		wires.push_back(module->addWire(padded("sigbit_perf_wire", i, name_padding), wire_width));

	int aliased = 0;
	for (int i = alias_every; i < wire_count; i += alias_every) {
		module->connect(RTLIL::SigSpec(wires[i]), RTLIL::SigSpec(wires[i - 1]));
		aliased++;
	}

	std::vector<RTLIL::SigBit> bits;
	bits.reserve((size_t)wire_count * wire_width);
	for (RTLIL::Wire *wire : wires)
		for (int i = 0; i < wire_width; i++)
			bits.push_back(RTLIL::SigBit(wire, i));

	uint32_t rng = 12345;
	std::vector<RTLIL::SigBit> probes = bits;
	for (size_t i = probes.size(); i > 1; i--)
		std::swap(probes[i - 1], probes[next_rand(rng) % i]);

	size_t rss_before = peak_rss_bytes();

	auto t0 = std::chrono::steady_clock::now();
	SigMap sigmap(module);
	auto t1 = std::chrono::steady_clock::now();

	size_t sigmap_checksum = 0;
	for (int round = 0; round < probe_rounds; round++)
		for (const RTLIL::SigBit &bit : probes)
			sigmap_checksum += sigmap(bit).offset;
	auto t2 = std::chrono::steady_clock::now();

	pool<RTLIL::SigBit> seen;
	for (int round = 0; round < probe_rounds; round++) {
		seen.clear();
		for (const RTLIL::SigBit &bit : probes)
			seen.insert(bit);
	}
	auto t3 = std::chrono::steady_clock::now();

	size_t hits = 0;
	for (int round = 0; round < probe_rounds; round++)
		for (const RTLIL::SigBit &bit : probes)
			hits += seen.count(bit);
	auto t4 = std::chrono::steady_clock::now();

	dict<RTLIL::SigBit, int> owner;
	for (int round = 0; round < probe_rounds; round++) {
		owner.clear();
		int n = 0;
		for (const RTLIL::SigBit &bit : probes)
			owner[bit] = n++;
	}
	auto t5 = std::chrono::steady_clock::now();

	size_t dict_checksum = 0;
	for (int round = 0; round < probe_rounds; round++)
		for (const RTLIL::SigBit &bit : probes)
			dict_checksum += owner.at(bit);
	auto t6 = std::chrono::steady_clock::now();

	size_t bit_count = probes.size();
	size_t ops = bit_count * (size_t)probe_rounds;

	EXPECT_EQ(seen.size(), bit_count);
	EXPECT_EQ(owner.size(), bit_count);
	EXPECT_EQ(hits, ops);

	printf("[ PERF     ] wires=%d width=%d alias_every=%d aliased=%d namepad=%d rounds=%d\n",
			wire_count, wire_width, alias_every, aliased, name_padding, probe_rounds);
	printf("[ PERF     ] bits=%zu ops_per_phase=%zu checksums=%zu,%zu\n",
			bit_count, ops, sigmap_checksum, dict_checksum);
	printf("[ PERF     ] sigmap_build_ms=%.1f sigmap_lookup_ns=%.2f\n",
			ms(t1 - t0), 1e6 * ms(t2 - t1) / (double)ops);
	printf("[ PERF     ] pool_insert_ns=%.2f pool_lookup_ns=%.2f\n",
			1e6 * ms(t3 - t2) / (double)ops, 1e6 * ms(t4 - t3) / (double)ops);
	printf("[ PERF     ] dict_insert_ns=%.2f dict_lookup_ns=%.2f\n",
			1e6 * ms(t5 - t4) / (double)ops, 1e6 * ms(t6 - t5) / (double)ops);
	printf("[ PERF     ] total_ms=%.1f peak_rss_mb=%.1f rss_before_mb=%.1f\n",
			ms(t6 - t0), peak_rss_bytes() / 1048576.0, rss_before / 1048576.0);
	fflush(stdout);

	delete design;
}

YOSYS_NAMESPACE_END
