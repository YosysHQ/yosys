#include <gtest/gtest.h>

#include <algorithm>
#include <chrono>
#include <string>
#include <vector>

#include "kernel/bitpattern.h"
#include "kernel/rtlil.h"
#include "perfHelpers.h"

YOSYS_NAMESPACE_BEGIN

namespace {

// Numerical Recipes LCG, top 24 bits; fixed seeds keep the shapes reproducible
uint32_t next_rand(uint32_t &state)
{
	state = state * 1664525u + 1013904223u;
	return state >> 8;
}

SigSpec const_pattern(int width, uint64_t value)
{
	return SigSpec(Const(value, width));
}

SigSpec wildcard_pattern(int width)
{
	return SigSpec(Const(std::vector<RTLIL::State>(width, RTLIL::State::Sa)));
}

SigSpec with_bits(SigSpec pat, int lsb, int count, uint64_t value)
{
	for (int i = 0; i < count; i++)
		pat[lsb + i] = (value >> i) & 1 ? RTLIL::State::S1 : RTLIL::State::S0;
	return pat;
}

struct PoolRun {
	int width;
	std::vector<SigSpec> items;
	bool query_empty_per_item;
	bool trailing_default;

	int live = 0;
	bool full = false;
	double take_ms = 0, empty_ms = 0;

	void execute()
	{
		BitPatternPool pool(width);
		auto t_take = std::chrono::steady_clock::duration::zero();
		auto t_empty = std::chrono::steady_clock::duration::zero();
		for (auto &item : items) {
			if (query_empty_per_item) {
				auto t0 = std::chrono::steady_clock::now();
				bool e = pool.empty();
				t_empty += std::chrono::steady_clock::now() - t0;
				if (e)
					break;
			}
			auto t0 = std::chrono::steady_clock::now();
			if (pool.take(item))
				live++;
			t_take += std::chrono::steady_clock::now() - t0;
		}
		if (trailing_default)
			pool.take_all();
		auto t0 = std::chrono::steady_clock::now();
		full = pool.empty();
		t_empty += std::chrono::steady_clock::now() - t0;
		take_ms = ms(t_take);
		empty_ms = ms(t_empty);
	}

	void report(const char *name)
	{
		printf("[ PERF     ] %s width=%d items=%zu live=%d full=%d take_ms=%.2f empty_ms=%.2f\n",
				name, width, items.size(), live, full, take_ms, empty_ms);
		fflush(stdout);
	}
};

// The items of a priority encoder can be listed either way round; the old pool
// was linear with the least specific item first and exponential the other way.
void run_both_orders(const char *name, int width, std::vector<SigSpec> items)
{
	PoolRun general_first{width, items, true, false};
	general_first.execute();
	general_first.report((std::string(name) + "_general_first").c_str());
	EXPECT_EQ(general_first.live, int(items.size()));
	EXPECT_TRUE(general_first.full);

	std::reverse(items.begin(), items.end());
	PoolRun specific_first{width, items, true, false};
	specific_first.execute();
	specific_first.report((std::string(name) + "_specific_first").c_str());
	EXPECT_EQ(specific_first.live, int(items.size()));
	EXPECT_TRUE(specific_first.full);
}

}

// casez (req)
//   16'b1???????????????: idx = 15;
//   16'b01??????????????: idx = 14;
//   ...
//   16'b0000000000000001: idx = 0;
//   16'b0:               valid = 0;
// endcase
TEST(BitpatternPerf, priority_encoder_msb_first)
{
	int width = env_int("YOSYS_BITPATTERN_PERF_WIDTH", 16);
	std::vector<SigSpec> items;
	for (int i = width - 1; i >= 0; i--)
		items.push_back(with_bits(wildcard_pattern(width), i, width - i, 1));
	items.push_back(const_pattern(width, 0));
	run_both_orders("priority_msb_first", width, items);
}

// casez (req)
//   16'b???????????????1: idx = 0;
//   16'b??????????????10: idx = 1;
//   ...
//   16'b1000000000000000: idx = 15;
//   16'b0:               valid = 0;
// endcase
TEST(BitpatternPerf, priority_encoder_lsb_first)
{
	int width = env_int("YOSYS_BITPATTERN_PERF_WIDTH", 16);
	std::vector<SigSpec> items;
	for (int i = 0; i < width; i++)
		items.push_back(with_bits(wildcard_pattern(width), 0, i + 1, uint64_t(1) << i));
	items.push_back(const_pattern(width, 0));
	run_both_orders("priority_lsb_first", width, items);
}

// casez ({n7, n6, ..., n0})
//   32'h???????F: hit = 0;
//   32'h??????F?: hit = 1;
//   ...
//   32'hF???????: hit = 7;
// endcase
TEST(BitpatternPerf, disjoint_fields)
{
	int field = env_int("YOSYS_BITPATTERN_PERF_FIELD", 4);
	int fields = env_int("YOSYS_BITPATTERN_PERF_FIELDS", 8);
	int width = field * fields;
	PoolRun run{width, {}, true, false};
	for (int f = 0; f < fields; f++)
		run.items.push_back(with_bits(wildcard_pattern(width), f * field, field, (uint64_t(1) << field) - 1));
	run.execute();
	run.report("disjoint_fields");
	EXPECT_EQ(run.live, fields);
	EXPECT_FALSE(run.full);
}

// case (addr)
//   9'd291: data = ...;
//   9'd17:   data = ...;
//   ...      // all possible values
// endcase
TEST(BitpatternPerf, dense_table)
{
	int width = env_int("YOSYS_BITPATTERN_PERF_TABLE_WIDTH", 9);
	PoolRun run{width, {}, true, false};
	uint32_t rng = 7;
	std::vector<uint64_t> values(size_t(1) << width);
	for (size_t i = 0; i < values.size(); i++)
		values[i] = i;
	for (size_t i = values.size(); i > 1; i--)
		std::swap(values[i - 1], values[next_rand(rng) % i]);
	for (uint64_t v : values)
		run.items.push_back(const_pattern(width, v));
	run.execute();
	run.report("dense_table");
	EXPECT_EQ(run.live, int(values.size()));
	EXPECT_TRUE(run.full);
}

// casez (addr)
//   9'b11???????: data = ...;
//   9'b???????00: data = ...;
//   9'd0:         data = ...;
//   9'd1:         data = ...;
//   ...            // all possible values, many now unreachable
// endcase
TEST(BitpatternPerf, dense_table_with_wildcard_items)
{
	int width = env_int("YOSYS_BITPATTERN_PERF_TABLE_WIDTH", 9);
	PoolRun run{width, {}, true, false};
	run.items.push_back(with_bits(wildcard_pattern(width), width - 2, 2, 3));
	run.items.push_back(with_bits(wildcard_pattern(width), 0, 2, 0));
	for (uint64_t v = 0; v < (uint64_t(1) << width); v++)
		run.items.push_back(const_pattern(width, v));
	run.execute();
	run.report("dense_table_wildcards");
	EXPECT_TRUE(run.full);
}

// casez (insn)   // 32 bits, RISC-V-like: opcode in [6:0], funct3 in [14:12],
//                // funct7 in [31:25] for half the items, a few fully specified
//   32'b???????_?????_?????_000_?????_0110011: op = ADD;
//   32'b0100000_?????_?????_000_?????_0110011: op = SUB;
//   32'b????????????_?????_010_?????_0000011: op = LW;
//   ...
//   default: op = ILLEGAL;
// endcase
TEST(BitpatternPerf, decoder)
{
	int width = env_int("YOSYS_BITPATTERN_PERF_WIDTH", 32);
	int count = env_int("YOSYS_BITPATTERN_PERF_DECODER_ITEMS", 12);
	PoolRun run{width, {}, true, true};
	uint32_t rng = 3;
	for (int i = 0; i < count; i++) {
		SigSpec pat = with_bits(wildcard_pattern(width), 0, 7, next_rand(rng) % 128);
		pat = with_bits(pat, 12, 3, next_rand(rng) % 8);
		if (next_rand(rng) % 2)
			pat = with_bits(pat, 25, 7, next_rand(rng) % 128);
		if (next_rand(rng) % 8 == 0)
			pat = with_bits(pat, 7, 18, next_rand(rng));
		run.items.push_back(pat);
	}
	run.execute();
	run.report("decoder");
	EXPECT_TRUE(run.full);
}

YOSYS_NAMESPACE_END
