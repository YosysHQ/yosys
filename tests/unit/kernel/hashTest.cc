#include <gtest/gtest.h>
#include "kernel/yosys_common.h"

#include <chrono>
#include <cstdlib>
#include <iostream>
#include <string>
#include <unordered_set>

YOSYS_NAMESPACE_BEGIN

static Hasher hash(int x)
{
	Hasher h;
	h.eat(x);
	return h;
}

TEST(CommutativeTest, basic)
{
	hashlib::commutative_hash comm1;
	comm1.eat(hash(1));
	comm1.eat(hash(2));
	hashlib::commutative_hash comm2;
	comm2.eat(hash(2));
	comm2.eat(hash(1));
	EXPECT_EQ(comm1.hash_into(Hasher()).yield(), comm2.hash_into(Hasher()).yield());
}

TEST(PoolHashTest, collisions)
{
	uint64_t collisions = 0;
	std::unordered_set<Hasher::hash_t> hashes;
	for (int i = 0; i < 1000; ++i) {
		for (int j = i + 1; j < 1000; ++j) {
			pool<int> p1;
			p1.insert(i);
			p1.insert(j);
			auto h = p1.hash_into(Hasher()).yield();
			if (!hashes.insert(h).second) {
				++collisions;
			}
		}
	}
	std::cout << "pool<int> collisions: " << collisions << std::endl;
	EXPECT_LT(collisions, 10'000);
}

TEST(PoolHashTest, subset_collisions)
{
	uint64_t collisions = 0;
	std::unordered_set<Hasher::hash_t> hashes;
	for (int i = 0; i < 1000 * 1000; ++i) {

		pool<int> p1;
		for (int b = 0; i >> b; ++b) {
			if ((i >> b) & 1) {
				p1.insert(b);
			}
		}
		auto h = p1.hash_into(Hasher()).yield();
		if (!hashes.insert(h).second) {
			++collisions;
		}

	}
	std::cout << "pool<int> subset collisions: " << collisions << std::endl;
	EXPECT_LT(collisions, 100);
}

static bool run_hash_benchmarks()
{
	const char *env = getenv("YOSYS_HASH_BENCH");
	return env != nullptr && std::string(env) != "0";
}

template<typename F>
static double time_ns_per_op(int ops, F &&f)
{
	auto start = std::chrono::steady_clock::now();
	f();
	auto stop = std::chrono::steady_clock::now();
	return std::chrono::duration<double, std::nano>(stop - start).count() / ops;
}

TEST(HashBenchmarkTest, dict_int_lookup)
{
	if (!run_hash_benchmarks())
		GTEST_SKIP() << "set YOSYS_HASH_BENCH=1 to run hash microbenchmarks";

	const int keys = 200000;
	const int probes = 2000000;
	dict<int, int> db;
	db.reserve(keys);
	for (int i = 0; i < keys; ++i)
		db[i] = i * 3;

	volatile int sink = 0;
	double ns_per_op = time_ns_per_op(probes, [&] {
		for (int i = 0; i < probes; ++i)
			sink += db.at((i * 2654435761u) % keys);
	});
	std::cout << "dict<int,int> lookup ns/op: " << ns_per_op << std::endl;
	int observed = sink;
	EXPECT_NE(observed, 0);
}

TEST(HashBenchmarkTest, pool_int_insert_count_erase)
{
	if (!run_hash_benchmarks())
		GTEST_SKIP() << "set YOSYS_HASH_BENCH=1 to run hash microbenchmarks";

	const int keys = 200000;
	pool<int> db;
	db.reserve(keys);
	volatile int sink = 0;

	double insert_ns = time_ns_per_op(keys, [&] {
		for (int i = 0; i < keys; ++i)
			db.insert(i);
	});
	double count_ns = time_ns_per_op(keys, [&] {
		for (int i = 0; i < keys; ++i)
			sink += db.count((i * 2654435761u) % keys);
	});
	double erase_ns = time_ns_per_op(keys, [&] {
		for (int i = 0; i < keys; ++i)
			db.erase(i);
	});

	std::cout << "pool<int> insert ns/op: " << insert_ns << std::endl;
	std::cout << "pool<int> count ns/op: " << count_ns << std::endl;
	std::cout << "pool<int> erase ns/op: " << erase_ns << std::endl;
	int observed = sink;
	EXPECT_EQ(observed, keys);
}

YOSYS_NAMESPACE_END
