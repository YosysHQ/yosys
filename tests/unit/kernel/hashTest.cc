#include <gtest/gtest.h>
#include "kernel/yosys_common.h"

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
	for (int i = 0; i < 10000; ++i) {
		for (int j = i + 1; j < 10000; ++j) {
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
	EXPECT_LT(collisions, 1000000);
}

YOSYS_NAMESPACE_END
