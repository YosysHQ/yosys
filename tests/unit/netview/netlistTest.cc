#include <gtest/gtest.h>

#include "kernel/netlist.h"

YOSYS_NAMESPACE_BEGIN

TEST(IdMapTest, growsAndFallsBack)
{
	IdMap<int> map;
	map.fallback = -1;
	map[5] = 7;
	EXPECT_EQ(map.get(5), 7);
	EXPECT_EQ(map.get(2), 0);
	EXPECT_EQ(map.get(9), -1);
	EXPECT_EQ(map.data.size(), 6u);
	map.clear();
	EXPECT_EQ(map.get(5), -1);
}

YOSYS_NAMESPACE_END
