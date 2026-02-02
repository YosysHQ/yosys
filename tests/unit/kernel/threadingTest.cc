#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include "kernel/threading.h"

YOSYS_NAMESPACE_BEGIN

class ThreadingTest : public testing::Test {
protected:
	ThreadingTest() {
		if (log_files.empty())
			log_files.emplace_back(stdout);
	}
};

TEST_F(ThreadingTest, ParallelDispatchThreadPoolCreate) {
	// Test creating a pool with 0 threads (treated as 1)
	ParallelDispatchThreadPool pool0(0);
	EXPECT_EQ(pool0.num_threads(), 1);

	// Test creating a pool with 1 thread
	ParallelDispatchThreadPool pool1(1);
	EXPECT_EQ(pool1.num_threads(), 1);

	// Test creating a pool with 2 threads
	ParallelDispatchThreadPool pool2(2);
	// YOSYS_MAX_THREADS or system configuration could mean we
	// decide to only use one thread.
	EXPECT_GE(pool2.num_threads(), 1);
	EXPECT_LE(pool2.num_threads(), 2);
}

TEST_F(ThreadingTest, ParallelDispatchThreadPoolRunSimple) {
	ParallelDispatchThreadPool pool(2);

	std::atomic<int> counter{0};
	pool.run([&counter](const ParallelDispatchThreadPool::RunCtx &) {
		counter.fetch_add(1, std::memory_order_relaxed);
	});

	EXPECT_EQ(counter.load(), pool.num_threads());
}

TEST_F(ThreadingTest, ParallelDispatchThreadPoolRunMultiple) {
	ParallelDispatchThreadPool pool(2);

	std::atomic<int> counter{0};
	// Run multiple times to verify the pool can be reused
	for (int i = 0; i < 5; ++i)
		pool.run([&counter](const ParallelDispatchThreadPool::RunCtx &) {
			counter.fetch_add(1, std::memory_order_relaxed);
		});

	EXPECT_EQ(counter.load(), pool.num_threads() * 5);
}

TEST_F(ThreadingTest, ParallelDispatchThreadPoolRunCtxThreadNums) {
	ParallelDispatchThreadPool pool(4);

	std::vector<int> thread_nums(pool.num_threads(), -1);
	pool.run([&thread_nums](const ParallelDispatchThreadPool::RunCtx &ctx) {
		thread_nums[ctx.thread_num] = ctx.thread_num;
	});

	// Every thread should have recorded its own thread number
	for (int i = 0; i < pool.num_threads(); ++i)
		EXPECT_EQ(thread_nums[i], i);
}

TEST_F(ThreadingTest, ParallelDispatchThreadPoolItemRange) {
	ParallelDispatchThreadPool pool(3);

	const int num_items = 100;
	std::vector<std::atomic<int>> item_counts(num_items);
	for (std::atomic<int> &c : item_counts)
		c.store(0);

	pool.run([&item_counts](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(num_items))
			item_counts[i].fetch_add(1);
	});

	// Each item should have been processed exactly once
	for (int i = 0; i < num_items; ++i)
		EXPECT_EQ(item_counts[i].load(), 1);
}

TEST_F(ThreadingTest, ParallelDispatchThreadPoolSubpool) {
	ParallelDispatchThreadPool pool(4);

	// Subpool limited to 2 threads
	ParallelDispatchThreadPool::Subpool subpool(pool, 2);
	EXPECT_LE(subpool.num_threads(), 2);

	std::atomic<int> counter{0};
	subpool.run([&counter](const ParallelDispatchThreadPool::RunCtx &) {
		counter.fetch_add(1, std::memory_order_relaxed);
	});

	EXPECT_EQ(counter.load(), subpool.num_threads());
}

TEST_F(ThreadingTest, IntRangeIteration) {
	IntRange range{3, 7};
	std::vector<int> values;
	for (int i : range)
		values.push_back(i);
	EXPECT_THAT(values, testing::ElementsAre(3, 4, 5, 6));
}

TEST_F(ThreadingTest, IntRangeEmpty) {
	IntRange range{5, 5};
	for (int _ : range)
		FAIL();
}

TEST_F(ThreadingTest, ItemRangeForWorker) {
	EXPECT_EQ(item_range_for_worker(10, 0, 3), (IntRange{0, 4}));
	EXPECT_EQ(item_range_for_worker(10, 1, 3), (IntRange{4, 7}));
	EXPECT_EQ(item_range_for_worker(10, 2, 3), (IntRange{7, 10}));
}

TEST_F(ThreadingTest, ItemRangeForWorkerZeroThreads) {
	EXPECT_EQ(item_range_for_worker(10, 0, 0), (IntRange{0, 10}));
}

TEST_F(ThreadingTest, ShardedVectorBasic) {
	ParallelDispatchThreadPool pool(2);
	ShardedVector<int> vec(pool);
	pool.run([&vec](const ParallelDispatchThreadPool::RunCtx &ctx) {
		vec.insert(ctx, ctx.thread_num * 10);
		vec.insert(ctx, ctx.thread_num * 10 + 1);
	});

	EXPECT_FALSE(vec.empty());

	// Count elements
	std::vector<int> elements;
	for (int v : vec) {
		elements.push_back(v);
	}

	if (pool.num_threads() == 2)
		EXPECT_THAT(elements, testing::ElementsAre(0, 1, 10, 11));
	else
		EXPECT_THAT(elements, testing::ElementsAre(0, 1));
}

TEST_F(ThreadingTest, MonotonicFlagBasic) {
	MonotonicFlag flag;
	EXPECT_FALSE(flag.load());
	flag.set();
	EXPECT_TRUE(flag.load());
	flag.set();
	EXPECT_TRUE(flag.load());
}

TEST_F(ThreadingTest, MonotonicFlagSetAndReturnOld) {
	MonotonicFlag flag;
	EXPECT_FALSE(flag.set_and_return_old());
	EXPECT_TRUE(flag.load());
	EXPECT_TRUE(flag.set_and_return_old());
}

YOSYS_NAMESPACE_END
