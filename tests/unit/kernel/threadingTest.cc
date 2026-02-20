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

TEST_F(ThreadingTest, ConcurrentQueueBasic) {
	ConcurrentQueue<int> queue;
	queue.push_back(1);
	queue.push_back(2);
	queue.push_back(3);

	auto v1 = queue.pop_front();
	auto v2 = queue.pop_front();
	auto v3 = queue.pop_front();

	ASSERT_TRUE(v1.has_value());
	ASSERT_TRUE(v2.has_value());
	ASSERT_TRUE(v3.has_value());
	EXPECT_EQ(*v1, 1);
	EXPECT_EQ(*v2, 2);
	EXPECT_EQ(*v3, 3);
}

TEST_F(ThreadingTest, ConcurrentQueueTryPopEmpty) {
	ConcurrentQueue<int> queue;
	auto v = queue.try_pop_front();
	EXPECT_FALSE(v.has_value());
}

TEST_F(ThreadingTest, ConcurrentQueueClose) {
	ConcurrentQueue<int> queue;
	queue.push_back(42);
	queue.close();

	// Can still pop existing elements
	auto v1 = queue.pop_front();
	ASSERT_TRUE(v1.has_value());
	EXPECT_EQ(*v1, 42);

	// After close and empty, pop_front returns nullopt
	auto v2 = queue.pop_front();
	EXPECT_FALSE(v2.has_value());
}

TEST_F(ThreadingTest, ThreadPoolCreate) {
	// pool_size of 0 means no worker threads
	ThreadPool pool0(0, [](int) {});
	EXPECT_EQ(pool0.num_threads(), 0);

	// pool_size of 1 means 1 worker thread
	std::atomic<int> counter{0};
	{
		ThreadPool pool1(1, [&counter](int thread_num) {
			EXPECT_EQ(thread_num, 0);
			counter.fetch_add(1);
		});
	}
#ifdef YOSYS_ENABLE_THREADS
	EXPECT_EQ(counter.load(), 1);
#else
	EXPECT_EQ(counter.load(), 0);
#endif
}

TEST_F(ThreadingTest, ThreadPoolMultipleThreads) {
	std::atomic<int> counter{0};
	{
		ThreadPool pool(2, [&counter](int) {
			counter.fetch_add(1);
		});
		EXPECT_LE(pool.num_threads(), 2);
	}
#ifdef YOSYS_ENABLE_THREADS
	EXPECT_GE(counter.load(), 1);
	EXPECT_LE(counter.load(), 2);
#else
	EXPECT_EQ(counter.load(), 0);
#endif
}

// Helper types for ShardedHashtable tests
struct IntValue {
	using Accumulated = IntValue;
	int value;
	operator int() const { return value; }
};

struct IntValueEquality {
	bool operator()(int a, int b) const { return a == b; }
};

TEST_F(ThreadingTest, ShardedHashtableBasic) {
	ParallelDispatchThreadPool pool(1);

	using HashSet = ShardedHashtable<IntValue, IntValueEquality>;
	HashSet::Builder builder(pool);

	// Insert some values
	pool.run([&builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		builder.insert(ctx, {{10}, 10});
		builder.insert(ctx, {{20}, 20});
		builder.insert(ctx, {{30}, 30});
	});

	// Process
	pool.run([&builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		builder.process(ctx);
	});

	// Build and lookup
	HashSet set(builder);
	const IntValue *found10 = set.find({{10}, 10});
	const IntValue *found20 = set.find({{20}, 20});
	const IntValue *found99 = set.find({{99}, 99});

	ASSERT_NE(found10, nullptr);
	ASSERT_NE(found20, nullptr);
	EXPECT_EQ(found99, nullptr);
	EXPECT_EQ(*found10, 10);
	EXPECT_EQ(*found20, 20);
}

TEST_F(ThreadingTest, ShardedHashtableParallelInsert) {
	ParallelDispatchThreadPool pool(3);

	using HashSet = ShardedHashtable<IntValue, IntValueEquality>;
	HashSet::Builder builder(pool);

	// Insert values from multiple threads
	pool.run([&builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i = 0; i < 10; ++i) {
			int val = ctx.thread_num * 100 + i;
			builder.insert(ctx, {{val}, static_cast<unsigned>(val)});
		}
	});

	pool.run([&builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		builder.process(ctx);
	});

	HashSet set(builder);

	// Verify all values can be found
	for (int t = 0; t < pool.num_threads(); ++t) {
		for (int i = 0; i < 10; ++i) {
			int val = t * 100 + i;
			const IntValue *found = set.find({{val}, static_cast<unsigned>(val)});
			ASSERT_NE(found, nullptr) << "Value " << val << " not found";
			EXPECT_EQ(*found, val);
		}
	}
}

// Helper types for ShardedHashtable tests
struct IntDictValue {
	using Accumulated = IntDictValue;
	int key;
	int value;
	bool operator==(const IntDictValue &other) const { return key == other.key && value == other.value; }
	bool operator!=(const IntDictValue &other) const { return !(*this == other); }
};

struct IntDictKeyEquality {
	bool operator()(const IntDictValue &a, const IntDictValue &b) const { return a.key == b.key; }
};

// Collision handler that sums values
struct SumCollisionHandler {
	void operator()(IntDictValue &existing, IntDictValue &incoming) const {
		existing.value += incoming.value;
	}
};

TEST_F(ThreadingTest, ShardedHashtableCollision) {
	ParallelDispatchThreadPool pool(1);

	using HashSet = ShardedHashtable<IntDictValue, IntDictKeyEquality, SumCollisionHandler>;
	HashSet::Builder builder(pool);

	// Insert duplicate keys with same hash - duplicates should collapse
	pool.run([&builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		builder.insert(ctx, {{5, 10}, 5});
		builder.insert(ctx, {{5, 12}, 5});  // Duplicate key/hash
		builder.insert(ctx, {{5, 14}, 5});  // Another duplicate
	});

	pool.run([&builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		builder.process(ctx);
	});

	HashSet set(builder);
	const IntDictValue *found = set.find({{5, 0}, 5});
	ASSERT_NE(found, nullptr);
	// With default collision handler, first value is kept
	EXPECT_EQ(*found, (IntDictValue{5, 36}));
}

TEST_F(ThreadingTest, ShardedHashtableEmpty) {
	ParallelDispatchThreadPool pool(1);

	using HashSet = ShardedHashtable<IntValue, IntValueEquality>;
	HashSet::Builder builder(pool);

	// Don't insert anything, just process
	pool.run([&builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		builder.process(ctx);
	});

	HashSet set(builder);
	const IntValue *found = set.find({{42}, 42});
	EXPECT_EQ(found, nullptr);
}

TEST_F(ThreadingTest, ConcurrentWorkQueueSingleThread) {
	ConcurrentWorkQueue<int> queue(1, 10);  // 1 thread, batch size 10
	EXPECT_EQ(queue.num_threads(), 1);

	ThreadIndex thread{0};

	// Push some items (less than batch size)
	for (int i = 0; i < 5; ++i)
		queue.push(thread, i);

	// Pop should return those items
	std::vector<int> batch = queue.pop_batch(thread);
	EXPECT_THAT(batch, testing::UnorderedElementsAre(0, 1, 2, 3, 4));

	// Next pop should return empty (all threads "waiting")
	std::vector<int> empty_batch = queue.pop_batch(thread);
	EXPECT_TRUE(empty_batch.empty());
}

TEST_F(ThreadingTest, ConcurrentWorkQueueBatching) {
	ConcurrentWorkQueue<int> queue(1, 3);  // batch size 3
	ThreadIndex thread{0};

	queue.push(thread, 10);
	queue.push(thread, 20);
	queue.push(thread, 30);
	queue.push(thread, 40);
	queue.push(thread, 50);

	std::vector<int> popped;
	while (true) {
		std::vector<int> batch = queue.pop_batch(thread);
		if (batch.empty())
			break;
		popped.insert(popped.end(), batch.begin(), batch.end());
	}
	EXPECT_THAT(popped, testing::UnorderedElementsAre(10, 20, 30, 40, 50));
}

TEST_F(ThreadingTest, ConcurrentWorkQueueParallel) {
	ParallelDispatchThreadPool pool(2);
	if (pool.num_threads() < 2) {
		// Skip test if we don't have multiple threads
		return;
	}

	ConcurrentWorkQueue<int> queue(2, 3);
	std::atomic<int> sum{0};

	pool.run([&queue, &sum](const ParallelDispatchThreadPool::RunCtx &ctx) {
		// Each thread pushes some work
		for (int i = 0; i < 10; ++i)
			queue.push(ctx, ctx.thread_num * 100 + i);

		// Each thread processes work until done
		while (true) {
			std::vector<int> batch = queue.pop_batch(ctx);
			if (batch.empty())
				break;
			for (int v : batch)
				sum.fetch_add(v);
		}
	});

	// Thread 0 pushes: 0+1+2+...+9 = 45
	// Thread 1 pushes: 100+101+...+109 = 1045
	// Total = 45 + 1045 = 1090
	EXPECT_EQ(sum.load(), 1090);
}

YOSYS_NAMESPACE_END
