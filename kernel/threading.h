#include <deque>

#ifdef YOSYS_ENABLE_THREADS
#include <condition_variable>
#include <mutex>
#include <thread>
#endif

#include "kernel/yosys_common.h"
#include "kernel/log.h"
#include "kernel/utils.h"

#ifndef YOSYS_THREADING_H
#define YOSYS_THREADING_H

YOSYS_NAMESPACE_BEGIN

// Concurrent queue implementation. Not fast, but simple.
// Multi-producer, multi-consumer, optionally bounded.
// When YOSYS_ENABLE_THREADS is not defined, this is just a non-thread-safe non-blocking deque.
template <typename T>
class ConcurrentQueue
{
public:
	ConcurrentQueue(int capacity = INT_MAX)
		: capacity(capacity) {}
	// Push an element into the queue. If it's at capacity, block until there is room.
	void push_back(T t)
	{
#ifdef YOSYS_ENABLE_THREADS
		std::unique_lock<std::mutex> lock(mutex);
		not_full_condition.wait(lock, [this] { return static_cast<int>(contents.size()) < capacity; });
		if (contents.empty())
			not_empty_condition.notify_one();
#endif
		log_assert(!closed);
		contents.push_back(std::move(t));
#ifdef YOSYS_ENABLE_THREADS
		if (static_cast<int>(contents.size()) < capacity)
			not_full_condition.notify_one();
#endif
	}
	// Signal that no more elements will be produced. `pop_front()` will return nullopt.
	void close()
	{
#ifdef YOSYS_ENABLE_THREADS
		std::unique_lock<std::mutex> lock(mutex);
		not_empty_condition.notify_all();
#endif
		closed = true;
	}
	// Pop an element from the queue. Blocks until an element is available
	// or the queue is closed and empty.
	std::optional<T> pop_front()
	{
		return pop_front_internal(true);
	}
	// Pop an element from the queue. Does not block, just returns nullopt if the
	// queue is empty.
	std::optional<T> try_pop_front()
	{
		return pop_front_internal(false);
	}
private:
#ifdef YOSYS_ENABLE_THREADS
	std::optional<T> pop_front_internal(bool wait)
	{
		std::unique_lock<std::mutex> lock(mutex);
		if (wait) {
			not_empty_condition.wait(lock, [this] { return !contents.empty() || closed; });
		}
#else
	std::optional<T> pop_front_internal(bool)
	{
#endif
		if (contents.empty())
			return std::nullopt;
#ifdef YOSYS_ENABLE_THREADS
		if (static_cast<int>(contents.size()) == capacity)
			not_full_condition.notify_one();
#endif
		T result = std::move(contents.front());
		contents.pop_front();
#ifdef YOSYS_ENABLE_THREADS
		if (!contents.empty())
			not_empty_condition.notify_one();
#endif
		return std::move(result);
	}

#ifdef YOSYS_ENABLE_THREADS
	std::mutex mutex;
	// Signals one waiter thread when the queue changes and is not full.
	std::condition_variable not_full_condition;
	// Signals one waiter thread when the queue changes and is not empty.
	std::condition_variable not_empty_condition;
#endif
	std::deque<T> contents;
	int capacity;
	bool closed = false;
};

class DeferredLogs
{
public:
	template <typename... Args>
	void log(FmtString<TypeIdentity<Args>...> fmt, Args... args)
	{
		logs.push_back({fmt.format(args...), false});
	}
	template <typename... Args>
	void log_error(FmtString<TypeIdentity<Args>...> fmt, Args... args)
	{
		logs.push_back({fmt.format(args...), true});
	}
	void flush();
private:
	struct Message
	{
		std::string text;
		bool error;
	};
	std::vector<Message> logs;
};

class ThreadPool
{
public:
	// Computes the number of worker threads to use.
	// `reserved_cores` cores are set aside for other threads (e.g. work on the main thread).
	// `max_worker_threads` --- don't return more workers than this.
	// The result may be 0.
	static int pool_size(int reserved_cores, int max_worker_threads);

	// Computes the number of worker threads to use, by dividing work_units among threads.
	// For testing purposes you can set YOSYS_WORK_UNITS_PER_THREAD to override `work_units_per_thread`.
	// The result may be 0.
	static int work_pool_size(int reserved_cores, int work_units, int work_units_per_thread);

	// Create a pool of threads running the given closure (parameterized by thread number).
	// `pool_size` must be the result of a `pool_size()` call.
	ThreadPool(int pool_size, std::function<void(int)> b);
	ThreadPool(ThreadPool &&other) = delete;
	// Waits for all threads to terminate. Make sure those closures return!
	~ThreadPool();

	// Return the number of threads in the pool.
	int num_threads() const
	{
#ifdef YOSYS_ENABLE_THREADS
		return threads.size();
#else
		return 0;
#endif
	}
private:
	std::function<void(int)> body;
#ifdef YOSYS_ENABLE_THREADS
	std::vector<std::thread> threads;
#endif
};

// Divides some number of items into `num_threads` subranges and returns the
// `thread_num`'th subrange. If `num_threads` is zero, returns the whole range.
IntRange item_range_for_worker(int num_items, int thread_num, int num_threads);

// A type that encapsulates the index of a thread in some list of threads. Useful for
// stronger typechecking and code readability.
struct ThreadIndex {
	int thread_num;
};

// A set of threads with a `run()` API that runs a closure on all of the threads
// and wait for all those closures to complete. This is a convenient way to implement
// parallel algorithms that use barrier synchronization.
class ParallelDispatchThreadPool
{
public:
	// Create a pool of threads running the given closure (parameterized by thread number).
	// `pool_size` must be the result of a `pool_size()` call.
	// `pool_size` can be zero, which we treat as 1.
	ParallelDispatchThreadPool(int pool_size);
	~ParallelDispatchThreadPool();

	// For each thread running a closure, a `RunCtx` is passed to the closure. Currently
	// it contains the thread index and the total number of threads. It can be passed
	// directly to any APIs requiring a `ThreadIndex`.
	struct RunCtx : public ThreadIndex {
		int num_threads;
		IntRange item_range(int num_items) const {
			return item_range_for_worker(num_items, thread_num, num_threads);
		}
	};
	// Sometimes we only want to activate a subset of the threads in the pool. This
	// class provides a way to do that. It provides the same `num_threads()`
	// and `run()` APIs as a `ParallelDispatchThreadPool`.
	class Subpool {
	public:
		Subpool(ParallelDispatchThreadPool &parent, int max_threads)
				: parent(parent), max_threads(max_threads) {}
		// Returns the number of threads that will be used when calling `run()`.
		int num_threads() const {
			return parent.num_threads(max_threads);
		}
		void run(std::function<void(const RunCtx &)> work) {
			parent.run(std::move(work), max_threads);
		}
		ParallelDispatchThreadPool &thread_pool() { return parent; }
	private:
		ParallelDispatchThreadPool &parent;
		int max_threads;
	};

	// Run the `work` function in parallel on each thread in the pool (parameterized by
	// thread number). Waits for all work functions to complete. Only one `run()` can be
	// active at a time.
	// Uses no more than `max_threads` threads (but at least one).
	void run(std::function<void(const RunCtx &)> work) {
		run(std::move(work), INT_MAX);
	}

	// Returns the number of threads that will be used when calling `run()`.
	int num_threads() const {
		return num_threads(INT_MAX);
	}
private:
	friend class Subpool;

	void run(std::function<void(const RunCtx &)> work, int max_threads);
	int num_threads(int max_threads) const {
		return std::min(num_worker_threads_ + 1, std::max(1, max_threads));
	}
	void run_worker(int thread_num);

	std::unique_ptr<ThreadPool> thread_pool;
	std::function<void(const RunCtx &)> *current_work = nullptr;
	// Keeps a correct count even when threads are exiting.
	int num_worker_threads_;
	// The count of active workerthreads for the current `run()`.
	int num_active_worker_threads_ = 0;

#ifdef YOSYS_ENABLE_THREADS
	// Not especially efficient for large numbers of threads. Worker wakeup could scale
	// better by conceptually organising workers into a tree and having workers wake
	// up their children.
	std::mutex main_to_workers_signal_mutex;
	std::condition_variable main_to_workers_signal_cv;
	std::vector<uint8_t> main_to_workers_signal;
	void signal_workers_start() {
		std::unique_lock lock(main_to_workers_signal_mutex);
		std::fill(main_to_workers_signal.begin(), main_to_workers_signal.begin() + num_active_worker_threads_, 1);
		// When `num_active_worker_threads_` is small compared to `num_worker_threads_`, we have a "thundering herd"
		// problem here. Fixing that would add complexity so don't worry about it for now.
		main_to_workers_signal_cv.notify_all();
	}
	void worker_wait_for_start(int thread_num) {
		std::unique_lock lock(main_to_workers_signal_mutex);
		main_to_workers_signal_cv.wait(lock, [this, thread_num] { return main_to_workers_signal[thread_num] > 0; });
		main_to_workers_signal[thread_num] = 0;
	}

	std::atomic<int> done_workers = 0;
	std::mutex workers_to_main_signal_mutex;
	std::condition_variable workers_to_main_signal_cv;
	void signal_worker_done() {
		int d = done_workers.fetch_add(1, std::memory_order_release);
		if (d + 1 == num_active_worker_threads_) {
			std::unique_lock lock(workers_to_main_signal_mutex);
			workers_to_main_signal_cv.notify_all();
		}
	}
	void wait_for_workers_done() {
		std::unique_lock lock(workers_to_main_signal_mutex);
		workers_to_main_signal_cv.wait(lock, [this] { return done_workers.load(std::memory_order_acquire) == num_active_worker_threads_; });
		done_workers.store(0, std::memory_order_relaxed);
	}
#endif
};

template <class T>
class ConcurrentStack
{
public:
	void push_back(T &&t) {
#ifdef YOSYS_ENABLE_THREADS
		std::lock_guard<std::mutex> lock(mutex);
#endif
		contents.push_back(std::move(t));
	}
	std::optional<T> try_pop_back() {
#ifdef YOSYS_ENABLE_THREADS
		std::lock_guard<std::mutex> lock(mutex);
#endif
		if (contents.empty())
			return std::nullopt;
		T result = std::move(contents.back());
		contents.pop_back();
		return result;
	}
private:
#ifdef YOSYS_ENABLE_THREADS
	std::mutex mutex;
#endif
	std::vector<T> contents;
};

// A vector that is sharded into buckets, one per thread. This lets multiple threads write
// efficiently to the vector without synchronization overhead. After all writers have
// finished writing, the vector can be iterated over. The iteration order is deterministic:
// all the elements written by thread 0 in the order it inserted them, followed by all elements
// written by thread 1, etc.
template <typename T>
class ShardedVector {
public:
	ShardedVector(const ParallelDispatchThreadPool &thread_pool) {
		init(thread_pool.num_threads());
	}
	ShardedVector(const ParallelDispatchThreadPool::Subpool &thread_pool) {
		init(thread_pool.num_threads());
	}

	// Insert a value, passing the `ThreadIndex` of the writer thread.
	// Parallel inserts with different `ThreadIndex` values are fine.
	// Inserts must not run concurrently with any other methods (e.g.
	// iteration or `empty()`.)
	void insert(const ThreadIndex &thread, T value) {
		buckets[thread.thread_num].emplace_back(std::move(value));
	}

	bool empty() const {
		for (const std::vector<T> &bucket : buckets)
			if (!bucket.empty())
				return false;
		return true;
	}

	using Buckets = std::vector<std::vector<T>>;
	class iterator {
	public:
		iterator(typename Buckets::iterator bucket_it, typename Buckets::iterator bucket_end)
			: bucket_it(std::move(bucket_it)), bucket_end(std::move(bucket_end)) {
			if (bucket_it != bucket_end)
				inner_it = bucket_it->begin();
			normalize();
		}
		T& operator*() const { return *inner_it.value(); }
		iterator &operator++() {
			++*inner_it;
			normalize();
			return *this;
		}
		bool operator!=(const iterator &other) const {
			return bucket_it != other.bucket_it || inner_it != other.inner_it;
		}
	private:
		void normalize() {
			if (bucket_it == bucket_end)
				return;
			while (inner_it == bucket_it->end()) {
				++bucket_it;
				if (bucket_it == bucket_end) {
					inner_it.reset();
					return;
				}
				inner_it = bucket_it->begin();
			}
		}
		std::optional<typename std::vector<T>::iterator> inner_it;
		typename Buckets::iterator bucket_it;
		typename Buckets::iterator bucket_end;
	};
	iterator begin() { return iterator(buckets.begin(), buckets.end()); }
	iterator end() { return iterator(buckets.end(), buckets.end()); }
private:
	void init(int num_threads) {
		buckets.resize(num_threads);
	}
	Buckets buckets;
};

// The default collision handler for `ShardedHashtable` resolves collisions by keeping
// the current value and discarding the other. This is correct when all values with the
// same key are interchangeable (e.g. the hashtable is being used as a set).
template <typename V>
struct DefaultCollisionHandler {
	void operator()(typename V::Accumulated &, typename V::Accumulated &) const {}
};

// A hashtable that can be efficiently built in parallel and then looked up concurrently.
// `V` is the type of elements that will be added to the hashtable. It must have a
// member type `Accumulated` representing the combination of multiple `V` elements. This
// can be the same as `V`, but for example `V` could contain a Wire* and `V::Accumulated`
// could contain a `pool<Wire*>`. `KeyEquality` is a class containing an `operator()` that
// returns true of two `V` elements have equal keys.
// `CollisionHandler` is used to reduce two `V::Accumulated` values into a single value.
//
// To use this, first construct a `Builder` and fill it in (in parallel), then construct
// a `ShardedHashtable` from the `Builder`.
template <typename V, typename KeyEquality, typename CollisionHandler = DefaultCollisionHandler<V>>
class ShardedHashtable {
public:
	// A combination of a `V` and its hash value.
	struct Value {
		Value(V value, unsigned int hash) : value(std::move(value)), hash(hash) {}
		Value(Value &&) = default;
		Value(const Value &) = delete;
		Value &operator=(const Value &) = delete;
		V value;
		unsigned int hash;
	};
	// A combination of a `V::Accumulated` and its hash value.
	struct AccumulatedValue {
		AccumulatedValue(typename V::Accumulated value, unsigned int hash) : value(std::move(value)), hash(hash) {}
		AccumulatedValue(AccumulatedValue &&) = default;
#if defined(_MSC_VER)
		AccumulatedValue(const AccumulatedValue &) {
			log_error("Copy constructor called on AccumulatedValue");
		}
		AccumulatedValue &operator=(const AccumulatedValue &) {
			log_error("Copy assignment called on AccumulatedValue");
			return *this;
		}
#else
		AccumulatedValue(const AccumulatedValue &) = delete;
		AccumulatedValue &operator=(const AccumulatedValue &) = delete;
#endif
		typename V::Accumulated value;
		unsigned int hash;
	};
	// A class containing an `operator()` that returns true of two `AccumulatedValue`
	// elements have equal keys.
	// Required to insert `AccumulatedValue`s into an `std::unordered_set`.
	struct AccumulatedValueEquality {
		KeyEquality inner;
		AccumulatedValueEquality(const KeyEquality &inner) : inner(inner) {}
		bool operator()(const AccumulatedValue &v1, const AccumulatedValue &v2) const {
			return inner(v1.value, v2.value);
		}
	};
	// A class containing an `operator()` that returns the hash value of an `AccumulatedValue`.
	// Required to insert `AccumulatedValue`s into an `std::unordered_set`.
	struct AccumulatedValueHashOp {
		size_t operator()(const AccumulatedValue &v) const {
			return static_cast<size_t>(v.hash);
		}
	};
	using Shard = std::unordered_set<AccumulatedValue, AccumulatedValueHashOp, AccumulatedValueEquality>;

	// First construct one of these. Then populate it in parallel by calling `insert()` from many threads.
	// Then do another parallel phase calling `process()` from many threads.
	class Builder {
	public:
		Builder(const ParallelDispatchThreadPool &thread_pool, KeyEquality equality = KeyEquality(), CollisionHandler collision_handler = CollisionHandler())
				: collision_handler(std::move(collision_handler)) {
			init(thread_pool.num_threads(), std::move(equality));
		}
		Builder(const ParallelDispatchThreadPool::Subpool &thread_pool, KeyEquality equality = KeyEquality(), CollisionHandler collision_handler = CollisionHandler())
				: collision_handler(std::move(collision_handler)) {
			init(thread_pool.num_threads(), std::move(equality));
		}
		// First call `insert` to insert all elements. All inserts must finish
		// before calling any `process()`.
		void insert(const ThreadIndex &thread, Value v) {
			// You might think that for the single-threaded case, we can optimize by
			// inserting directly into the `std::unordered_set` here. But that slows things down
			// a lot and I never got around to figuring out why.
			std::vector<std::vector<Value>> &buckets = all_buckets[thread.thread_num];
			size_t bucket = static_cast<size_t>(v.hash) % buckets.size();
			buckets[bucket].emplace_back(std::move(v));
		}
		// Then call `process` for each thread. All `process()`s must finish before using
		// the `Builder` to construct a `ShardedHashtable`.
		void process(const ThreadIndex &thread) {
			int size = 0;
			for (std::vector<std::vector<Value>> &buckets : all_buckets)
				size += GetSize(buckets[thread.thread_num]);
			Shard &shard = shards[thread.thread_num];
			shard.reserve(size);
			for (std::vector<std::vector<Value>> &buckets : all_buckets) {
				for (Value &value : buckets[thread.thread_num])
					accumulate(value, shard);
				// Free as much memory as we can during the parallel phase.
				std::vector<Value>().swap(buckets[thread.thread_num]);
			}
		}
	private:
		friend class ShardedHashtable<V, KeyEquality, CollisionHandler>;
		void accumulate(Value &value, Shard &shard) {
			// With C++20 we could make this more efficient using heterogenous lookup
			AccumulatedValue accumulated_value{std::move(value.value), value.hash};
			auto [it, inserted] = shard.insert(std::move(accumulated_value));
			if (!inserted)
				collision_handler(const_cast<typename V::Accumulated &>(it->value), accumulated_value.value);
		}
		void init(int num_threads, KeyEquality equality) {
			all_buckets.resize(num_threads);
			for (std::vector<std::vector<Value>> &buckets : all_buckets)
				buckets.resize(num_threads);
			for (int i = 0; i < num_threads; ++i)
				shards.emplace_back(0, AccumulatedValueHashOp(), AccumulatedValueEquality(equality));
		}
		const CollisionHandler collision_handler;
		// A num_threads x num_threads matrix of buckets.
		// In the first phase, each thread i gemerates elements and writes them to
		// bucket [i][j] where j = hash(element) % num_threads.
		// In the second phase, thread i reads from bucket [j][i] for all j, collecting
		// all elements where i = hash(element) % num_threads.
		std::vector<std::vector<std::vector<Value>>> all_buckets;
		std::vector<Shard> shards;
	};

	// Then finally construct the hashtable:
	ShardedHashtable(Builder &builder) : shards(std::move(builder.shards)) {
		// Check that all necessary 'process()' calls were made.
		for (std::vector<std::vector<Value>> &buckets : builder.all_buckets)
			for (std::vector<Value> &bucket : buckets)
				log_assert(bucket.empty());
		// Free memory.
		std::vector<std::vector<std::vector<Value>>>().swap(builder.all_buckets);
	}
	ShardedHashtable(ShardedHashtable &&other) = default;
	ShardedHashtable() {}

	ShardedHashtable &operator=(ShardedHashtable &&other) = default;

	// Look up by `AccumulatedValue`. If we switch to C++20 then we could use
	// heterogenous lookup to support looking up by `Value` here. Returns nullptr
	// if the key is not found.
	const typename V::Accumulated *find(const AccumulatedValue &v) const {
		size_t num_shards = shards.size();
		if (num_shards == 0)
			return nullptr;
		size_t shard = static_cast<size_t>(v.hash) % num_shards;
		auto it = shards[shard].find(v);
		if (it == shards[shard].end())
			return nullptr;
		return &it->value;
	}

	// Insert an element into the table. The caller is responsible for ensuring this does not
	// happen concurrently with any other method calls.
	void insert(AccumulatedValue v) {
		size_t num_shards = shards.size();
		if (num_shards == 0)
			return;
		size_t shard = static_cast<size_t>(v.hash) % num_shards;
		shards[shard].insert(v);
	}

	// Call this for each shard to implement parallel destruction. For very large `ShardedHashtable`s,
	// deleting all elements of all shards on a single thread can be a performance bottleneck.
	void clear(const ThreadIndex &shard) {
		AccumulatedValueEquality equality = shards[0].key_eq();
		shards[shard.thread_num] = Shard(0, AccumulatedValueHashOp(), equality);
	}
private:
	std::vector<Shard> shards;
};

// A concurrent work-queue that can share batches of work across threads.
// Uses a naive implementation of work-stealing.
template <typename T>
class ConcurrentWorkQueue {
public:
	// Create a queue that supports the given number of threads and
	// groups work into `batch_size` units.
	ConcurrentWorkQueue(int num_threads, int batch_size = 100)
		: batch_size(batch_size), thread_states(num_threads) {}
	int num_threads() const { return GetSize(thread_states); }
	// Push some work to do. Pushes and pops with the same `thread` must
	// not happen concurrently.
	void push(const ThreadIndex &thread, T work) {
		ThreadState &thread_state = thread_states[thread.thread_num];
		thread_state.next_batch.emplace_back(std::move(work));
		if (GetSize(thread_state.next_batch) < batch_size)
			return;
		bool was_empty;
		{
			std::unique_lock lock(thread_state.batches_lock);
			was_empty = thread_state.batches.empty();
			thread_state.batches.push_back(std::move(thread_state.next_batch));
		}
		if (was_empty) {
			std::unique_lock lock(waiters_lock);
			if (num_waiters > 0) {
				waiters_cv.notify_one();
			}
		}
	}
	// Grab some work to do.
	// If all threads enter `pop_batch()`, then instead of deadlocking the
	// queue will return no work. That is the only case in which it will
	// return no work.
	std::vector<T> pop_batch(const ThreadIndex &thread) {
		ThreadState &thread_state = thread_states[thread.thread_num];
		if (!thread_state.next_batch.empty())
			return std::move(thread_state.next_batch);
		// Empty our own work queue first.
		{
			std::unique_lock lock(thread_state.batches_lock);
			if (!thread_state.batches.empty()) {
				std::vector<T> batch = std::move(thread_state.batches.back());
				thread_state.batches.pop_back();
				return batch;
			}
		}
		// From here on in this function, our work queue is empty.
		while (true) {
			std::vector<T> batch = try_steal(thread);
			if (!batch.empty()) {
				return std::move(batch);
			}
			// Termination: if all threads run out of work, then all of
			// them will eventually enter this loop and there will be no further
			// notifications on waiters_cv, so all will eventually increment
			// num_waiters and wait, so num_waiters == num_threads()
			// will become true.
			std::unique_lock lock(waiters_lock);
			++num_waiters;
			if (num_waiters == num_threads()) {
				waiters_cv.notify_all();
				return {};
			}
			// As above, it's possible that we'll wait here even when there
			// are work batches posted by other threads. That's OK.
			waiters_cv.wait(lock);
			if (num_waiters == num_threads())
				return {};
			--num_waiters;
		}
	}
private:
	std::vector<T> try_steal(const ThreadIndex &thread) {
		for (int i = 1; i < num_threads(); i++) {
			int other_thread_num = (thread.thread_num + i) % num_threads();
			ThreadState &other_thread_state = thread_states[other_thread_num];
			std::unique_lock lock(other_thread_state.batches_lock);
			if (!other_thread_state.batches.empty()) {
				std::vector<T> batch = std::move(other_thread_state.batches.front());
				other_thread_state.batches.pop_front();
				return batch;
			}
		}
		return {};
	}

	int batch_size;

	struct ThreadState {
		// Entirely thread-local.
		std::vector<T> next_batch;

		std::mutex batches_lock;
		// Only the associated thread ever adds to this, and only at the back.
		// Other threads can remove elements from the front.
		std::deque<std::vector<T>> batches;
	};
	std::vector<ThreadState> thread_states;

	std::mutex waiters_lock;
	std::condition_variable waiters_cv;
	// Number of threads waiting for work. Their queues are empty.
	int num_waiters = 0;
};

// A monotonic flag. Starts false, and can be set to true in a thread-safe way.
// Once `load()` returns true, it will always return true.
// Uses relaxed atomics so there are no memory ordering guarantees. Do not use this
// to guard access to shared memory.
class MonotonicFlag {
public:
	MonotonicFlag() : value(false) {}
	bool load() const { return value.load(std::memory_order_relaxed); }
	void set() { value.store(true, std::memory_order_relaxed); }
	bool set_and_return_old() {
		return value.exchange(true, std::memory_order_relaxed);
	}
private:
	std::atomic<bool> value;
};

YOSYS_NAMESPACE_END

#endif // YOSYS_THREADING_H
