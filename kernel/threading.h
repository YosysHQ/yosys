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

YOSYS_NAMESPACE_END

#endif // YOSYS_THREADING_H
