#include <deque>

#ifdef YOSYS_ENABLE_THREADS
#include <condition_variable>
#include <mutex>
#include <thread>
#endif

#include "kernel/yosys_common.h"
#include "kernel/log.h"

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
	// `max_threads` --- don't return more workers than this.
	// The result may be 0.
	static int pool_size(int reserved_cores, int max_threads);

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
