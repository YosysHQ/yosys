#include "kernel/yosys_common.h"
#include "kernel/threading.h"

YOSYS_NAMESPACE_BEGIN

static int init_max_threads()
{
	const char *v = getenv("YOSYS_MAX_THREADS");
	if (v == nullptr)
		return INT32_MAX;
	return atoi(v);
}

static int get_max_threads()
{
	static int max_threads = init_max_threads();
	return max_threads;
}

static int init_work_units_per_thread_override()
{
	const char *v = getenv("YOSYS_WORK_UNITS_PER_THREAD");
	if (v == nullptr)
		return 0;
	return atoi(v);
}

static int get_work_units_per_thread_override()
{
	static int work_units_per_thread = init_work_units_per_thread_override();
	return work_units_per_thread;
}

void DeferredLogs::flush()
{
	for (auto &m : logs)
		if (m.error)
			YOSYS_NAMESPACE_PREFIX log_error("%s", m.text.c_str());
		else
			YOSYS_NAMESPACE_PREFIX log("%s", m.text.c_str());
}

int ThreadPool::pool_size(int reserved_cores, int max_worker_threads)
{
#ifdef YOSYS_ENABLE_THREADS
	int available_threads = std::min<int>(std::thread::hardware_concurrency(), get_max_threads());
	int num_threads = std::min(available_threads - reserved_cores, max_worker_threads);
        return std::max(0, num_threads);
#else
        return 0;
#endif
}

int ThreadPool::work_pool_size(int reserved_cores, int work_units, int work_units_per_thread)
{
	int work_units_per_thread_override = get_work_units_per_thread_override();
	if (work_units_per_thread_override > 0)
		work_units_per_thread = work_units_per_thread_override;
	return pool_size(reserved_cores, work_units / work_units_per_thread);
}

ThreadPool::ThreadPool(int pool_size, std::function<void(int)> b)
	: body(std::move(b))
{
#ifdef YOSYS_ENABLE_THREADS
        threads.reserve(pool_size);
        for (int i = 0; i < pool_size; i++)
                threads.emplace_back([i, this]{ body(i); });
#else
        log_assert(pool_size == 0);
#endif
}

ThreadPool::~ThreadPool()
{
#ifdef YOSYS_ENABLE_THREADS
	for (auto &t : threads)
		t.join();
#endif
}

IntRange item_range_for_worker(int num_items, int thread_num, int num_threads)
{
	if (num_threads <= 1) {
		return {0, num_items};
	}
	int items_per_thread = num_items / num_threads;
	int extra_items = num_items % num_threads;
	// The first `extra_items` threads get one extra item.
	int start = thread_num * items_per_thread + std::min(thread_num, extra_items);
	int end = (thread_num + 1) * items_per_thread + std::min(thread_num + 1, extra_items);
	return {start, end};
}

ParallelDispatchThreadPool::ParallelDispatchThreadPool(int pool_size)
		: num_worker_threads_(std::max(1, pool_size) - 1)
{
#ifdef YOSYS_ENABLE_THREADS
	main_to_workers_signal.resize(num_worker_threads_, 0);
#endif
	// Don't start the threads until we've constructed all our data members.
	thread_pool = std::make_unique<ThreadPool>(num_worker_threads_, [this](int thread_num){
		run_worker(thread_num);
	});
}

ParallelDispatchThreadPool::~ParallelDispatchThreadPool()
{
#ifdef YOSYS_ENABLE_THREADS
	if (num_worker_threads_ == 0)
		return;
	current_work = nullptr;
	num_active_worker_threads_ = num_worker_threads_;
	signal_workers_start();
	wait_for_workers_done();
#endif
}

void ParallelDispatchThreadPool::run(std::function<void(const RunCtx &)> work, int max_threads)
{
	Multithreading multithreading;
	num_active_worker_threads_ = num_threads(max_threads) - 1;
	if (num_active_worker_threads_ == 0) {
		work({{0}, 1});
		return;
	}
#ifdef YOSYS_ENABLE_THREADS
	current_work = &work;
	signal_workers_start();
	work({{0}, num_active_worker_threads_ + 1});
	wait_for_workers_done();
#endif
}

void ParallelDispatchThreadPool::run_worker(int thread_num)
{
#ifdef YOSYS_ENABLE_THREADS
	while (true)
	{
		worker_wait_for_start(thread_num);
		if (current_work == nullptr)
			break;
		(*current_work)({{thread_num + 1}, num_active_worker_threads_ + 1});
		signal_worker_done();
	}
	signal_worker_done();
#endif
}

YOSYS_NAMESPACE_END
