#include "kernel/yosys_common.h"
#include "kernel/threading.h"

YOSYS_NAMESPACE_BEGIN

void DeferredLogs::flush()
{
	for (auto &m : logs)
		if (m.error)
			YOSYS_NAMESPACE_PREFIX log_error("%s", m.text.c_str());
		else
			YOSYS_NAMESPACE_PREFIX log("%s", m.text.c_str());
}

int ThreadPool::pool_size(int reserved_cores, int max_threads)
{
#ifdef YOSYS_ENABLE_THREADS
	int num_threads = std::min<int>(std::thread::hardware_concurrency() - reserved_cores, max_threads);
        return std::max(0, num_threads);
#else
        return 0;
#endif
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

YOSYS_NAMESPACE_END
