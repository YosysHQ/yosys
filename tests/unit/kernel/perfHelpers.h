#ifndef PERF_HELPERS_H
#define PERF_HELPERS_H

#include <chrono>
#include <cstdio>
#include <cstdlib>

#if defined(__linux__) || defined(__FreeBSD__)
#  include <sys/resource.h>
#  include <unistd.h>
#endif

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

inline int env_int(const char *name, int fallback)
{
	const char *value = getenv(name);
	if (value == nullptr || *value == 0)
		return fallback;
	return atoi(value);
}

inline size_t rss_bytes()
{
#if defined(__linux__) || defined(__FreeBSD__)
	size_t total_pages = 0, resident_pages = 0;
	FILE *f = fopen("/proc/self/statm", "r");
	if (f == nullptr)
		return 0;
	if (fscanf(f, "%zu %zu", &total_pages, &resident_pages) != 2)
		resident_pages = 0;
	fclose(f);
	return resident_pages * (size_t)sysconf(_SC_PAGESIZE);
#else
	return 0;
#endif
}

inline size_t peak_rss_bytes()
{
#if defined(__linux__) || defined(__FreeBSD__)
	struct rusage ru;
	if (getrusage(RUSAGE_SELF, &ru) != 0)
		return 0;
	return (size_t)ru.ru_maxrss * 1024;
#else
	return 0;
#endif
}

inline double mb(size_t bytes)
{
	return bytes / 1048576.0;
}

inline double ms(std::chrono::steady_clock::duration d)
{
	return std::chrono::duration<double, std::milli>(d).count();
}

YOSYS_NAMESPACE_END

#endif
