/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"

#ifndef LOG_H
#define LOG_H

#include <time.h>
#include <regex>

#ifndef _WIN32
#  include <sys/time.h>
#  include <sys/resource.h>
#endif

#if defined(_MSC_VER)
// At least this is not in MSVC++ 2013.
#  define __PRETTY_FUNCTION__ __FUNCTION__
#endif

// from libs/sha1/sha1.h
class SHA1;

YOSYS_NAMESPACE_BEGIN

#define S__LINE__sub2(x) #x
#define S__LINE__sub1(x) S__LINE__sub2(x)
#define S__LINE__ S__LINE__sub1(__LINE__)

struct log_cmd_error_exception { };

extern std::vector<FILE*> log_files;
extern std::vector<std::ostream*> log_streams;
extern std::map<std::string, std::set<std::string>> log_hdump;
extern std::vector<std::regex> log_warn_regexes, log_nowarn_regexes, log_werror_regexes;
extern std::set<std::string> log_warnings, log_experimentals, log_experimentals_ignored;
extern int log_warnings_count;
extern int log_warnings_count_noexpect;
extern bool log_expect_no_warnings;
extern bool log_hdump_all;
extern FILE *log_errfile;
extern SHA1 *log_hasher;

extern bool log_time;
extern bool log_error_stderr;
extern bool log_cmd_error_throw;
extern bool log_quiet_warnings;
extern int log_verbose_level;
extern string log_last_error;
extern void (*log_error_atexit)();

extern int log_make_debug;
extern int log_force_debug;
extern int log_debug_suppressed;

void logv(const char *format, va_list ap);
void logv_header(RTLIL::Design *design, const char *format, va_list ap);
void logv_warning(const char *format, va_list ap);
void logv_warning_noprefix(const char *format, va_list ap);
YS_NORETURN void logv_error(const char *format, va_list ap) YS_ATTRIBUTE(noreturn);

void log(const char *format, ...)  YS_ATTRIBUTE(format(printf, 1, 2));
void log_header(RTLIL::Design *design, const char *format, ...) YS_ATTRIBUTE(format(printf, 2, 3));
void log_warning(const char *format, ...) YS_ATTRIBUTE(format(printf, 1, 2));
void log_experimental(const char *format, ...) YS_ATTRIBUTE(format(printf, 1, 2));

// Log with filename to report a problem in a source file.
void log_file_warning(const std::string &filename, int lineno, const char *format, ...) YS_ATTRIBUTE(format(printf, 3, 4));
void log_file_info(const std::string &filename, int lineno, const char *format, ...) YS_ATTRIBUTE(format(printf, 3, 4));

void log_warning_noprefix(const char *format, ...) YS_ATTRIBUTE(format(printf, 1, 2));
YS_NORETURN void log_error(const char *format, ...) YS_ATTRIBUTE(format(printf, 1, 2), noreturn);
void log_file_error(const string &filename, int lineno, const char *format, ...) YS_ATTRIBUTE(format(printf, 3, 4), noreturn);
YS_NORETURN void log_cmd_error(const char *format, ...) YS_ATTRIBUTE(format(printf, 1, 2), noreturn);

#ifndef NDEBUG
static inline bool ys_debug(int n = 0) { if (log_force_debug) return true; log_debug_suppressed += n; return false; }
#  define log_debug(...) do { if (ys_debug(1)) log(__VA_ARGS__); } while (0)
#else
static inline bool ys_debug(int = 0) { return false; }
#  define log_debug(_fmt, ...) do { } while (0)
#endif

static inline void log_suppressed() {
	if (log_debug_suppressed && !log_make_debug) {
		log("<suppressed ~%d debug messages>\n", log_debug_suppressed);
		log_debug_suppressed = 0;
	}
}

struct LogMakeDebugHdl {
	bool status = false;
	LogMakeDebugHdl(bool start_on = false) {
		if (start_on)
			on();
	}
	~LogMakeDebugHdl() {
		off();
	}
	void on() {
		if (status) return;
		status=true;
		log_make_debug++;
	}
	void off_silent() {
		if (!status) return;
		status=false;
		log_make_debug--;
	}
	void off() {
		off_silent();
	}
};

void log_spacer();
void log_push();
void log_pop();

void log_backtrace(const char *prefix, int levels);
void log_reset_stack();
void log_flush();

struct LogExpectedItem
{
	LogExpectedItem(std::string pattern, int expected) :
		expected_count(expected),
		current_count(0),
		pattern(pattern)
	{
	}

	int expected_count;
	int current_count;
	std::string pattern;
};

extern std::vector<std::pair<std::regex,LogExpectedItem>> log_expect_log, log_expect_warning, log_expect_error;
void log_check_expected();

const char *log_signal(const RTLIL::SigSpec &sig, bool autoint = true);
const char *log_const(const RTLIL::Const &value, bool autoint = true);
const char *log_id(RTLIL::IdString id);

template<typename T> static inline const char *log_id(T *obj, const char *nullstr = nullptr) {
	if (nullstr && obj == nullptr)
		return nullstr;
	return log_id(obj->name);
}

void log_module(RTLIL::Module *module, std::string indent = "");
void log_cell(RTLIL::Cell *cell, std::string indent = "");
void log_wire(RTLIL::Wire *wire, std::string indent = "");

#ifndef NDEBUG
static inline void log_assert_worker(bool cond, const char *expr, const char *file, int line) {
	if (!cond) log_error("Assert `%s' failed in %s:%d.\n", expr, file, line);
}
#  define log_assert(_assert_expr_) YOSYS_NAMESPACE_PREFIX log_assert_worker(_assert_expr_, #_assert_expr_, __FILE__, __LINE__)
#else
#  define log_assert(_assert_expr_)
#endif

#define log_abort() YOSYS_NAMESPACE_PREFIX log_error("Abort in %s:%d.\n", __FILE__, __LINE__)
#define log_ping() YOSYS_NAMESPACE_PREFIX log("-- %s:%d %s --\n", __FILE__, __LINE__, __PRETTY_FUNCTION__)


// ---------------------------------------------------
// This is the magic behind the code coverage counters
// ---------------------------------------------------

#if defined(YOSYS_ENABLE_COVER) && (defined(__linux__) || defined(__FreeBSD__))

#define cover(_id) do { \
    static CoverData __d __attribute__((section("yosys_cover_list"), aligned(1), used)) = { __FILE__, __FUNCTION__, _id, __LINE__, 0 }; \
    __d.counter++; \
} while (0)

struct CoverData {
	const char *file, *func, *id;
	int line, counter;
} YS_ATTRIBUTE(packed);

// this two symbols are created by the linker for the "yosys_cover_list" ELF section
extern "C" struct CoverData __start_yosys_cover_list[];
extern "C" struct CoverData __stop_yosys_cover_list[];

extern dict<std::string, std::pair<std::string, int>> extra_coverage_data;

void cover_extra(std::string parent, std::string id, bool increment = true);
dict<std::string, std::pair<std::string, int>> get_coverage_data();

#define cover_list(_id, ...) do { cover(_id); \
	std::string r = cover_list_worker(_id, __VA_ARGS__); \
	log_assert(r.empty()); \
} while (0)

static inline std::string cover_list_worker(std::string, std::string last) {
	return last;
}

template<typename... T>
std::string cover_list_worker(std::string prefix, std::string first, T... rest) {
	std::string selected = cover_list_worker(prefix, rest...);
	cover_extra(prefix, prefix + "." + first, first == selected);
	return first == selected ? "" : selected;
}

#else
#  define cover(...) do { } while (0)
#  define cover_list(...) do { } while (0)
#endif


// ------------------------------------------------------------
// everything below this line are utilities for troubleshooting
// ------------------------------------------------------------

// simple timer for performance measurements
// toggle the '#if 1' to get a baseline for the performance penalty added by the measurement
struct PerformanceTimer
{
#if 1
	int64_t total_ns;

	PerformanceTimer() {
		total_ns = 0;
	}

	static int64_t query() {
#  ifdef _WIN32
		return 0;
#  elif defined(_POSIX_TIMERS) && (_POSIX_TIMERS > 0)
		struct timespec ts;
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
		return int64_t(ts.tv_sec)*1000000000 + ts.tv_nsec;
#  elif defined(RUSAGE_SELF)
		struct rusage rusage;
		int64_t t;
		if (getrusage(RUSAGE_SELF, &rusage) == -1) {
			log_cmd_error("getrusage failed!\n");
			log_abort();
		}
		t = 1000000000ULL * (int64_t) rusage.ru_utime.tv_sec + (int64_t) rusage.ru_utime.tv_usec * 1000ULL;
		t += 1000000000ULL * (int64_t) rusage.ru_stime.tv_sec + (int64_t) rusage.ru_stime.tv_usec * 1000ULL;
		return t;
#  else
#    error "Don't know how to measure per-process CPU time. Need alternative method (times()/clocks()/gettimeofday()?)."
#  endif
	}

	void reset() {
		total_ns = 0;
	}

	void begin() {
		total_ns -= query();
	}

	void end() {
		total_ns += query();
	}

	float sec() const {
		return total_ns * 1e-9f;
	}
#else
	static int64_t query() { return 0; }
	void reset() { }
	void begin() { }
	void end() { }
	float sec() const { return 0; }
#endif
};

// simple API for quickly dumping values when debugging

static inline void log_dump_val_worker(short v) { log("%d", v); }
static inline void log_dump_val_worker(unsigned short v) { log("%u", v); }
static inline void log_dump_val_worker(int v) { log("%d", v); }
static inline void log_dump_val_worker(unsigned int v) { log("%u", v); }
static inline void log_dump_val_worker(long int v) { log("%ld", v); }
static inline void log_dump_val_worker(unsigned long int v) { log("%lu", v); }
#ifndef _WIN32
static inline void log_dump_val_worker(long long int v) { log("%lld", v); }
static inline void log_dump_val_worker(unsigned long long int v) { log("%lld", v); }
#endif
static inline void log_dump_val_worker(char c) { log(c >= 32 && c < 127 ? "'%c'" : "'\\x%02x'", c); }
static inline void log_dump_val_worker(unsigned char c) { log(c >= 32 && c < 127 ? "'%c'" : "'\\x%02x'", c); }
static inline void log_dump_val_worker(bool v) { log("%s", v ? "true" : "false"); }
static inline void log_dump_val_worker(double v) { log("%f", v); }
static inline void log_dump_val_worker(char *v) { log("%s", v); }
static inline void log_dump_val_worker(const char *v) { log("%s", v); }
static inline void log_dump_val_worker(std::string v) { log("%s", v.c_str()); }
static inline void log_dump_val_worker(PerformanceTimer p) { log("%f seconds", p.sec()); }
static inline void log_dump_args_worker(const char *p YS_ATTRIBUTE(unused)) { log_assert(*p == 0); }
void log_dump_val_worker(RTLIL::IdString v);
void log_dump_val_worker(RTLIL::SigSpec v);
void log_dump_val_worker(RTLIL::State v);

template<typename K, typename T, typename OPS>
static inline void log_dump_val_worker(dict<K, T, OPS> &v) {
	log("{");
	bool first = true;
	for (auto &it : v) {
		log(first ? " " : ", ");
		log_dump_val_worker(it.first);
		log(": ");
		log_dump_val_worker(it.second);
		first = false;
	}
	log(" }");
}

template<typename K, typename OPS>
static inline void log_dump_val_worker(pool<K, OPS> &v) {
	log("{");
	bool first = true;
	for (auto &it : v) {
		log(first ? " " : ", ");
		log_dump_val_worker(it);
		first = false;
	}
	log(" }");
}

template<typename T>
static inline void log_dump_val_worker(T *ptr) { log("%p", ptr); }

template<typename T, typename ... Args>
void log_dump_args_worker(const char *p, T first, Args ... args)
{
	int next_p_state = 0;
	const char *next_p = p;
	while (*next_p && (next_p_state != 0 || *next_p != ',')) {
		if (*next_p == '"')
			do {
				next_p++;
				while (*next_p == '\\' && *(next_p + 1))
					next_p += 2;
			} while (*next_p && *next_p != '"');
		if (*next_p == '\'') {
			next_p++;
			if (*next_p == '\\')
				next_p++;
			if (*next_p)
				next_p++;
		}
		if (*next_p == '(' || *next_p == '[' || *next_p == '{')
			next_p_state++;
		if ((*next_p == ')' || *next_p == ']' || *next_p == '}') && next_p_state > 0)
			next_p_state--;
		next_p++;
	}
	log("\n\t%.*s => ", int(next_p - p), p);
	if (*next_p == ',')
		next_p++;
	while (*next_p == ' ' || *next_p == '\t' || *next_p == '\r' || *next_p == '\n')
		next_p++;
	log_dump_val_worker(first);
	log_dump_args_worker(next_p, args ...);
}

#define log_dump(...) do { \
	log("DEBUG DUMP IN %s AT %s:%d:", __PRETTY_FUNCTION__, __FILE__, __LINE__); \
	log_dump_args_worker(#__VA_ARGS__, __VA_ARGS__); \
	log("\n"); \
} while (0)

YOSYS_NAMESPACE_END

#endif
