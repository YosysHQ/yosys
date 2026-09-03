/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#ifndef LOG_H
#define LOG_H

#include "kernel/yosys_common.h"

#include <chrono>
#include <time.h>

#include <regex>
#define YS_REGEX_COMPILE(param) std::regex(param, \
				std::regex_constants::nosubs | \
				std::regex_constants::optimize | \
				std::regex_constants::egrep)
#define YS_REGEX_COMPILE_WITH_SUBS(param) std::regex(param, \
				std::regex_constants::optimize | \
				std::regex_constants::egrep)

#if defined(_WIN32)
#  include <intrin.h>
#else
#  include <sys/time.h>
#  include <sys/resource.h>
#  if defined(__unix__) || (defined(__APPLE__) && defined(__MACH__))
#    include <signal.h>
#  endif
#endif

// from libs/sha1/sha1.h
class SHA1;

YOSYS_NAMESPACE_BEGIN

// YS_DEBUGTRAP is a macro that is functionally equivalent to a breakpoint
// if the platform provides such functionality, and does nothing otherwise.
// If no debugger is attached, it starts a just-in-time debugger if available,
// and crashes the process otherwise.
#if defined(_WIN32)
# define YS_DEBUGTRAP __debugbreak()
#else
# ifndef __has_builtin
// __has_builtin is a GCC/Clang extension; on a different compiler (or old enough GCC/Clang)
// that does not have it, using __has_builtin(...) is a syntax error.
#  define __has_builtin(x) 0
# endif
# if __has_builtin(__builtin_debugtrap)
#  define YS_DEBUGTRAP __builtin_debugtrap()
# elif defined(__unix__) || (defined(__APPLE__) && defined(__MACH__))
#  define YS_DEBUGTRAP raise(SIGTRAP)
# else
#  define YS_DEBUGTRAP do {} while(0)
# endif
#endif

// YS_DEBUGTRAP_IF_DEBUGGING is a macro that is functionally equivalent to a breakpoint
// if a debugger is attached, and does nothing otherwise.
#if defined(_WIN32)
# define YS_DEBUGTRAP_IF_DEBUGGING do { if (IsDebuggerPresent()) DebugBreak(); } while(0)
# elif defined(__unix__) || (defined(__APPLE__) && defined(__MACH__))
// There is no reliable (or portable) *nix equivalent of IsDebuggerPresent(). However,
// debuggers will stop when SIGTRAP is raised, even if the action is set to ignore.
# define YS_DEBUGTRAP_IF_DEBUGGING do { \
		auto old = signal(SIGTRAP, SIG_IGN); raise(SIGTRAP); signal(SIGTRAP, old); \
	} while(0)
#else
# define YS_DEBUGTRAP_IF_DEBUGGING do {} while(0)
#endif

struct log_cmd_error_exception { };

enum class LogSeverity {
	Debug,
	Comment,
	Info,
	Header,
	Warning,
	Error
};

struct LogMessage {
	LogMessage(LogSeverity severity, std::string_view prefix, std::string_view format, std::string_view message);
	LogSeverity severity;
	std::string prefix;
	std::string format;
	std::string message;
	std::chrono::steady_clock::time_point timestamp;

	std::string cached_msg;
};

class LogSink
{
public:
	virtual ~LogSink() = default;

	virtual bool should_log(const LogMessage &) const { return true; }
	virtual void log(const LogMessage &msg) = 0;
	virtual void flush() {}
	// TODO: Remove when AST/read_verilog removed
	virtual FILE *file_handle() { return nullptr; }
};

class LogSinkRef : public LogSink
{
public:
	explicit LogSinkRef(LogSink *sink) : sink(sink) {}
	bool should_log(const LogMessage &msg) const override { return sink->should_log(msg); }
	void log(const LogMessage &msg) override { sink->log(msg); }
	void flush() override { sink->flush(); }
	FILE *file_handle() override { return sink->file_handle(); }
private:
	LogSink *sink;
};

class FileLogSink : public LogSink
{
public:
	explicit FileLogSink(const std::string &filename, bool line_buffered, bool append);
	~FileLogSink() override;
	void log(const LogMessage &msg) override;
	void flush() override;
	FILE *file_handle() override { return file; }

private:
	FILE *file;
};

class ConsoleLogSink : public LogSink
{
public:
	void log(const LogMessage &msg) override;
	void flush() override;
	FILE *file_handle() override { return stdout; }
};

class StderrLogSink : public LogSink
{
public:
	explicit StderrLogSink(bool quiet) : quiet_warnings(quiet) {}
	bool should_log(const LogMessage &msg) const override;
	void log(const LogMessage &msg) override;
	void flush() override;
private:
	bool quiet_warnings;
};

class StreamLogSink : public LogSink
{
public:
	explicit StreamLogSink(std::ostream &stream) : stream(stream) {}
	void log(const LogMessage &msg) override { stream << msg.cached_msg; }
	void flush() override { stream.flush(); }

private:
	std::ostream &stream;
};

class ScratchPadLogSink : public LogSink
{
public:
	explicit ScratchPadLogSink(std::string scratchpad);
	void log(const LogMessage &msg) override;

private:
	std::string scratchpad;
};

class LogManager
{
private:
	struct LogExpectedItem
	{
		LogExpectedItem(const std::regex &pat, int expected) :
				pattern(pat), expected_count(expected), current_count(0) {}
		LogExpectedItem() : expected_count(0), current_count(0) {}

		std::regex pattern;
		int expected_count;
		int current_count;
	};

public:
	LogManager() = default;

	template<typename T, typename... Args>
	T &add_sink(Args&&... args)
	{
		auto sink = std::make_unique<T>(std::forward<Args>(args)...);
		T &ref = *sink;
		sinks.push_back(std::move(sink));
		return ref;
	}

	template<typename F>
	void for_each_sink(F &&func)
	{
		for (auto &sink : sinks)
			func(*sink);
	}

	bool empty() { return sinks.empty(); }
	void clear() { sinks.clear(); }
	void clear_original()
	{
		std::erase_if(sinks, [](const auto &sink) { return dynamic_cast<LogSinkRef *>(sink.get()) != nullptr; });
	}
	void flush() { for (auto &sink : sinks) sink->flush(); }

	class Scoped
	{
	public:
		explicit Scoped(LogManager &manager) :
			manager(manager),
			backup_sinks(std::move(manager.sinks)),
			backup_verbose_level(manager.verbose_level)
		{
			manager.sinks.reserve(backup_sinks.size());

			for (const auto &sink : backup_sinks)
				manager.sinks.push_back(std::make_unique<LogSinkRef>(sink.get()));
		}

		~Scoped()
		{
			manager.sinks.clear();
			manager.sinks = std::move(backup_sinks);
			manager.verbose_level = backup_verbose_level;
		}

		Scoped(const Scoped &) = delete;
		Scoped &operator=(const Scoped &) = delete;

	private:
		LogManager &manager;
		std::vector<std::unique_ptr<LogSink>> backup_sinks;
		int backup_verbose_level;
	};

	Scoped sink_scope()
	{
		return Scoped(*this);
	}

	class ScopedCmdErrorThrow
	{
	public:
		explicit ScopedCmdErrorThrow(LogManager &manager)
			: manager(manager), previous(manager.cmd_error_throw)
		{
			manager.cmd_error_throw = true;
		}

		~ScopedCmdErrorThrow()
		{
			manager.cmd_error_throw = previous;
		}

	private:
		LogManager &manager;
		bool previous;
	};

	ScopedCmdErrorThrow error_throw_scope()
	{
		return ScopedCmdErrorThrow(*this);
	}

	class LogMakeDebugHdl
	{
	public:
		explicit LogMakeDebugHdl(LogManager &manager, bool start_on = false)
			: manager(manager)
		{
			if (start_on)
				on();
		}

		~LogMakeDebugHdl()
		{
			off();
		}

		void on()
		{
			if (status)
				return;
			status = true;
			manager.make_debug++;
		}

		void off_silent()
		{
			if (!status)
				return;
			status = false;
			manager.make_debug--;
		}

		void off()
		{
			off_silent();
		}
	private:
		LogManager &manager;
		bool status = false;
	};

	LogMakeDebugHdl make_debug_scope(bool start_on = false)
	{
		return LogMakeDebugHdl(*this, start_on);
	}

	class ForceDebug
	{
	public:
		explicit ForceDebug(LogManager &manager, bool start_on = false)
			: manager(manager)
		{
			if (start_on)
				on();
		}

		~ForceDebug()
		{
			off();
		}

		void on()
		{
			if (active)
				return;

			active = true;
			manager.force_debug++;
		}

		void off()
		{
			if (!active)
				return;

			active = false;
			manager.force_debug--;
		}
	private:
		LogManager &manager;
		bool active = false;
	};

	ForceDebug force_debug_scope(bool start_on = false)
	{
		return ForceDebug(*this, start_on);
	}

	void force_debug_on() { force_debug++; }
	void force_debug_off() { if (force_debug > 0) force_debug--; }
	void set_force_debug(bool enabled) { force_debug = enabled ? 1 : 0;	}

	void report_unexpected_error();

	void add_experimental_ignore(std::string name) { experimental_ignored.insert(name); }
	void add_warn(std::string pattern) { warn_regexes.push_back(YS_REGEX_COMPILE(pattern)); }
	void add_nowarn(std::string pattern) { nowarn_regexes.push_back(YS_REGEX_COMPILE(pattern)); }
	void add_werror(std::string pattern) { werror_regexes.push_back(YS_REGEX_COMPILE(pattern)); }
	void add_expect(std::string type, std::string pattern, int count);

	void set_verbose_level(int level) { verbose_level = level; }
	void add_verbose_level(int level) { verbose_level += level; }
	void set_expect_no_warnings(bool value) { expect_no_warnings = value; }
	void set_log_time(bool value) { log_time = value; }
	void set_cmd_error_throw(bool value) { cmd_error_throw = value; }
	void set_hdump_all(bool value) { hdump_all = value; }
	int get_verbose_level() const { return verbose_level; }
	bool get_log_time() const { return log_time; }
	int get_warnings_unique() const { return GetSize(warnings); }
	int get_warnings_total() const { return warnings_count; }
	int get_errors_total() const { return errors_count; }
	const std::set<std::string> &get_experimental() const { return experimental; }
	const std::set<std::string> &get_deprecated() const { return deprecated; }
	std::chrono::steady_clock::time_point get_initial_time() const;

	void add_hdump(std::string name, std::string value) { hdump[name].insert(value); }

	void formatted_string(LogSeverity severity, std::string_view prefix, std::string_view format, std::string str);
	void formatted_header(RTLIL::Design *design, std::string_view format, std::string str);
	void formatted_warning(std::string_view prefix, std::string_view format, std::string message);
	void formatted_file_warning(std::string_view filename, int lineno, std::string_view format, std::string str);
	void formatted_file_info(std::string_view filename, int lineno, std::string_view format, std::string str);
	[[noreturn]] void formatted_file_error(std::string_view filename, int lineno, std::string_view format, std::string str);
	[[noreturn]] void formatted_error(std::string_view format, std::string str);
	[[noreturn]] void formatted_cmd_error(std::string_view format, std::string message);
	void suppressed();
	void add_experimental(const std::string &str);
	void add_deprecated(const std::string &str);
	void spacer();
	void push();
	void pop();

	void reset_stack();

	void check_expected();
	bool expects_error() { return (expect_error.size() + expect_prefix_error.size())>0; }
#ifndef NDEBUG
	bool is_debug(int n = 0) { if (force_debug) return true; debug_suppressed += n; return false; }
#else
	bool is_debug(int = 0) { return false; }
#endif
	void start_hasher();
	std::string finish_hasher();

private:
	void logv_string(LogSeverity severity, std::string_view prefix, std::string_view format, std::string str_in);
	[[noreturn]] void error_with_prefix(std::string_view prefix, std::string_view format, std::string message);

	std::vector<std::unique_ptr<LogSink>> sinks;
	int verbose_level = 0;
	int newline_count = 0;
	vector<int> header_count;
	int errors_count = 0;
	int warnings_count = 0;
	int warnings_count_noexpect = 0;
	std::set<std::string> warnings, experimental, experimental_ignored, deprecated;

	std::vector<std::regex> warn_regexes, nowarn_regexes, werror_regexes;
	dict<std::string, LogExpectedItem> expect_log, expect_warning, expect_error;
	dict<std::string, LogExpectedItem> expect_prefix_log, expect_prefix_warning, expect_prefix_error;
	bool expect_no_warnings = false;
	bool log_time = false;
	bool cmd_error_throw = false;
	std::map<std::string, std::set<std::string>> hdump;
	bool hdump_all = false;

	int debug_suppressed = 0;
	int make_debug = 0;
	int force_debug = 0;
	std::unique_ptr<SHA1> hasher;
};

LogManager &logger();

extern void (*log_error_atexit)();

void set_verific_logging(void (*cb)(int msg_type, const char *message_id, const char* file_path, unsigned int left_line, unsigned int left_col, unsigned int right_line, unsigned int right_col, const char *msg));
extern void (*log_verific_callback)(int msg_type, const char *message_id, const char* file_path, unsigned int left_line, unsigned int left_col, unsigned int right_line, unsigned int right_col, const char *msg);

#ifndef NDEBUG
static inline bool ys_debug(int n = 0) { return logger().is_debug(n); }
#else
static inline bool ys_debug(int = 0) { return false; }
#endif

template <typename... Args>
inline void log(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_string(LogSeverity::Info, {}, fmt.format_string(), fmt.format(args...));
}

template <typename... Args>
inline void log_comment(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_string(LogSeverity::Comment, {}, fmt.format_string(), fmt.format(args...));
}

template <typename... Args>
inline void log_formatted_string(LogSeverity severity, std::string_view prefix,
		FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_string(severity, prefix, fmt.format_string(), fmt.format(args...));
}

#define log_debug(...) do { if (ys_debug(1)) YOSYS_NAMESPACE_PREFIX log_formatted_string(YOSYS_NAMESPACE_PREFIX LogSeverity::Debug, {}, __VA_ARGS__); } while (0)

template <typename... Args>
inline void log_header(RTLIL::Design *design, FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_header(design, fmt.format_string(), fmt.format(args...));
}

template <typename... Args>
inline void log_warning(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_warning("Warning: ", fmt.format_string(), fmt.format(args...));
}

template <typename... Args>
inline void log_warning_noprefix(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_warning({}, fmt.format_string(), fmt.format(args...));
}

inline void log_experimental(const std::string &str)
{
	logger().add_experimental(str);
}

inline void log_deprecated(const std::string &str)
{
	logger().add_deprecated(str);
}

// Log with filename to report a problem in a source file.
template <typename... Args>
void log_file_warning(std::string_view filename, int lineno, FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_file_warning(filename, lineno, fmt.format_string(), fmt.format(args...));
}

template <typename... Args>
void log_file_info(std::string_view filename, int lineno, FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_file_info(filename, lineno, fmt.format_string(), fmt.format(args...));
}

template <typename... Args>
[[noreturn]] void log_error(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_error(fmt.format_string(), fmt.format(args...));
}

template <typename... Args>
[[noreturn]] void log_file_error(std::string_view filename, int lineno, FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_file_error(filename, lineno, fmt.format_string(), fmt.format(args...));
}

template <typename... Args>
[[noreturn]] void log_cmd_error(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
{
	logger().formatted_cmd_error(fmt.format_string(), fmt.format(args...));
}

inline void log_suppressed()
{
	logger().suppressed();
}

inline void log_spacer() { logger().spacer(); }
inline void log_push() { logger().push(); }
inline void log_pop() { logger().pop(); }

inline void log_reset_stack() { logger().reset_stack(); }
inline void log_flush() { logger().flush(); }

void log_backtrace(const char *prefix, int levels);


std::string log_signal(const RTLIL::SigSpec &sig, bool autoint = true);
std::string log_const(const RTLIL::Const &value, bool autoint = true);
const char *log_id(const RTLIL::IdString &id);

template<typename T> static inline const char *log_id(T *obj, const char *nullstr = nullptr) {
	if (nullstr && obj == nullptr)
		return nullstr;
	return log_id(obj->name);
}

void log_module(RTLIL::Module *module, std::string indent = "");
void log_cell(RTLIL::Cell *cell, std::string indent = "");
void log_wire(RTLIL::Wire *wire, std::string indent = "");

[[noreturn]]
void log_assert_failure(const char *expr, const char *file, int line);
static inline void log_assert_worker(bool cond, const char *expr, const char *file, int line) {
	if (!cond) {
		log_assert_failure(expr, file, line);
		log_flush();
		raise(SIGABRT);
	}
}
#ifndef NDEBUG
#  define log_assert(_assert_expr_) YOSYS_NAMESPACE_PREFIX log_assert_worker(_assert_expr_, #_assert_expr_, __FILE__, __LINE__)
#else
#  define log_assert(_assert_expr_) do { if (0) { (void)(_assert_expr_); } } while(0)
#endif

[[noreturn]]
void log_abort_internal(const char *file, int line);
#define log_abort() YOSYS_NAMESPACE_PREFIX log_abort_internal(__FILE__, __LINE__)
#define log_ping() YOSYS_NAMESPACE_PREFIX log("-- %s:%d %s --\n", __FILE__, __LINE__, __PRETTY_FUNCTION__)


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
#  elif defined(RUSAGE_SELF)
		struct rusage rusage;
		int64_t t = 0;
		for (int who : {RUSAGE_SELF, RUSAGE_CHILDREN}) {
			if (getrusage(who, &rusage) == -1) {
				log_cmd_error("getrusage failed!\n");
				log_abort();
			}
			t += 1000000000ULL * (int64_t) rusage.ru_utime.tv_sec + (int64_t) rusage.ru_utime.tv_usec * 1000ULL;
			t += 1000000000ULL * (int64_t) rusage.ru_stime.tv_sec + (int64_t) rusage.ru_stime.tv_usec * 1000ULL;
		}
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
static inline void log_dump_val_worker(char c)
{
	if (c >= 32 && c < 127) {
		log("'%c'", c);
	} else {
		log("'\\x%02x'", c);
	}
}
static inline void log_dump_val_worker(unsigned char c)
{
	if (c >= 32 && c < 127) {
		log("'%c'", c);
	} else {
		log("'\\x%02x'", c);
	}
}
static inline void log_dump_val_worker(bool v) { log("%s", v ? "true" : "false"); }
static inline void log_dump_val_worker(double v) { log("%f", v); }
static inline void log_dump_val_worker(char *v) { log("%s", v); }
static inline void log_dump_val_worker(const char *v) { log("%s", v); }
static inline void log_dump_val_worker(std::string v) { log("%s", v); }
static inline void log_dump_val_worker(PerformanceTimer p) { log("%f seconds", p.sec()); }
static inline void log_dump_args_worker(const char *p) { log_assert(*p == 0); }
void log_dump_val_worker(RTLIL::IdString v);
void log_dump_val_worker(RTLIL::SigSpec v);
void log_dump_val_worker(RTLIL::State v);

template<typename K, typename T> static inline void log_dump_val_worker(dict<K, T> &v);
template<typename K> static inline void log_dump_val_worker(pool<K> &v);
template<typename K> static inline void log_dump_val_worker(std::vector<K> &v);
template<typename T> static inline void log_dump_val_worker(T *ptr);

template<typename K, typename T>
static inline void log_dump_val_worker(dict<K, T> &v) {
	log("{");
	bool first = true;
	for (auto &it : v) {
		log("%s ", first ? "" : ",");
		log_dump_val_worker(it.first);
		log(": ");
		log_dump_val_worker(it.second);
		first = false;
	}
	log(" }");
}

template<typename K>
static inline void log_dump_val_worker(pool<K> &v) {
	log("{");
	bool first = true;
	for (auto &it : v) {
		log("%s ", first ? "" : ",");
		log_dump_val_worker(it);
		first = false;
	}
	log(" }");
}

template<typename K>
static inline void log_dump_val_worker(std::vector<K> &v) {
	log("{");
	bool first = true;
	for (auto &it : v) {
		log("%s ", first ? "" : ",");
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

#include "kernel/yosys.h"

#endif
