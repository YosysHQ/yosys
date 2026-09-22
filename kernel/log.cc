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

#include "kernel/yosys.h"
#include "libs/sha1/sha1.h"
#include "backends/rtlil/rtlil_backend.h"

#if !defined(_WIN32) || defined(__MINGW32__)
#  include <sys/time.h>
#endif

#if defined(YOSYS_ENABLE_DLOPEN)
#  include <dlfcn.h>
#endif

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <vector>
#include <list>

YOSYS_NAMESPACE_BEGIN

bool log_stderr_sink_forced = false;

LogManager &logger()
{
	static LogManager instance;
	return instance;
}

std::chrono::steady_clock::time_point LogManager::get_initial_time() const
{
	static const auto initial_time = std::chrono::steady_clock::now();
	return initial_time;
}

void (*log_error_atexit)() = NULL;
void (*log_verific_callback)(int msg_type, const char *message_id, const char* file_path, unsigned int left_line, unsigned int left_col, unsigned int right_line, unsigned int right_col, const char *msg) = NULL;

// TODO: remove when log_id is removed
vector<char*> log_id_cache;

static bool next_print_log = true;

FileLogSink::FileLogSink(const std::string &filename, bool line_buffered, bool append)
	: file(fopen(filename.c_str(), append ? "at" : "wt"))
{
	if (!file)
		throw std::runtime_error("Can't open log file `" + filename + "' for writing!\n");

	if (line_buffered)
		setvbuf(file, nullptr, _IOLBF, 0);
}

FileLogSink::~FileLogSink()
{
	flush();
	if (file)
		fclose(file);
}

void FileLogSink::log(const LogMessage &msg)
{
	fputs(msg.cached_msg.c_str(), file);
}

void FileLogSink::flush()
{
	fflush(file);
}

void ConsoleLogSink::log(const LogMessage &msg)
{
	FILE *file = (msg.severity == LogSeverity::Error) ? stderr : stdout;
	fputs(msg.cached_msg.c_str(), file);
}

void ConsoleLogSink::flush()
{
	fflush(stdout);
	fflush(stderr);
}

bool StderrLogSink::should_log(const LogMessage &msg) const
{
	return msg.severity == LogSeverity::Error ||
			(msg.severity == LogSeverity::Warning && !quiet_warnings) ||
			log_stderr_sink_forced;
}

void StderrLogSink::log(const LogMessage &msg)
{
	fputs(msg.cached_msg.c_str(), stderr);
}

void StderrLogSink::flush()
{
	fflush(stderr);
}

ScratchPadLogSink::ScratchPadLogSink(std::string scratchpad)
	: scratchpad(std::move(scratchpad))
{
}

void ScratchPadLogSink::log(const LogMessage &msg)
{
	RTLIL::Design *design = yosys_get_design();
	if (!design)
		return;

	design->scratchpad[scratchpad].append(msg.cached_msg);
}

LogMessage::LogMessage(LogSeverity severity, std::string_view prefix, std::string_view format, std::string_view message) :
	severity(severity),
	prefix(prefix),
	format(format),
	message(message),
	timestamp(std::chrono::steady_clock::now())
{
	std::string time_str;
	if (logger().get_log_time())
	{
		if (next_print_log) {
			next_print_log = false;
			auto elapsed = std::chrono::steady_clock::now() - logger().get_initial_time();
			auto us = std::chrono::duration_cast<std::chrono::microseconds>(elapsed);
			time_str += stringf("[%05d.%06d] ", int(us.count() / 1'000'000),int(us.count() % 1'000'000));
		}

		if (!format.empty() && format.back() == '\n')
			next_print_log = true;

		// Special case to detect newlines in Python log output, since
		// the binding always calls `log("%s", payload)` and the newline
		// is then in the first formatted argument
		if (format == "%s" && !message.empty() && message.back() == '\n')
			next_print_log = true;
	}
	cached_msg = stringf("%s%s%s", time_str, prefix, message);
}

static void log_id_cache_clear()
{
	for (auto p : log_id_cache)
		free(p);
	log_id_cache.clear();
}

void LogManager::logv_string(LogSeverity severity, std::string_view prefix, std::string_view format, std::string str_in) {
	size_t remove_leading = 0;
	while (format.size() > 1 && format[0] == '\n') {
		logv_string(severity, prefix, "\n", "\n");
		format = format.substr(1);
		++remove_leading;
	}
	if (remove_leading > 0) {
		str_in = str_in.substr(remove_leading);
	}

	std::string str = stringf("%s%s",prefix,str_in);

	if (str.empty())
		return;

	size_t nnl_pos = str.find_last_not_of('\n');
	if (nnl_pos == std::string::npos)
		newline_count += GetSize(str);
	else
		newline_count = GetSize(str) - nnl_pos - 1;

	if (hasher)
		hasher->update(str);

	auto msg = LogMessage(severity, prefix, format, str_in);
	for (auto &sink : sinks) {
		if (sink->should_log(msg))
			sink->log(msg);
	}

	if (severity == LogSeverity::Header)
		str = str_in;

	static std::string linebuffer;
	static bool warn_regex_recusion_guard = false;

	if (!warn_regex_recusion_guard)
	{
		warn_regex_recusion_guard = true;

		if (warn_regexes.empty() && expect_log.empty() && expect_prefix_log.empty())
		{
			linebuffer.clear();
		}
		else
		{
			linebuffer += str;

			if (!linebuffer.empty() && linebuffer.back() == '\n') {
				for (auto &re : warn_regexes)
					if (std::regex_search(linebuffer, re))
						log_warning("Found log message matching -W regex:\n%s", str);

				for (auto &[_, item] : expect_log)
					if (std::regex_search(linebuffer, item.pattern))
						item.current_count++;

				linebuffer.clear();
			}
		}

		warn_regex_recusion_guard = false;
	}
}

void LogManager::formatted_string(LogSeverity severity, std::string_view prefix, std::string_view format, std::string str)
{
	log_assert(!Multithreading::active());

	if (make_debug && !is_debug(1))
		return;
	logv_string(severity, prefix, format, std::move(str));
}

void LogManager::formatted_header(RTLIL::Design *design, std::string_view format, std::string str)
{
	log_assert(!Multithreading::active());

	spacer();
	if (header_count.size() > 0)
		header_count.back()++;

	if (int(header_count.size()) <= verbose_level) {
		log_stderr_sink_forced = true;
	}

	std::string header_id;

	for (int c : header_count)
		header_id += stringf("%s%d", header_id.empty() ? "" : ".", c);

	formatted_string(LogSeverity::Header, stringf("%s. ", header_id), format, std::move(str));
	flush();

	if (hdump_all)
		hdump[header_id].insert("yosys_dump_" + header_id + ".il");

	if (hdump.count(header_id) && design != nullptr)
		for (auto &filename : hdump.at(header_id)) {
			log("Dumping current design to '%s'.\n", filename);
			if (yosys_xtrace)
				IdString::xtrace_db_dump();
			Pass::call(design, {"dump", "-o", filename});
			if (yosys_xtrace)
				log("#X# -- end of dump --\n");
		}
	log_stderr_sink_forced = false;
}

void LogManager::formatted_warning(std::string_view prefix, std::string_view format, std::string message)
{
	log_assert(!Multithreading::active());

	bool suppressed = false;

	for (auto &re : nowarn_regexes)
		if (std::regex_search(message, re))
			suppressed = true;

	if (suppressed)
	{
		log("Suppressed %s%s", prefix, message);
	}
	else
	{
		int bak_make_debug = make_debug;
		make_debug = 0;

		for (auto &re : werror_regexes)
			if (std::regex_search(message, re))
				formatted_error(format, message);

		bool warning_match = false;
		for (auto &[_, item] : expect_warning)
			if (std::regex_search(message, item.pattern)) {
				item.current_count++;
				warning_match = true;
			}

		for (auto &[_, item] : expect_prefix_warning)
			if (std::regex_search(string(prefix) + message, item.pattern)) {
				item.current_count++;
				warning_match = true;
			}

		if (warnings.count(message))
		{
			formatted_string(LogSeverity::Info, prefix, format, message);
			flush();
		}
		else
		{
			formatted_string(LogSeverity::Warning, prefix, format, message);
			flush();
			warnings.insert(message);
		}

		if (!warning_match)
			warnings_count_noexpect++;
		warnings_count++;
		make_debug = bak_make_debug;
	}
}

void LogManager::formatted_file_warning(std::string_view filename, int lineno, std::string_view format, std::string str)
{
	std::string prefix = stringf("%s:%d: Warning: ", filename, lineno);
	formatted_warning(prefix, format, std::move(str));
}

void LogManager::formatted_file_info(std::string_view filename, int lineno, std::string_view format, std::string str)
{
	std::string prefix = stringf("%s:%d: Info: ", filename, lineno);
	formatted_string(LogSeverity::Info, prefix, format, std::move(str));
}

void LogManager::suppressed() {
	if (debug_suppressed && !make_debug) {
		constexpr const char* format = "<suppressed ~%d debug messages>\n";
		logv_string(LogSeverity::Info, {}, format, stringf(format, debug_suppressed));
		debug_suppressed = 0;
	}
}

[[noreturn]]
void LogManager::error_with_prefix(std::string_view prefix, std::string_view format, std::string message)
{
	int bak_make_debug = make_debug;
	make_debug = 0;
	suppressed();

	formatted_string(LogSeverity::Error, prefix, format, message);
	flush();

	make_debug = bak_make_debug;

	for (auto &[_, item] : expect_error)
		if (std::regex_search(message, item.pattern))
			item.current_count++;

	for (auto &[_, item] : expect_prefix_error)
		if (std::regex_search(string(prefix) + message, item.pattern))
			item.current_count++;

	errors_count++;

	check_expected();

	if (log_error_atexit)
		log_error_atexit();

	YS_DEBUGTRAP_IF_DEBUGGING;
	const char *e = getenv("YOSYS_ABORT_ON_LOG_ERROR");
	if (e && atoi(e))
		abort();

#if defined(_MSC_VER)
	_exit(1);
#else
	_Exit(1);
#endif
}

void LogManager::formatted_file_error(std::string_view filename, int lineno, std::string_view format, std::string str)
{
	std::string prefix = stringf("%s:%d: ERROR: ", filename, lineno);
	error_with_prefix(prefix, format, str);
}

void LogManager::add_experimental(const std::string &str)
{
	if (experimental_ignored.count(str) == 0 && experimental.count(str) == 0) {
		log_warning("Feature '%s' is experimental.\n", str);
		experimental.insert(str);
	}
}

void LogManager::add_deprecated(const std::string &str)
{
	if (deprecated.count(str) == 0) {
		log_warning("Feature '%s' is deprecated.\n", str);
		deprecated.insert(str);
	}
}

void LogManager::formatted_error(std::string_view format, std::string str)
{
	error_with_prefix("ERROR: ", format, std::move(str));
}

void log_assert_failure(const char *expr, const char *file, int line)
{
	log_error("Assert `%s' failed in %s:%d.\n", expr, file, line);
}

void log_abort_internal(const char *file, int line)
{
	log_error("Abort in %s:%d.\n", file, line);
}

void log_yosys_abort_message(std::string_view file, int line, std::string_view func, std::string_view message)
{
	log_error("Abort in %s:%d (%s): %s\n", file, line, func, message);
}

void LogManager::formatted_cmd_error(std::string_view format, std::string message)
{
	if (cmd_error_throw) {
		formatted_string(LogSeverity::Error, "ERROR: ", format, message);
		flush();

		throw log_cmd_error_exception();
	}

	formatted_error(format, message);
}

void LogManager::spacer()
{
	if (newline_count < 2) log("\n");
	if (newline_count < 2) log("\n");
}

void LogManager::push()
{
	header_count.push_back(0);
}

void LogManager::pop()
{
	header_count.pop_back();
	log_id_cache_clear();
	flush();
}

#if defined(YOSYS_ENABLE_DLOPEN)
void log_backtrace(const char *prefix, int levels)
{
	if (levels <= 0) return;

	Dl_info dli;
	void *p;

	if ((p = __builtin_extract_return_addr(__builtin_return_address(0))) && dladdr(p, &dli)) {
		log("%sframe #1: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #1: ---\n", prefix);
		return;
	}

	if (levels <= 1) return;

#ifndef DEBUG
	log("%sframe #2: [build Yosys with ENABLE_DEBUG for deeper backtraces]\n", prefix);
#else
	if ((p = __builtin_extract_return_addr(__builtin_return_address(1))) && dladdr(p, &dli)) {
		log("%sframe #2: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #2: ---\n", prefix);
		return;
	}

	if (levels <= 2) return;

	if ((p = __builtin_extract_return_addr(__builtin_return_address(2))) && dladdr(p, &dli)) {
		log("%sframe #3: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #3: ---\n", prefix);
		return;
	}

	if (levels <= 3) return;

	if ((p = __builtin_extract_return_addr(__builtin_return_address(3))) && dladdr(p, &dli)) {
		log("%sframe #4: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #4: ---\n", prefix);
		return;
	}

	if (levels <= 4) return;

	if ((p = __builtin_extract_return_addr(__builtin_return_address(4))) && dladdr(p, &dli)) {
		log("%sframe #5: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #5: ---\n", prefix);
		return;
	}

	if (levels <= 5) return;

	if ((p = __builtin_extract_return_addr(__builtin_return_address(5))) && dladdr(p, &dli)) {
		log("%sframe #6: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #6: ---\n", prefix);
		return;
	}

	if (levels <= 6) return;

	if ((p = __builtin_extract_return_addr(__builtin_return_address(6))) && dladdr(p, &dli)) {
		log("%sframe #7: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #7: ---\n", prefix);
		return;
	}

	if (levels <= 7) return;

	if ((p = __builtin_extract_return_addr(__builtin_return_address(7))) && dladdr(p, &dli)) {
		log("%sframe #8: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #8: ---\n", prefix);
		return;
	}

	if (levels <= 8) return;

	if ((p = __builtin_extract_return_addr(__builtin_return_address(8))) && dladdr(p, &dli)) {
		log("%sframe #9: %p %s(%p) %s(%p)\n", prefix, p, dli.dli_fname, dli.dli_fbase, dli.dli_sname, dli.dli_saddr);
	} else {
		log("%sframe #9: ---\n", prefix);
		return;
	}

	if (levels <= 9) return;
#endif
}
#else
void log_backtrace(const char*, int) { }
#endif

void LogManager::reset_stack()
{
	while (header_count.size() > 1)
		header_count.pop_back();
	log_id_cache_clear();
	flush();
}

void log_dump_val_worker(RTLIL::IdString v) {
	log("%s", v.unescape());
}

void log_dump_val_worker(RTLIL::SigSpec v) {
	log("%s", log_signal(v));
}

void log_dump_val_worker(RTLIL::State v) {
	log("%s", log_signal(v));
}

std::string log_signal(const RTLIL::SigSpec &sig, bool autoint)
{
	std::stringstream buf;
	RTLIL_BACKEND::dump_sigspec(buf, sig, autoint);
	return buf.str();
}

std::string log_const(const RTLIL::Const &value, bool autoint)
{
	if ((value.flags & RTLIL::CONST_FLAG_STRING) == 0)
		return log_signal(value, autoint);

	return "\"" + value.decode_string() + "\"";
}

const char *log_id(const RTLIL::IdString &str)
{
	std::string unescaped = str.unescape();
	log_id_cache.push_back(strdup(unescaped.c_str()));
	return log_id_cache.back();
}

void log_module(RTLIL::Module *module, std::string indent)
{
	std::stringstream buf;
	RTLIL_BACKEND::dump_module(buf, indent, module, module->design, false);
	log("%s", buf.str());
}

void log_cell(RTLIL::Cell *cell, std::string indent)
{
	std::stringstream buf;
	RTLIL_BACKEND::dump_cell(buf, indent, cell);
	log("%s", buf.str());
}

void log_wire(RTLIL::Wire *wire, std::string indent)
{
	std::stringstream buf;
	RTLIL_BACKEND::dump_wire(buf, indent, wire);
	log("%s", buf.str());
}

void LogManager::check_expected()
{
	// copy out all of the expected logs so that they cannot be re-checked
	// or match against themselves
	dict<std::string, LogExpectedItem> expect_log_copy, expect_warning_copy, expect_error_copy;
	dict<std::string, LogExpectedItem> expect_prefix_log_copy, expect_prefix_warning_copy, expect_prefix_error_copy;
	std::swap(expect_warning_copy, expect_warning);
	std::swap(expect_log_copy, expect_log);
	std::swap(expect_error_copy, expect_error);
	std::swap(expect_prefix_warning_copy, expect_prefix_warning);
	std::swap(expect_prefix_log_copy, expect_prefix_log);
	std::swap(expect_prefix_error_copy, expect_prefix_error);

	auto check = [&](const std::string kind, std::string pattern, LogExpectedItem item) {
		if (item.current_count == 0) {
			warn_regexes.clear();
			log_error("Expected %s pattern '%s' not found !\n", kind, pattern);
		}
		if (item.current_count != item.expected_count) {
			warn_regexes.clear();
			log_error("Expected %s pattern '%s' found %d time(s), instead of %d time(s) !\n",
				kind.c_str(), pattern.c_str(), item.current_count, item.expected_count);
		}
	};

	for (auto &[pattern, item] : expect_warning_copy)
		check("warning", pattern, item);
	for (auto &[pattern, item] : expect_prefix_warning_copy)
		check("prefixed warning", pattern, item);
	for (auto &[pattern, item] : expect_log_copy)
		check("log", pattern, item);
	for (auto &[pattern, item] : expect_prefix_log_copy)
		check("prefixed log", pattern, item);

	auto check_err = [&](const std::string kind, std::string pattern, LogExpectedItem item) {
		if (item.current_count == item.expected_count) {
			warn_regexes.clear();
			log("Expected %s pattern '%s' found !!!\n", kind, pattern);
			yosys_shutdown();
			#if defined(_MSC_VER)
				_exit(0);
			#else
				_Exit(0);
			#endif
		} else {
			warn_regexes.clear();
			log_error("Expected %s pattern '%s' not found !\n", kind, pattern);
		}
	};
	for (auto &[pattern, item] : expect_error_copy)
		check_err("error", pattern, item);
	for (auto &[pattern, item] : expect_prefix_error_copy)
		check_err("prefixed error", pattern, item);
}

void LogManager::report_unexpected_error()
{
	if (expect_no_warnings && warnings_count_noexpect)
		log_error("Unexpected warnings found: %d unique messages, %d total, %d expected\n", GetSize(warnings),
					warnings_count, warnings_count - warnings_count_noexpect);
}

void LogManager::add_expect(std::string type, std::string pattern, int count)
{
	if (type == "error")
		expect_error[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "prefix-error")
		expect_prefix_error[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "warning")
		expect_warning[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "prefix-warning")
		expect_prefix_warning[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "log")
		expect_log[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "prefix-log")
		expect_prefix_log[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else log_abort();
}

void LogManager::start_hasher()
{
	hasher = std::make_unique<SHA1>();
}

std::string LogManager::finish_hasher()
{
	if (!hasher)
		return {};

	std::string hash = hasher->final().substr(0, 10);
	hasher.reset();
	return hash;
}

YOSYS_NAMESPACE_END
