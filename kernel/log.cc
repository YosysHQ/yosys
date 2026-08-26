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
			logger().get_log_forced();
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

void LogManager::logv_string(std::string_view prefix, std::string_view format, std::string str_in, LogSeverity severity) {
	size_t remove_leading = 0;
	while (format.size() > 1 && format[0] == '\n') {
		logv_string(prefix, "\n", "\n", severity);
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
		log_newline_count += GetSize(str);
	else
		log_newline_count = GetSize(str) - nnl_pos - 1;

	if (log_hasher)
		log_hasher->update(str);

	auto msg = LogMessage(severity, prefix, format, str_in);
	for (auto &sink : log_sinks) {
		if (sink->should_log(msg))
			sink->log(msg);
	}

	if (severity == LogSeverity::Header)
		str = str_in;

	static std::string linebuffer;
	static bool log_warn_regex_recusion_guard = false;

	if (!log_warn_regex_recusion_guard)
	{
		log_warn_regex_recusion_guard = true;

		if (log_warn_regexes.empty() && log_expect_log.empty() && log_expect_prefix_log.empty())
		{
			linebuffer.clear();
		}
		else
		{
			linebuffer += str;

			if (!linebuffer.empty() && linebuffer.back() == '\n') {
				for (auto &re : log_warn_regexes)
					if (std::regex_search(linebuffer, re))
						log_warning("Found log message matching -W regex:\n%s", str);

				for (auto &[_, item] : log_expect_log)
					if (std::regex_search(linebuffer, item.pattern))
						item.current_count++;

				linebuffer.clear();
			}
		}

		log_warn_regex_recusion_guard = false;
	}
}

void LogManager::log_formatted_string(std::string_view prefix, std::string_view format, std::string str, LogSeverity severity)
{
	log_assert(!Multithreading::active());

	if (log_make_debug && !is_debug(1))
		return;
	logv_string(prefix, format, std::move(str), severity);
}

void LogManager::log_formatted_header(RTLIL::Design *design, std::string_view format, std::string str)
{
	log_assert(!Multithreading::active());

	log_spacer();
	if (header_count.size() > 0)
		header_count.back()++;

	if (int(header_count.size()) <= log_verbose_level) {
		log_forced = true;
	}

	std::string header_id;

	for (int c : header_count)
		header_id += stringf("%s%d", header_id.empty() ? "" : ".", c);

	log_formatted_string(stringf("%s. ", header_id), format, std::move(str), LogSeverity::Header);
	flush();

	if (log_hdump_all)
		log_hdump[header_id].insert("yosys_dump_" + header_id + ".il");

	if (log_hdump.count(header_id) && design != nullptr)
		for (auto &filename : log_hdump.at(header_id)) {
			log("Dumping current design to '%s'.\n", filename);
			if (yosys_xtrace)
				IdString::xtrace_db_dump();
			Pass::call(design, {"dump", "-o", filename});
			if (yosys_xtrace)
				log("#X# -- end of dump --\n");
		}
	log_forced = false;
}

void LogManager::log_formatted_warning(std::string_view prefix, std::string_view format, std::string message)
{
	log_assert(!Multithreading::active());

	bool suppressed = false;

	for (auto &re : log_nowarn_regexes)
		if (std::regex_search(message, re))
			suppressed = true;

	if (suppressed)
	{
		log("Suppressed %s%s", prefix, message);
	}
	else
	{
		int bak_log_make_debug = log_make_debug;
		log_make_debug = 0;

		for (auto &re : log_werror_regexes)
			if (std::regex_search(message, re))
				log_formatted_error(format, message);

		bool warning_match = false;
		for (auto &[_, item] : log_expect_warning)
			if (std::regex_search(message, item.pattern)) {
				item.current_count++;
				warning_match = true;
			}

		for (auto &[_, item] : log_expect_prefix_warning)
			if (std::regex_search(string(prefix) + message, item.pattern)) {
				item.current_count++;
				warning_match = true;
			}

		if (log_warnings.count(message))
		{
			log_formatted_string(prefix, format, message, LogSeverity::Info);
			flush();
		}
		else
		{
			log_formatted_string(prefix, format, message, LogSeverity::Warning);
			flush();
			log_warnings.insert(message);
		}

		if (!warning_match)
			log_warnings_count_noexpect++;
		log_warnings_count++;
		log_make_debug = bak_log_make_debug;
	}
}

void LogManager::log_formatted_file_warning(std::string_view filename, int lineno, std::string_view format, std::string str)
{
	std::string prefix = stringf("%s:%d: Warning: ", filename, lineno);
	log_formatted_warning(prefix, format, std::move(str));
}

void LogManager::log_formatted_file_info(std::string_view filename, int lineno, std::string_view format, std::string str)
{
	std::string prefix = stringf("%s:%d: Info: ", filename, lineno);
	log_formatted_string(prefix, format, std::move(str), LogSeverity::Info);
}

void LogManager::log_suppressed() {
	if (log_debug_suppressed && !log_make_debug) {
		constexpr const char* format = "<suppressed ~%d debug messages>\n";
		logv_string({}, format, stringf(format, log_debug_suppressed),LogSeverity::Info);
		log_debug_suppressed = 0;
	}
}

[[noreturn]]
void LogManager::log_error_with_prefix(std::string_view prefix, std::string_view format, std::string message)
{
	int bak_log_make_debug = log_make_debug;
	log_make_debug = 0;
	log_suppressed();

	log_formatted_string(prefix, format, message, LogSeverity::Error);
	flush();

	log_make_debug = bak_log_make_debug;

	for (auto &[_, item] : log_expect_error)
		if (std::regex_search(message, item.pattern))
			item.current_count++;

	for (auto &[_, item] : log_expect_prefix_error)
		if (std::regex_search(string(prefix) + message, item.pattern))
			item.current_count++;

	log_errors_count++;

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

void LogManager::log_formatted_file_error(std::string_view filename, int lineno, std::string_view format, std::string str)
{
	std::string prefix = stringf("%s:%d: ERROR: ", filename, lineno);
	log_error_with_prefix(prefix, format, str);
}

void LogManager::log_experimental(const std::string &str)
{
	if (experimental_ignored.count(str) == 0 && experimental.count(str) == 0) {
		log_warning("Feature '%s' is experimental.\n", str);
		experimental.insert(str);
	}
}

void LogManager::log_deprecated(const std::string &str)
{
	log_warning("Feature '%s' is deprecated.\n", str);
	deprecated.insert(str);
}

void LogManager::log_formatted_error(std::string_view format, std::string str)
{
	log_error_with_prefix("ERROR: ", format, std::move(str));
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

void LogManager::log_formatted_cmd_error(std::string_view format, std::string message)
{
	if (log_cmd_error_throw) {
		log_formatted_string("ERROR: ", format, message, LogSeverity::Error);
		flush();

		throw log_cmd_error_exception();
	}

	log_formatted_error(format, message);
}

void LogManager::log_spacer()
{
	if (log_newline_count < 2) log("\n");
	if (log_newline_count < 2) log("\n");
}

void LogManager::log_push()
{
	header_count.push_back(0);
}

void LogManager::log_pop()
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

void LogManager::log_reset_stack()
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
	dict<std::string, LogExpectedItem> expect_log, expect_warning, expect_error;
	dict<std::string, LogExpectedItem> expect_prefix_log, expect_prefix_warning, expect_prefix_error;
	std::swap(expect_warning, log_expect_warning);
	std::swap(expect_log, log_expect_log);
	std::swap(expect_error, log_expect_error);
	std::swap(expect_prefix_warning, log_expect_prefix_warning);
	std::swap(expect_prefix_log, log_expect_prefix_log);
	std::swap(expect_prefix_error, log_expect_prefix_error);

	auto check = [&](const std::string kind, std::string pattern, LogExpectedItem item) {
		if (item.current_count == 0) {
			log_warn_regexes.clear();
			log_error("Expected %s pattern '%s' not found !\n", kind, pattern);
		}
		if (item.current_count != item.expected_count) {
			log_warn_regexes.clear();
			log_error("Expected %s pattern '%s' found %d time(s), instead of %d time(s) !\n",
				kind.c_str(), pattern.c_str(), item.current_count, item.expected_count);
		}
	};

	for (auto &[pattern, item] : expect_warning)
		check("warning", pattern, item);
	for (auto &[pattern, item] : expect_prefix_warning)
		check("prefixed warning", pattern, item);
	for (auto &[pattern, item] : expect_log)
		check("log", pattern, item);
	for (auto &[pattern, item] : expect_prefix_log)
		check("prefixed log", pattern, item);

	auto check_err = [&](const std::string kind, std::string pattern, LogExpectedItem item) {
		if (item.current_count == item.expected_count) {
			log_warn_regexes.clear();
			log("Expected %s pattern '%s' found !!!\n", kind, pattern);
			yosys_shutdown();
			#if defined(_MSC_VER)
				_exit(0);
			#else
				_Exit(0);
			#endif
		} else {
			log_warn_regexes.clear();
			log_error("Expected %s pattern '%s' not found !\n", kind, pattern);
		}
	};
	for (auto &[pattern, item] : expect_error)
		check_err("error", pattern, item);
	for (auto &[pattern, item] : expect_prefix_error)
		check_err("prefixed error", pattern, item);
}

void LogManager::report_unexpected_error()
{
	if (log_expect_no_warnings && log_warnings_count_noexpect)
		log_error("Unexpected warnings found: %d unique messages, %d total, %d expected\n", GetSize(log_warnings),
					log_warnings_count, log_warnings_count - log_warnings_count_noexpect);
}

void LogManager::add_expect(std::string type, std::string pattern, int count)
{
	if (type == "error")
		log_expect_error[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "prefix-error")
		log_expect_prefix_error[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "warning")
		log_expect_warning[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "prefix-warning")
		log_expect_prefix_warning[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "log")
		log_expect_log[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else if (type == "prefix-log")
		log_expect_prefix_log[pattern] = LogExpectedItem(YS_REGEX_COMPILE(pattern), count);
	else log_abort();
}

void LogManager::start_hasher()
{
	log_hasher = std::make_unique<SHA1>();
}

std::string LogManager::finish_hasher()
{
	if (!log_hasher)
		return {};

	std::string hash = log_hasher->final().substr(0, 10);
	log_hasher.reset();
	return hash;
}

YOSYS_NAMESPACE_END
