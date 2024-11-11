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

#if defined(__linux__) || defined(__FreeBSD__)
#  include <dlfcn.h>
#endif

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <vector>
#include <list>

YOSYS_NAMESPACE_BEGIN

std::vector<FILE*> log_files;
std::vector<std::ostream*> log_streams;
std::vector<std::string> log_scratchpads;
std::map<std::string, std::set<std::string>> log_hdump;
std::vector<std::regex> log_warn_regexes, log_nowarn_regexes, log_werror_regexes;
dict<std::string, LogExpectedItem> log_expect_log, log_expect_warning, log_expect_error;
std::set<std::string> log_warnings, log_experimentals, log_experimentals_ignored;
int log_warnings_count = 0;
int log_warnings_count_noexpect = 0;
bool log_expect_no_warnings = false;
bool log_hdump_all = false;
FILE *log_errfile = NULL;
SHA1 *log_hasher = NULL;

bool log_time = false;
bool log_error_stderr = false;
bool log_cmd_error_throw = false;
bool log_quiet_warnings = false;
int log_verbose_level;
string log_last_error;
void (*log_error_atexit)() = NULL;
void (*log_verific_callback)(int msg_type, const char *message_id, const char* file_path, unsigned int left_line, unsigned int left_col, unsigned int right_line, unsigned int right_col, const char *msg) = NULL;

int log_make_debug = 0;
int log_force_debug = 0;
int log_debug_suppressed = 0;

vector<int> header_count;
vector<char*> log_id_cache;
vector<shared_str> string_buf;
int string_buf_index = -1;

static struct timeval initial_tv = { 0, 0 };
static bool next_print_log = false;
static int log_newline_count = 0;

static void log_id_cache_clear()
{
	for (auto p : log_id_cache)
		free(p);
	log_id_cache.clear();
}

#if defined(_WIN32) && !defined(__MINGW32__)
// this will get time information and return it in timeval, simulating gettimeofday()
int gettimeofday(struct timeval *tv, struct timezone *tz)
{
	LARGE_INTEGER counter;
	LARGE_INTEGER freq;

	QueryPerformanceFrequency(&freq);
	QueryPerformanceCounter(&counter);

	counter.QuadPart *= 1000000;
	counter.QuadPart /= freq.QuadPart;

	tv->tv_sec = long(counter.QuadPart / 1000000);
	tv->tv_usec = counter.QuadPart % 1000000;

	return 0;
}
#endif

void logv(const char *format, va_list ap)
{
	while (format[0] == '\n' && format[1] != 0) {
		log("\n");
		format++;
	}

	if (log_make_debug && !ys_debug(1))
		return;

	std::string str = vstringf(format, ap);

	if (str.empty())
		return;

	size_t nnl_pos = str.find_last_not_of('\n');
	if (nnl_pos == std::string::npos)
		log_newline_count += GetSize(str);
	else
		log_newline_count = GetSize(str) - nnl_pos - 1;

	if (log_hasher)
		log_hasher->update(str);

	if (log_time)
	{
		std::string time_str;

		if (next_print_log || initial_tv.tv_sec == 0) {
			next_print_log = false;
			struct timeval tv;
			gettimeofday(&tv, NULL);
			if (initial_tv.tv_sec == 0)
				initial_tv = tv;
			if (tv.tv_usec < initial_tv.tv_usec) {
				tv.tv_sec--;
				tv.tv_usec += 1000000;
			}
			tv.tv_sec -= initial_tv.tv_sec;
			tv.tv_usec -= initial_tv.tv_usec;
			time_str += stringf("[%05d.%06d] ", int(tv.tv_sec), int(tv.tv_usec));
		}

		if (format[0] && format[strlen(format)-1] == '\n')
			next_print_log = true;

		// Special case to detect newlines in Python log output, since
		// the binding always calls `log("%s", payload)` and the newline
		// is then in the first formatted argument
		if (!strcmp(format, "%s") && str.back() == '\n')
			next_print_log = true;

		for (auto f : log_files)
			fputs(time_str.c_str(), f);

		for (auto f : log_streams)
			*f << time_str;
	}

	for (auto f : log_files)
		fputs(str.c_str(), f);

	for (auto f : log_streams)
		*f << str;

	RTLIL::Design *design = yosys_get_design();
	if (design != nullptr)
		for (auto &scratchpad : log_scratchpads)
			design->scratchpad[scratchpad].append(str);

	static std::string linebuffer;
	static bool log_warn_regex_recusion_guard = false;

	if (!log_warn_regex_recusion_guard)
	{
		log_warn_regex_recusion_guard = true;

		if (log_warn_regexes.empty() && log_expect_log.empty())
		{
			linebuffer.clear();
		}
		else
		{
			linebuffer += str;

			if (!linebuffer.empty() && linebuffer.back() == '\n') {
				for (auto &re : log_warn_regexes)
					if (std::regex_search(linebuffer, re))
						log_warning("Found log message matching -W regex:\n%s", str.c_str());

				for (auto &item : log_expect_log)
					if (std::regex_search(linebuffer, item.second.pattern))
						item.second.current_count++;

				linebuffer.clear();
			}
		}

		log_warn_regex_recusion_guard = false;
	}
}

void logv_header(RTLIL::Design *design, const char *format, va_list ap)
{
	bool pop_errfile = false;

	log_spacer();
	if (header_count.size() > 0)
		header_count.back()++;

	if (int(header_count.size()) <= log_verbose_level && log_errfile != NULL) {
		log_files.push_back(log_errfile);
		pop_errfile = true;
	}

	std::string header_id;

	for (int c : header_count)
		header_id += stringf("%s%d", header_id.empty() ? "" : ".", c);

	log("%s. ", header_id.c_str());
	logv(format, ap);
	log_flush();

	if (log_hdump_all)
		log_hdump[header_id].insert("yosys_dump_" + header_id + ".il");

	if (log_hdump.count(header_id) && design != nullptr)
		for (auto &filename : log_hdump.at(header_id)) {
			log("Dumping current design to '%s'.\n", filename.c_str());
			if (yosys_xtrace)
				IdString::xtrace_db_dump();
			Pass::call(design, {"dump", "-o", filename});
			if (yosys_xtrace)
				log("#X# -- end of dump --\n");
		}

	if (pop_errfile)
		log_files.pop_back();
}

static void logv_warning_with_prefix(const char *prefix,
                                     const char *format, va_list ap)
{
	std::string message = vstringf(format, ap);
	bool suppressed = false;

	for (auto &re : log_nowarn_regexes)
		if (std::regex_search(message, re))
			suppressed = true;

	if (suppressed)
	{
		log("Suppressed %s%s", prefix, message.c_str());
	}
	else
	{
		int bak_log_make_debug = log_make_debug;
		log_make_debug = 0;

		for (auto &re : log_werror_regexes)
			if (std::regex_search(message, re))
				log_error("%s",  message.c_str());

		bool warning_match = false;
		for (auto &item : log_expect_warning)
			if (std::regex_search(message, item.second.pattern)) {
				item.second.current_count++;
				warning_match = true;
			}

		if (log_warnings.count(message))
		{
			log("%s%s", prefix, message.c_str());
			log_flush();
		}
		else
		{
			if (log_errfile != NULL && !log_quiet_warnings)
				log_files.push_back(log_errfile);

			log("%s%s", prefix, message.c_str());
			log_flush();

			if (log_errfile != NULL && !log_quiet_warnings)
				log_files.pop_back();

			log_warnings.insert(message);
		}

		if (!warning_match)
			log_warnings_count_noexpect++;
		log_warnings_count++;
		log_make_debug = bak_log_make_debug;
	}
}

void logv_warning(const char *format, va_list ap)
{
	logv_warning_with_prefix("Warning: ", format, ap);
}

void logv_warning_noprefix(const char *format, va_list ap)
{
	logv_warning_with_prefix("", format, ap);
}

void log_file_warning(const std::string &filename, int lineno,
                      const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	std::string prefix = stringf("%s:%d: Warning: ",
			filename.c_str(), lineno);
	logv_warning_with_prefix(prefix.c_str(), format, ap);
	va_end(ap);
}

void log_file_info(const std::string &filename, int lineno,
                      const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	std::string fmt = stringf("%s:%d: Info: %s",
			filename.c_str(), lineno, format);
	logv(fmt.c_str(), ap);
	va_end(ap);
}

[[noreturn]]
static void logv_error_with_prefix(const char *prefix,
                                   const char *format, va_list ap)
{
#ifdef EMSCRIPTEN
	auto backup_log_files = log_files;
#endif
	int bak_log_make_debug = log_make_debug;
	log_make_debug = 0;
	log_suppressed();

	if (log_errfile != NULL)
		log_files.push_back(log_errfile);

	if (log_error_stderr)
		for (auto &f : log_files)
			if (f == stdout)
				f = stderr;

	log_last_error = vstringf(format, ap);
	log("%s%s", prefix, log_last_error.c_str());
	log_flush();

	log_make_debug = bak_log_make_debug;

	for (auto &item : log_expect_error)
		if (std::regex_search(log_last_error, item.second.pattern))
			item.second.current_count++;

	log_check_expected();

	if (log_error_atexit)
		log_error_atexit();

	YS_DEBUGTRAP_IF_DEBUGGING;
	const char *e = getenv("YOSYS_ABORT_ON_LOG_ERROR");
	if (e && atoi(e))
		abort();

#ifdef EMSCRIPTEN
	log_files = backup_log_files;
	throw 0;
#elif defined(_MSC_VER)
	_exit(1);
#else
	_Exit(1);
#endif
}

void logv_error(const char *format, va_list ap)
{
	logv_error_with_prefix("ERROR: ", format, ap);
}

void logv_file_error(const string &filename, int lineno,
                     const char *format, va_list ap)
{
	std::string prefix = stringf("%s:%d: ERROR: ",
				     filename.c_str(), lineno);
	logv_error_with_prefix(prefix.c_str(), format, ap);
}

void log_file_error(const string &filename, int lineno,
                    const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	logv_file_error(filename, lineno, format, ap);
}

void log(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	logv(format, ap);
	va_end(ap);
}

void log_header(RTLIL::Design *design, const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	logv_header(design, format, ap);
	va_end(ap);
}

void log_warning(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	logv_warning(format, ap);
	va_end(ap);
}

void log_experimental(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	string s = vstringf(format, ap);
	va_end(ap);

	if (log_experimentals_ignored.count(s) == 0 && log_experimentals.count(s) == 0) {
		log_warning("Feature '%s' is experimental.\n", s.c_str());
		log_experimentals.insert(s);
	}
}

void log_warning_noprefix(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	logv_warning_noprefix(format, ap);
	va_end(ap);
}

void log_error(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	logv_error(format, ap);
}

void log_cmd_error(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);

	if (log_cmd_error_throw) {
		log_last_error = vstringf(format, ap);

		// Make sure the error message gets through any selective silencing
		// of log output
		bool pop_errfile = false;
		if (log_errfile != NULL) {
			log_files.push_back(log_errfile);
			pop_errfile = true;
		}

		log("ERROR: %s", log_last_error.c_str());
		log_flush();

		if (pop_errfile)
			log_files.pop_back();

		throw log_cmd_error_exception();
	}

	logv_error(format, ap);
}

void log_spacer()
{
	if (log_newline_count < 2) log("\n");
	if (log_newline_count < 2) log("\n");
}

void log_push()
{
	header_count.push_back(0);
}

void log_pop()
{
	header_count.pop_back();
	log_id_cache_clear();
	string_buf.clear();
	string_buf_index = -1;
	log_flush();
}

#if (defined(__linux__) || defined(__FreeBSD__)) && defined(YOSYS_ENABLE_PLUGINS)
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

void log_reset_stack()
{
	while (header_count.size() > 1)
		header_count.pop_back();
	log_id_cache_clear();
	string_buf.clear();
	string_buf_index = -1;
	log_flush();
}

void log_flush()
{
	for (auto f : log_files)
		fflush(f);

	for (auto f : log_streams)
		f->flush();
}

void log_dump_val_worker(RTLIL::IdString v) {
	log("%s", log_id(v));
}

void log_dump_val_worker(RTLIL::SigSpec v) {
	log("%s", log_signal(v));
}

void log_dump_val_worker(RTLIL::State v) {
	log("%s", log_signal(v));
}

const char *log_signal(const RTLIL::SigSpec &sig, bool autoint)
{
	std::stringstream buf;
	RTLIL_BACKEND::dump_sigspec(buf, sig, autoint);

	if (string_buf.size() < 100) {
		string_buf.push_back(buf.str());
		return string_buf.back().c_str();
	} else {
		if (++string_buf_index == 100)
			string_buf_index = 0;
		string_buf[string_buf_index] = buf.str();
		return string_buf[string_buf_index].c_str();
	}
}

const char *log_const(const RTLIL::Const &value, bool autoint)
{
	if ((value.flags & RTLIL::CONST_FLAG_STRING) == 0)
		return log_signal(value, autoint);

	std::string str = "\"" + value.decode_string() + "\"";

	if (string_buf.size() < 100) {
		string_buf.push_back(str);
		return string_buf.back().c_str();
	} else {
		if (++string_buf_index == 100)
			string_buf_index = 0;
		string_buf[string_buf_index] = str;
		return string_buf[string_buf_index].c_str();
	}
}

const char *log_id(const RTLIL::IdString &str)
{
	log_id_cache.push_back(strdup(str.c_str()));
	const char *p = log_id_cache.back();
	if (p[0] != '\\')
		return p;
	if (p[1] == '$' || p[1] == '\\' || p[1] == 0)
		return p;
	if (p[1] >= '0' && p[1] <= '9')
		return p;
	return p+1;
}

const char *log_str(const char *str)
{
	log_id_cache.push_back(strdup(str));
	return log_id_cache.back();
}

const char *log_str(std::string const &str) {
	return log_str(str.c_str());
}

void log_module(RTLIL::Module *module, std::string indent)
{
	std::stringstream buf;
	RTLIL_BACKEND::dump_module(buf, indent, module, module->design, false);
	log("%s", buf.str().c_str());
}

void log_cell(RTLIL::Cell *cell, std::string indent)
{
	std::stringstream buf;
	RTLIL_BACKEND::dump_cell(buf, indent, cell);
	log("%s", buf.str().c_str());
}

void log_wire(RTLIL::Wire *wire, std::string indent)
{
	std::stringstream buf;
	RTLIL_BACKEND::dump_wire(buf, indent, wire);
	log("%s", buf.str().c_str());
}

void log_check_expected()
{
	// copy out all of the expected logs so that they cannot be re-checked
	// or match against themselves
	dict<std::string, LogExpectedItem> expect_log, expect_warning, expect_error;
	std::swap(expect_warning, log_expect_warning);
	std::swap(expect_log, log_expect_log);
	std::swap(expect_error, log_expect_error);

	for (auto &item : expect_warning) {
		if (item.second.current_count == 0) {
			log_warn_regexes.clear();
			log_error("Expected warning pattern '%s' not found !\n", item.first.c_str());
		}
		if (item.second.current_count != item.second.expected_count) {
			log_warn_regexes.clear();
			log_error("Expected warning pattern '%s' found %d time(s), instead of %d time(s) !\n",
				item.first.c_str(), item.second.current_count, item.second.expected_count);
		}
	}

	for (auto &item : expect_log) {
		if (item.second.current_count == 0) {
			log_warn_regexes.clear();
			log_error("Expected log pattern '%s' not found !\n", item.first.c_str());
		}
		if (item.second.current_count != item.second.expected_count) {
			log_warn_regexes.clear();
			log_error("Expected log pattern '%s' found %d time(s), instead of %d time(s) !\n",
				item.first.c_str(), item.second.current_count, item.second.expected_count);
		}
	}

	for (auto &item : expect_error)
		if (item.second.current_count == item.second.expected_count) {
			log_warn_regexes.clear();
			log("Expected error pattern '%s' found !!!\n", item.first.c_str());
			yosys_shutdown();
			#ifdef EMSCRIPTEN
				throw 0;
			#elif defined(_MSC_VER)
				_exit(0);
			#else
				_Exit(0);
			#endif
		} else {
			log_warn_regexes.clear();
			log_error("Expected error pattern '%s' not found !\n", item.first.c_str());
		}
}

// ---------------------------------------------------
// This is the magic behind the code coverage counters
// ---------------------------------------------------
#if defined(YOSYS_ENABLE_COVER) && (defined(__linux__) || defined(__FreeBSD__))

dict<std::string, std::pair<std::string, int>> extra_coverage_data;

void cover_extra(std::string parent, std::string id, bool increment) {
	if (extra_coverage_data.count(id) == 0) {
		for (CoverData *p = __start_yosys_cover_list; p != __stop_yosys_cover_list; p++)
			if (p->id == parent)
				extra_coverage_data[id].first = stringf("%s:%d:%s", p->file, p->line, p->func);
		log_assert(extra_coverage_data.count(id));
	}
	if (increment)
		extra_coverage_data[id].second++;
}

dict<std::string, std::pair<std::string, int>> get_coverage_data()
{
	dict<std::string, std::pair<std::string, int>> coverage_data;

	for (auto &it : pass_register) {
		std::string key = stringf("passes.%s", it.first.c_str());
		coverage_data[key].first = stringf("%s:%d:%s", __FILE__, __LINE__, __FUNCTION__);
		coverage_data[key].second += it.second->call_counter;
	}

	for (auto &it : extra_coverage_data) {
		if (coverage_data.count(it.first))
			log_warning("found duplicate coverage id \"%s\".\n", it.first.c_str());
		coverage_data[it.first].first = it.second.first;
		coverage_data[it.first].second += it.second.second;
	}

	for (CoverData *p = __start_yosys_cover_list; p != __stop_yosys_cover_list; p++) {
		if (coverage_data.count(p->id))
			log_warning("found duplicate coverage id \"%s\".\n", p->id);
		coverage_data[p->id].first = stringf("%s:%d:%s", p->file, p->line, p->func);
		coverage_data[p->id].second += p->counter;
	}

	for (auto &it : coverage_data)
		if (!it.second.first.compare(0, strlen(YOSYS_SRC "/"), YOSYS_SRC "/"))
			it.second.first = it.second.first.substr(strlen(YOSYS_SRC "/"));

	return coverage_data;
}

#endif

YOSYS_NAMESPACE_END
