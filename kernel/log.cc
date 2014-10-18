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
#include "libs/sha1/sha1.h"
#include "backends/ilang/ilang_backend.h"

#if !defined(_WIN32) || defined(__MINGW32__)
#  include <sys/time.h>
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
FILE *log_errfile = NULL;
SHA1 *log_hasher = NULL;

bool log_time = false;
bool log_cmd_error_throw = false;
int log_verbose_level;

std::vector<int> header_count;
std::list<std::string> string_buf;
int string_buf_size = 0;

static struct timeval initial_tv = { 0, 0 };
static bool next_print_log = false;
static int log_newline_count = 0;

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

		for (auto f : log_files)
			fputs(time_str.c_str(), f);

		for (auto f : log_streams)
			*f << time_str;
	}

	for (auto f : log_files)
		fputs(str.c_str(), f);

	for (auto f : log_streams)
		*f << str;
}

void logv_header(const char *format, va_list ap)
{
	bool pop_errfile = false;

	log_spacer();
	if (header_count.size() > 0)
		header_count.back()++;

	if (int(header_count.size()) <= log_verbose_level && log_errfile != NULL) {
		log_files.push_back(log_errfile);
		pop_errfile = true;
	}

	for (int c : header_count)
		log("%d.", c);
	log(" ");
	logv(format, ap);
	log_flush();

	if (pop_errfile)
		log_files.pop_back();
}

void logv_error(const char *format, va_list ap)
{
	if (log_errfile != NULL)
		log_files.push_back(log_errfile);

	log("ERROR: ");
	logv(format, ap);
	log_flush();
	exit(1);
}

void log(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	logv(format, ap);
	va_end(ap);
}

void log_header(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	logv_header(format, ap);
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
		log("ERROR: ");
		logv(format, ap);
		log_flush();
		throw log_cmd_error_expection();
	}

	logv_error(format, ap);
}

void log_spacer()
{
	while (log_newline_count < 2)
		log("\n");
}

void log_push()
{
	header_count.push_back(0);
}

void log_pop()
{
	header_count.pop_back();
	string_buf.clear();
	string_buf_size = 0;
	log_flush();
}

void log_reset_stack()
{
	while (header_count.size() > 1)
		header_count.pop_back();
	string_buf.clear();
	string_buf_size = 0;
	log_flush();
}

void log_flush()
{
	for (auto f : log_files)
		fflush(f);

	for (auto f : log_streams)
		f->flush();
}

void log_dump_val_worker(RTLIL::SigSpec v) {
	log("%s", log_signal(v));
}

const char *log_signal(const RTLIL::SigSpec &sig, bool autoint)
{
	std::stringstream buf;
	ILANG_BACKEND::dump_sigspec(buf, sig, autoint);

	if (string_buf_size < 100)
		string_buf_size++;
	else
		string_buf.pop_front();
	string_buf.push_back(buf.str());

	return string_buf.back().c_str();
}

const char *log_id(RTLIL::IdString str)
{
	const char *p = str.c_str();
	log_assert(RTLIL::IdString::global_refcount_storage_[str.index_] > 1);
	if (p[0] == '\\' && p[1] != '$' && p[1] != 0)
		return p+1;
	return p;
}

void log_cell(RTLIL::Cell *cell, std::string indent)
{
	std::stringstream buf;
	ILANG_BACKEND::dump_cell(buf, indent, cell);
	log("%s", buf.str().c_str());
}

// ---------------------------------------------------
// This is the magic behind the code coverage counters
// ---------------------------------------------------
#ifdef COVER_ACTIVE

std::map<std::string, std::pair<std::string, int>> extra_coverage_data;

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

std::map<std::string, std::pair<std::string, int>> get_coverage_data()
{
	std::map<std::string, std::pair<std::string, int>> coverage_data;

	for (auto &it : pass_register) {
		std::string key = stringf("passes.%s", it.first.c_str());
		coverage_data[key].first = stringf("%s:%d:%s", __FILE__, __LINE__, __FUNCTION__);
		coverage_data[key].second += it.second->call_counter;
	}

	for (auto &it : extra_coverage_data) {
		if (coverage_data.count(it.first))
			log("WARNING: found duplicate coverage id \"%s\".\n", it.first.c_str());
		coverage_data[it.first].first = it.second.first;
		coverage_data[it.first].second += it.second.second;
	}

	for (CoverData *p = __start_yosys_cover_list; p != __stop_yosys_cover_list; p++) {
		if (coverage_data.count(p->id))
			log("WARNING: found duplicate coverage id \"%s\".\n", p->id);
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

