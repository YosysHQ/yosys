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

#ifndef LOG_H
#define LOG_H

#include "kernel/rtlil.h"
#include <stdio.h>
#include <vector>

extern std::vector<FILE*> log_files;
extern FILE *log_errfile;
extern bool log_time;
extern bool log_cmd_error_throw;

std::string stringf(const char *fmt, ...);

void logv(const char *format, va_list ap);
void logv_header(const char *format, va_list ap);
void logv_error(const char *format, va_list ap) __attribute__ ((noreturn));

void log(const char *format, ...)  __attribute__ ((format (printf, 1, 2)));
void log_header(const char *format, ...) __attribute__ ((format (printf, 1, 2)));
void log_error(const char *format, ...) __attribute__ ((format (printf, 1, 2))) __attribute__ ((noreturn));
void log_cmd_error(const char *format, ...) __attribute__ ((format (printf, 1, 2))) __attribute__ ((noreturn));

void log_push();
void log_pop();

void log_reset_stack();
void log_flush();

const char *log_signal(const RTLIL::SigSpec &sig, bool autoint = true);

#endif
