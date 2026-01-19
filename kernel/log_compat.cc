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


#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

// ABI compatibility for the YosysHQ Verific Extensions

// The YosysHQ Verific Extensions are compiled separately using their own
// stripped-down version of the Yosys headers. To maintain ABI compatibility
// with older extension builds post C++-ification of Yosys's logging APIs,
// which are backwards compatible on the API but not ABI level, this file
// provides ABI compatible versions of a subset of the old logging API used by
// the extensions.

void log_cmd_error(const char *format, ...)
{
    va_list ap;
	va_start(ap, format);
	std::string formatted = vstringf(format, ap);
	va_end(ap);
    log_formatted_cmd_error(formatted);
}

void log_warning(const char *format, ...)
{
    va_list ap;
	va_start(ap, format);
	std::string formatted = vstringf(format, ap);
	va_end(ap);
    log_formatted_warning("Warning: ", formatted);
}

void log_warning_noprefix(const char *format, ...)
{
    va_list ap;
	va_start(ap, format);
	std::string formatted = vstringf(format, ap);
	va_end(ap);
    log_formatted_warning("", formatted);
}

void log_error(const char *format, ...)
{
    va_list ap;
	va_start(ap, format);
	std::string formatted = vstringf(format, ap);
	va_end(ap);
    log_formatted_error(formatted);
}

static inline void log_formatted(std::string const &str)
{
    // We use this inline wrapper as the following becomes ambiguous as soon as
    // the `log` function below is declared.
    return log("%s", str);
}

void log(const char *format, ...)
{
    va_list ap;
	va_start(ap, format);
	std::string formatted = vstringf(format, ap);
	va_end(ap);
    log_formatted(formatted);
}

YOSYS_NAMESPACE_END
