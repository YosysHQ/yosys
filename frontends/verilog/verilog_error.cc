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
 *  ---
 *
 */

#include "kernel/yosys_common.h"
#include "frontends/verilog/verilog_error.h"
#include "frontends/verilog/verilog_location.h"

USING_YOSYS_NAMESPACE

/**
 * Legacy behavior is to only track lines. Now we have columns too, but we don't
 * report them in errors.
 * TODO: report columns, too
 */

[[noreturn]]
static void verr_at(std::string filename, int begin_line, char const *fmt, va_list ap)
{
    char buffer[1024];
    char *p = buffer;
    p += vsnprintf(p, buffer + sizeof(buffer) - p, fmt, ap);
    p += snprintf(p, buffer + sizeof(buffer) - p, "\n");
    YOSYS_NAMESPACE_PREFIX log_file_error(filename, begin_line, "%s", buffer);
    exit(1);
}

static void vwarn_at(std::string filename, int begin_line, char const *fmt, va_list ap)
{
    char buffer[1024];
    char *p = buffer;
    p += vsnprintf(p, buffer + sizeof(buffer) - p, fmt, ap);
    p += snprintf(p, buffer + sizeof(buffer) - p, "\n");
    YOSYS_NAMESPACE_PREFIX log_file_warning(filename, begin_line, "%s", buffer);
}

[[noreturn]]
void VERILOG_FRONTEND::err_at_loc(Location loc, char const *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    verr_at(loc.begin.filename ? *(loc.begin.filename) : "UNKNOWN", loc.begin.line, fmt, args);
}
void VERILOG_FRONTEND::warn_at_loc(Location loc, char const *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    vwarn_at(loc.begin.filename ? *(loc.begin.filename) : "UNKNOWN", loc.begin.line, fmt, args);
    va_end(args);
}

