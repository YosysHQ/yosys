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
void VERILOG_FRONTEND::formatted_err_at_loc(Location loc, std::string str)
{
    YOSYS_NAMESPACE_PREFIX log_file_error(loc.begin.filename ? *(loc.begin.filename) : "UNKNOWN", loc.begin.line,
            "%s\n", std::move(str));
}

void VERILOG_FRONTEND::formatted_warn_at_loc(Location loc, std::string str)
{
    YOSYS_NAMESPACE_PREFIX log_file_warning(loc.begin.filename ? *(loc.begin.filename) : "UNKNOWN", loc.begin.line,
            "%s\n", std::move(str));
}
