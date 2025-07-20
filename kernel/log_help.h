/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2025  Krystine Dawn <krystinedawn@yosyshq.com>
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

#ifndef LOG_HELP_H
#define LOG_HELP_H

#include "kernel/yosys_common.h"
#include "kernel/json.h"

#ifdef YOSYS_ENABLE_SOURCE_LOCATION
#include <experimental/source_location>
using std::experimental::source_location;
#else
struct source_location { // dummy placeholder
	int line() const { return 0; }
	int column() const { return 0; }
	const char* file_name() const { return nullptr; }
	const char* function_name() const { return nullptr; }
	static const source_location current(...) { return source_location(); }
};
#endif

YOSYS_NAMESPACE_BEGIN

class PrettyHelp
{
	PrettyHelp *prior = nullptr;
	int current_indent = 0;
public:
	PrettyHelp();
	~PrettyHelp();

	static PrettyHelp *get_current();

	bool has_content();

	void usage(
		const string &usage,
		const source_location location = source_location::current()
	);
	void option(
		const string &text,
		const string &description = "",
		const source_location location = source_location::current()
	);
	void codeblock(
		const string &code,
		const string &language = "none",
		const source_location location = source_location::current()
	);
	void paragraph(
		const string &text,
		const source_location location = source_location::current()
	);

	void open_optiongroup(
		const string &group = "",
		const source_location location = source_location::current()
	);
	void open_option(
		const string &text,
		const source_location location = source_location::current()
	);
	void close(int levels = 1);
};

YOSYS_NAMESPACE_END

#endif
