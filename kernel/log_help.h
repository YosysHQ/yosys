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

struct ContentListing {
	string type = "root";
	string body = "";
	const char* source_file = nullptr;
	int source_line = 0;
	vector<ContentListing *> content = {};
	ContentListing *parent = nullptr;

	void add_content(ContentListing *new_content) {
		new_content->parent = this;
		content.push_back(new_content);
	}

	void add_content(string type, string body, source_location location) {
		auto new_content = new ContentListing();
		new_content->type = type;
		new_content->body = body;
		new_content->source_file = location.file_name();
		new_content->source_line = location.line();
		add_content(new_content);
	}

	Json to_json();
};

class PrettyHelp
{
public:
	enum Mode {
		LOG,
		LISTING,
	};

private:
	PrettyHelp *_prior;
	Mode _mode;

	int _current_indent = 0;
	ContentListing _root_listing;
	ContentListing *_current_listing;
public:
	PrettyHelp(Mode mode = LOG);
	~PrettyHelp();

	static PrettyHelp *get_current();

	bool has_content() { return _root_listing.content.size();}
	const vector<ContentListing *> get_content() {
		const vector<ContentListing *> content = _root_listing.content;
		return content;
	}

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
		const string &name = "",
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
