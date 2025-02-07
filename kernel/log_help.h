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

YOSYS_NAMESPACE_BEGIN

class ContentListing {
	vector<ContentListing *> _content;
public:
	string type;
	string body;
	const char* source_file;
	int source_line;

	ContentListing(
		string type = "root", string body = "",
		const char* source_file = "unknown", int source_line = 0
	) : type(type), body(body), source_file(source_file), source_line(source_line) {
		_content = {};
	}

	ContentListing(string type, string body, source_location location) :
		ContentListing(type, body, location.file_name(), location.line()) { }

	void add_content(ContentListing *new_content) {
		_content.push_back(new_content);
	}

	void add_content(string type, string body, source_location location) {
		auto new_content = new ContentListing(type, body, location);
		add_content(new_content);
	}

	bool has_content() { return _content.size() != 0; }
	const vector<ContentListing *> get_content() {
		const vector<ContentListing *> content = _content;
		return content;
	}
	ContentListing* back() {
		return _content.back();
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

	ContentListing* open_optiongroup(
		const string &name = "",
		const source_location location = source_location::current()
	);
	ContentListing* open_option(
		const string &text,
		const source_location location = source_location::current()
	);

	Json to_json();
};

class PrettyHelp
{
public:
	string group = "unknown";

private:
	PrettyHelp *_prior;
	ContentListing _root_listing;

public:
	PrettyHelp();
	~PrettyHelp();

	static PrettyHelp *get_current();

	bool has_content() { return _root_listing.has_content(); }
	const vector<ContentListing *> get_content() {
		return _root_listing.get_content();
	}
	ContentListing* get_root() {
		return &_root_listing;
	}

	void set_group(const string g) { group = g; }
	bool has_group() { return group.compare("unknown") != 0; }

	void log_help();
};

YOSYS_NAMESPACE_END

#endif
