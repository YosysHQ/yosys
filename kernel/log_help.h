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
	vector<ContentListing> _content;
public:
	string type;
	string body;
	const char* source_file;
	int source_line;
	std::map<string, string> options;

	ContentListing(
		string type = "root", string body = "",
		const char* source_file = "unknown", int source_line = 0
	) : type(type), body(body), source_file(source_file), source_line(source_line) {
		_content = {};
		options = {};
	}

	ContentListing(string type, string body, source_location location) :
		ContentListing(type, body, location.file_name(), location.line()) { }

	void add_content(string type, string body, source_location location) {
		_content.push_back({type, body, location});
	}

	bool has_content() const { return _content.size() != 0; }

	vector<ContentListing>::const_iterator begin() const { return _content.cbegin(); }
	vector<ContentListing>::const_iterator end() const { return _content.cend(); }

	ContentListing* back() {
		return &_content.back();
	}

	void set_option(string key, string val = "") {
		options[key] = val;
	}

	void usage(
		const string &text,
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

	ContentListing* open_usage(
		const string &text,
		const source_location location = source_location::current()
	);
	ContentListing* open_option(
		const string &text,
		const source_location location = source_location::current()
	);

	Json to_json() const;
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

	bool has_content() const { return _root_listing.has_content(); }

	vector<ContentListing>::const_iterator begin() const { return _root_listing.begin(); }
	vector<ContentListing>::const_iterator end() const { return _root_listing.end(); }

	ContentListing* get_root() {
		return &_root_listing;
	}

	void set_group(const string g) { group = g; }
	bool has_group() const { return group.compare("unknown") != 0; }

	void log_help() const;
};

YOSYS_NAMESPACE_END

#endif
