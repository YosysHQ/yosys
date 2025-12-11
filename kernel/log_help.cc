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

#include "kernel/log_help.h"

USING_YOSYS_NAMESPACE

Json ContentListing::to_json() const {
	Json::object object;
	object["type"] = type;
	if (body.length()) object["body"] = body;
	if (strcmp(source_file, "unknown") != 0) object["source_file"] = source_file;
	if (source_line != 0) object["source_line"] = source_line;
	object["options"] = Json(options);
	Json::array content_array;
	for (auto child : _content) content_array.push_back(child.to_json());
	object["content"] = content_array;
	return object;
}

void ContentListing::usage(const string &text,
	const source_location location)
{
	log_assert(type.compare("root") == 0);
	add_content("usage", text, location);
}

void ContentListing::option(const string &text, const string &description,
	const source_location location)
{
	auto option = open_option(text, location);
	if (description.length())
		option->add_content("text", description, location);
}

void ContentListing::codeblock(const string &code, const string &language,
	const source_location location)
{
	add_content("code", code, location);
	back()->set_option("language", language);
}

void ContentListing::paragraph(const string &text,
	const source_location location)
{
	add_content("text", text, location);
}

ContentListing* ContentListing::open_usage(const string &text,
	const source_location location)
{
	usage(text, location);
	return back();
}

ContentListing* ContentListing::open_option(const string &text,
	const source_location location)
{
	log_assert(type.compare("root") == 0 || type.compare("usage") == 0);
	add_content("option", text, location);
	return back();
}

#define MAX_LINE_LEN 80
void log_content_body(const ContentListing &content, int indent=0, bool leading_newline=false) {
	// skip empty nodes
	if (content.body.empty())
		return;

	if (leading_newline)
		log("\n");

	// iterate over lines in content
	std::string indent_str(indent*4, ' ');
	std::istringstream iss(content.body);	
	bool partial_line = false;
	for (std::string line; std::getline(iss, line);) {
		log("%s", indent_str);
		if (content.type == "code") {
			// code blocks are verbatim
			log("%s", line);
		} else {
			// iterate over words and break at max line length
			auto curr_len = indent_str.length();
			std::istringstream lss(line);
			for (std::string word; std::getline(lss, word, ' ');) {
				// remove inline rst formatting
				while (word[0] == '`' && word.back() == '`')
					word = word.substr(1, word.length()-2);

				// if the current line is not empty, break before going over max
				if (partial_line && (curr_len + word.length()) >= MAX_LINE_LEN) {
					curr_len = indent_str.length();
					log("\n%s", indent_str);
					partial_line = false;
				}

				// print non-empty words
				if (word.length()) {
					if (partial_line)
						// add space after prior word
						word.insert(0, " ");
					log("%s", word);
					curr_len += word.length();
					partial_line = true;
				}
			}
		}
		log("\n");
	}
}

PrettyHelp *current_help = nullptr;

PrettyHelp::PrettyHelp()
{
	_prior = current_help;
	_root_listing = ContentListing("root", "");

	current_help = this;
}

PrettyHelp::~PrettyHelp()
{
	current_help = _prior;
}

PrettyHelp *PrettyHelp::get_current()
{
	if (current_help == nullptr)
		new PrettyHelp();
	return current_help;
}

void PrettyHelp::log_help() const
{
	for (auto &content : _root_listing) {
		if (content.type.compare("usage") == 0) {
			log_content_body(content, 1, true);
			log("\n");
		} else if (content.type.compare("option") == 0) {
			log_content_body(content, 1);
			for (auto &child : content) {
				log_content_body(child, 2);
				log("\n");
			}
		} else {
			log_content_body(content, 0);
			log("\n");
		}
	}
}
