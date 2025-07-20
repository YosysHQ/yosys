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

Json ContentListing::to_json() {
	Json::object object;
	object["type"] = type;
	if (body.length()) object["body"] = body;
	if (strcmp(source_file, "unknown") != 0) object["source_file"] = source_file;
	if (source_line != 0) object["source_line"] = source_line;
	Json::array content_array;
	for (auto child : content) content_array.push_back(child->to_json());
	object["content"] = content_array;
	return object;
}

#define MAX_LINE_LEN 80
void log_pass_str(const std::string &pass_str, std::string indent_str, bool leading_newline=false) {
	if (pass_str.empty())
		return;
	std::istringstream iss(pass_str);
	if (leading_newline)
		log("\n");
	for (std::string line; std::getline(iss, line);) {
		log("%s", indent_str.c_str());
		auto curr_len = indent_str.length();
		std::istringstream lss(line);
		for (std::string word; std::getline(lss, word, ' ');) {
			while (word[0] == '`' && word.back() == '`')
				word = word.substr(1, word.length()-2);
			if (curr_len + word.length() >= MAX_LINE_LEN-1) {
				curr_len = 0;
				log("\n%s", indent_str.c_str());
			}
			if (word.length()) {
				log("%s ", word.c_str());
				curr_len += word.length() + 1;
			}
		}
		log("\n");
	}
}
void log_pass_str(const std::string &pass_str, int indent=0, bool leading_newline=false) {
	std::string indent_str(indent*4, ' ');
	log_pass_str(pass_str, indent_str, leading_newline);
}

PrettyHelp *current_help = nullptr;

PrettyHelp::PrettyHelp(Mode mode)
{
	_prior = current_help;
	_mode = mode;
	_root_listing = ContentListing({
		.type = "root"
	});
	_root_listing.type = "root";
	_current_listing = &_root_listing;

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

void PrettyHelp::usage(const string &usage,
	const source_location location)
{
	switch (_mode)
	{
	case LOG:
		log_pass_str(usage, _current_indent+1, true);
		log("\n");
		break;
	case LISTING:
		add_content("usage", usage, location);
		break;
	default:
		log_abort();
	}
}

void PrettyHelp::option(const string &text, const string &description,
	const source_location location)
{
	open_option(text);
	if (description.length()) {
		switch (_mode)
		{
		case LOG:
			log_pass_str(description, _current_indent);
			log("\n");
			break;
		case LISTING:
			add_content("text", description, location);
			break;
		default:
			log_abort();
		}
	}
	close(1);
}

void PrettyHelp::codeblock(const string &code, const string &language,
	const source_location location)
{
	switch (_mode)
	{
	case LOG:
		log("%s\n", code.c_str());
		break;
	case LISTING:
		add_content("code", code, location);
		break;
	default:
		log_abort();
	}
}

void PrettyHelp::paragraph(const string &text,
	const source_location location)
{
	switch (_mode)
	{
	case LOG:
		log_pass_str(text, _current_indent);
		log("\n");
		break;
	case LISTING:
		add_content("text", text, location);
		break;
	default:
		log_abort();
	}
}

void PrettyHelp::open_optiongroup(const string &name,
	const source_location location)
{
	switch (_mode)
	{
	case LOG:
		break;
	case LISTING:
		push_content("optiongroup", name, location);
		break;
	default:
		log_abort();
	}
	_current_indent += 1;
}

void PrettyHelp::open_option(const string &text,
	const source_location location)
{
	switch (_mode)
	{
	case LOG:
		log_pass_str(text, _current_indent);
		break;
	case LISTING:
		push_content("option", text, location);
		break;
	default:
		log_abort();
	}
	_current_indent += 1;
}

void PrettyHelp::close(int levels)
{
	
	switch (_mode)
	{
	case LOG:
		_current_indent -= levels;
		log_assert(_current_indent >= 0);
		break;
	case LISTING:
		for (int i=0; i<levels; i++) {
			_current_indent--;
			log_assert(_current_indent >= 0);
			pop_content();
		}
		break;
	default:
		log_abort();
	}
}
