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

PrettyHelp::PrettyHelp()
{
	prior = current_help;
	current_help = this;
}

PrettyHelp::~PrettyHelp()
{
	current_help = prior;
}

PrettyHelp *PrettyHelp::get_current()
{
	if (current_help != nullptr)
		return current_help;
	else
		return new PrettyHelp();
}

bool PrettyHelp::has_content()
{
	return false;
}

void PrettyHelp::usage(const string &usage)
{
	log_pass_str(usage, current_indent+1, true);
	log("\n");
}

void PrettyHelp::option(const string &option, const string &description)
{
	log_pass_str(option, current_indent);
	if (description.length()) {
		log_pass_str(description, current_indent+1);
		log("\n");
	}
}

void PrettyHelp::codeblock(const string &code, const string &)
{
	log("%s\n", code.c_str());
}

void PrettyHelp::paragraph(const string &text)
{
	log_pass_str(text, current_indent);
	log("\n");
}

void PrettyHelp::optiongroup(const string &)
{
	current_indent += 1;
}

void PrettyHelp::endgroup()
{
	current_indent -= 1;
	log_assert(current_indent >= 0);
}
