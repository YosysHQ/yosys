/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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
 *  The Verilog frontend.
 *
 *  This frontend is using the AST frontend library (see frontends/ast/).
 *  Thus this frontend does not generate RTLIL code directly but creates an
 *  AST directly from the Verilog parse tree and then passes this AST to
 *  the AST frontend library.
 *
 *  ---
 *
 *  Ad-hoc implementation of a Verilog preprocessor. The directives `define,
 *  `include, `ifdef, `ifndef, `else and `endif are handled here. All other
 *  directives are handled by the lexer (see lexer.l).
 *
 */

#include "verilog_frontend.h"
#include "kernel/log.h"
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <list>

static std::list<std::string> output_code;
static std::list<std::string> input_buffer;
static size_t input_buffer_charp;

static void return_char(char ch)
{
	if (input_buffer_charp == 0)
		input_buffer.push_front(std::string() + ch);
	else
		input_buffer.front()[--input_buffer_charp] = ch;
}

static void insert_input(std::string str)
{
	if (input_buffer_charp != 0) {
		input_buffer.front() = input_buffer.front().substr(input_buffer_charp);
		input_buffer_charp = 0;
	}
	input_buffer.push_front(str);
}

static char next_char()
{
	if (input_buffer.size() == 0)
		return 0;

	assert(input_buffer_charp <= input_buffer.front().size());
	if (input_buffer_charp == input_buffer.front().size()) {
		input_buffer_charp = 0;
		input_buffer.pop_front();
		return next_char();
	}

	char ch = input_buffer.front()[input_buffer_charp++];
	return ch == '\r' ? next_char() : ch;
}

static void skip_spaces()
{
	while (1) {
		char ch = next_char();
		if (ch == 0)
			break;
		if (ch != ' ' && ch != '\t') {
			return_char(ch);
			break;
		}
	}
}

static std::string next_token(bool pass_newline = false)
{
	std::string token;

	char ch = next_char();
	if (ch == 0)
		return token;

	token += ch;
	if (ch == '\n') {
		if (pass_newline) {
			output_code.push_back(token);
			return "";
		}
		return token;
	}
	
	if (ch == ' ' || ch == '\t')
	{
		while ((ch = next_char()) != 0) {
			if (ch != ' ' && ch != '\t') {
				return_char(ch);
				break;
			}
			token += ch;
		}
	}
	else if (ch == '"')
	{
		while ((ch = next_char()) != 0) {
			token += ch;
			if (ch == '"')
				break;
			if (ch == '\\') {
				if ((ch = next_char()) != 0)
					token += ch;
			}
		}
	}
	else if (ch == '/')
	{
		if ((ch = next_char()) != 0) {
			if (ch == '/') {
				token += '*';
				char last_ch = 0;
				while ((ch = next_char()) != 0) {
					if (ch == '\n') {
						return_char(ch);
						break;
					}
					if (last_ch != '*' || ch != '/') {
						token += ch;
						last_ch = ch;
					}
				}
				token += " */";
			}
			else if (ch == '*') {
				token += '*';
				int newline_count = 0;
				char last_ch = 0;
				while ((ch = next_char()) != 0) {
					if (ch == '\n') {
						newline_count++;
						token += ' ';
					} else
						token += ch;
					if (last_ch == '*' && ch == '/')
						break;
					last_ch = ch;
				}
				while (newline_count-- > 0)
					return_char('\n');
			}
			else
				return_char(ch);
		}
	}
	else
	{
		const char *ok = "abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ$0123456789";
		while ((ch = next_char()) != 0) {
			if (strchr(ok, ch) == NULL) {
				return_char(ch);
				break;
			}
			token += ch;
		}
	}

	return token;
}

static void input_file(FILE *f, std::string filename)
{
	char buffer[513];
	int rc;

	insert_input("");
	auto it = input_buffer.begin();

	input_buffer.insert(it, "`file_push " + filename + "\n");
	while ((rc = fread(buffer, 1, sizeof(buffer)-1, f)) > 0) {
		buffer[rc] = 0;
		input_buffer.insert(it, buffer);
	}
	input_buffer.insert(it, "`file_pop\n");
}

static std::string define_to_feature(std::string defname)
{
	if (defname == "__YOSYS_ENABLE_DEFATTR__")
		return "defattr";
	return std::string();
}

std::string frontend_verilog_preproc(FILE *f, std::string filename)
{
	std::map<std::string, std::string> defines_map;
	int ifdef_fail_level = 0;

	output_code.clear();
	input_buffer.clear();
	input_buffer_charp = 0;

	input_file(f, filename);
	defines_map["__YOSYS__"] = "1";

	while (!input_buffer.empty())
	{
		std::string tok = next_token();
		// printf("token: >>%s<<\n", tok != "\n" ? tok.c_str() : "NEWLINE");

		if (tok == "`endif") {
			if (ifdef_fail_level > 0)
				ifdef_fail_level--;
			continue;
		}

		if (tok == "`else") {
			if (ifdef_fail_level == 0)
				ifdef_fail_level = 1;
			else if (ifdef_fail_level == 1)
				ifdef_fail_level = 0;
			continue;
		}

		if (tok == "`ifdef") {
			skip_spaces();
			std::string name = next_token(true);
			if (ifdef_fail_level > 0 || defines_map.count(name) == 0)
				ifdef_fail_level++;
			continue;
		}

		if (tok == "`ifndef") {
			skip_spaces();
			std::string name = next_token(true);
			if (ifdef_fail_level > 0 || defines_map.count(name) != 0)
				ifdef_fail_level++;
			continue;
		}

		if (ifdef_fail_level > 0) {
			if (tok == "\n")
				output_code.push_back(tok);
			continue;
		}

		if (tok == "`include") {
			skip_spaces();
			std::string fn = next_token(true);
			while (1) {
				size_t pos = fn.find('"');
				if (pos == std::string::npos)
					break;
				if (pos == 0)
					fn = fn.substr(1);
				else
					fn = fn.substr(0, pos) + fn.substr(pos+1);
			}
			FILE *fp = fopen(fn.c_str(), "r");
			if (fp == NULL && fn.size() > 0 && fn[0] != '/' && filename.find('/') != std::string::npos) {
				std::string fn2 = filename.substr(0, filename.rfind('/')+1) + fn;
				fp = fopen(fn2.c_str(), "r");
			}
			if (fp != NULL) {
				input_file(fp, fn);
				fclose(fp);
			} else
				output_code.push_back("`file_notfound " + fn + "\n");
			continue;
		}

		if (tok == "`define") {
			std::string name, value;
			skip_spaces();
			name = next_token(true);
			if (!define_to_feature(name).empty())
				output_code.push_back("`yosys_enable_" + define_to_feature(name));
			skip_spaces();
			int newline_count = 0;
			while (!tok.empty()) {
				tok = next_token();
				if (tok == "\n") {
					return_char('\n');
					break;
				}
				if (tok == "\\") {
					char ch = next_char();
					if (ch == '\n') {
						value += " ";
						newline_count++;
					} else {
						value += std::string("\\");
						return_char(ch);
					}
				} else
					value += tok;
			}
			while (newline_count-- > 0)
				return_char('\n');
			// printf("define: >>%s<< -> >>%s<<\n", name.c_str(), value.c_str());
			defines_map[name] = value;
			continue;
		}

		if (tok == "`undef") {
			std::string name;
			skip_spaces();
			name = next_token(true);
			if (!define_to_feature(name).empty())
				output_code.push_back("`yosys_disable_" + define_to_feature(name));
			// printf("undef: >>%s<<\n", name.c_str());
			defines_map.erase(name);
			continue;
		}

		if (tok == "`timescale") {
			std::string name;
			skip_spaces();
			while (!tok.empty() && tok != "\n")
				tok = next_token(true);
			if (tok == "\n")
				return_char('\n');
			continue;
		}

		if (tok.size() > 1 && tok[0] == '`' && defines_map.count(tok.substr(1)) > 0) {
			// printf("expand: >>%s<< -> >>%s<<\n", tok.c_str(), defines_map[tok.substr(1)].c_str());
			insert_input(defines_map[tok.substr(1)]);
			continue;
		}

		output_code.push_back(tok);
	}

	std::string output;
	for (auto &str : output_code)
		output += str;

	output_code.clear();
	input_buffer.clear();
	input_buffer_charp = 0;

	return output;
}

