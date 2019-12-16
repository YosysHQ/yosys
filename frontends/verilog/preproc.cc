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
 *  directives are handled by the lexer (see verilog_lexer.l).
 *
 */

#include "verilog_frontend.h"
#include "kernel/log.h"
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

YOSYS_NAMESPACE_BEGIN
using namespace VERILOG_FRONTEND;

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
	if (input_buffer.empty())
		return 0;

	log_assert(input_buffer_charp <= input_buffer.front().size());
	if (input_buffer_charp == input_buffer.front().size()) {
		input_buffer_charp = 0;
		input_buffer.pop_front();
		return next_char();
	}

	char ch = input_buffer.front()[input_buffer_charp++];
	return ch == '\r' ? next_char() : ch;
}

static std::string skip_spaces()
{
	std::string spaces;
	while (1) {
		char ch = next_char();
		if (ch == 0)
			break;
		if (ch != ' ' && ch != '\t') {
			return_char(ch);
			break;
		}
		spaces += ch;
	}
	return spaces;
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
		if (token == "\"\"" && (ch = next_char()) != 0) {
			if (ch == '"')
				token += ch;
			else
				return_char(ch);
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
		if (ch == '`' || strchr(ok, ch) != NULL)
		{
			char first = ch;
			ch = next_char();
			if (first == '`' && (ch == '"' || ch == '`')) {
				token += ch;
			} else do {
					if (strchr(ok, ch) == NULL) {
						return_char(ch);
						break;
					}
					token += ch;
				} while ((ch = next_char()) != 0);
		}
	}
	return token;
}

static void input_file(std::istream &f, std::string filename)
{
	char buffer[513];
	int rc;

	insert_input("");
	auto it = input_buffer.begin();

	input_buffer.insert(it, "`file_push \"" + filename + "\"\n");
	while ((rc = readsome(f, buffer, sizeof(buffer)-1)) > 0) {
		buffer[rc] = 0;
		input_buffer.insert(it, buffer);
	}
	input_buffer.insert(it, "\n`file_pop\n");
}


static bool try_expand_macro(std::set<std::string> &defines_with_args,
			     std::map<std::string, std::string> &defines_map,
			     std::string &tok
				    )
{
	if (tok == "`\"") {
		std::string literal("\"");
		// Expand string literal
		while (!input_buffer.empty()) {
			std::string ntok = next_token();
			if (ntok == "`\"") {
				insert_input(literal+"\"");
				return true;
			} else if (!try_expand_macro(defines_with_args, defines_map, ntok)) {
					literal += ntok;
			}
		}
		return false; // error - unmatched `"
	} else if (tok.size() > 1 && tok[0] == '`' && defines_map.count(tok.substr(1)) > 0) {
			std::string name = tok.substr(1);
			// printf("expand: >>%s<< -> >>%s<<\n", name.c_str(), defines_map[name].c_str());
			std::string skipped_spaces = skip_spaces();
			tok = next_token(false);
			if (tok == "(" && defines_with_args.count(name) > 0) {
				int level = 1;
				std::vector<std::string> args;
				args.push_back(std::string());
				while (1)
				{
					skip_spaces();
					tok = next_token(true);
					if (tok == ")" || tok == "}" || tok == "]")
						level--;
					if (level == 0)
						break;
					if (level == 1 && tok == ",")
						args.push_back(std::string());
					else
						args.back() += tok;
					if (tok == "(" || tok == "{" || tok == "[")
						level++;
				}
				for (int i = 0; i < GetSize(args); i++)
					defines_map[stringf("macro_%s_arg%d", name.c_str(), i+1)] = args[i];
			} else {
				insert_input(tok);
				insert_input(skipped_spaces);
			}
			insert_input(defines_map[name]);
			return true;
	} else if (tok == "``") {
		// Swallow `` in macro expansion
		return true;
	} else return false;
}

std::string frontend_verilog_preproc(std::istream &f, std::string filename, const std::map<std::string, std::string> &pre_defines_map,
		dict<std::string, std::pair<std::string, bool>> &global_defines_cache, const std::list<std::string> &include_dirs)
{
	std::set<std::string> defines_with_args;
	std::map<std::string, std::string> defines_map(pre_defines_map);
	std::vector<std::string> filename_stack;
	int ifdef_fail_level = 0;
	bool in_elseif = false;

	output_code.clear();
	input_buffer.clear();
	input_buffer_charp = 0;

	input_file(f, filename);

	defines_map["YOSYS"] = "1";
	defines_map[formal_mode ? "FORMAL" : "SYNTHESIS"] = "1";

	for (auto &it : pre_defines_map)
		defines_map[it.first] = it.second;

	for (auto &it : global_defines_cache) {
		if (it.second.second)
			defines_with_args.insert(it.first);
		defines_map[it.first] = it.second.first;
	}

	while (!input_buffer.empty())
	{
		std::string tok = next_token();
		// printf("token: >>%s<<\n", tok != "\n" ? tok.c_str() : "NEWLINE");

		if (tok == "`endif") {
			if (ifdef_fail_level > 0)
				ifdef_fail_level--;
			if (ifdef_fail_level == 0)
				in_elseif = false;
			continue;
		}

		if (tok == "`else") {
			if (ifdef_fail_level == 0)
				ifdef_fail_level = 1;
			else if (ifdef_fail_level == 1 && !in_elseif)
				ifdef_fail_level = 0;
			continue;
		}

		if (tok == "`elsif") {
			skip_spaces();
			std::string name = next_token(true);
			if (ifdef_fail_level == 0)
				ifdef_fail_level = 1, in_elseif = true;
			else if (ifdef_fail_level == 1 && defines_map.count(name) != 0)
				ifdef_fail_level = 0, in_elseif = true;
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
			while (try_expand_macro(defines_with_args, defines_map, fn)) {
				fn = next_token();
			}
			while (1) {
				size_t pos = fn.find('"');
				if (pos == std::string::npos)
					break;
				if (pos == 0)
					fn = fn.substr(1);
				else
					fn = fn.substr(0, pos) + fn.substr(pos+1);
			}
			std::ifstream ff;
			ff.clear();
			std::string fixed_fn = fn;
			ff.open(fixed_fn.c_str());

			bool filename_path_sep_found;
			bool fn_relative;
#ifdef _WIN32
			// Both forward and backslash are acceptable separators on Windows.
			filename_path_sep_found = (filename.find_first_of("/\\") != std::string::npos);
			// Easier just to invert the check for an absolute path (e.g. C:\ or C:/)
			fn_relative = !(fn[1] == ':' && (fn[2] == '/' || fn[2] == '\\'));
#else
			filename_path_sep_found = (filename.find('/') != std::string::npos);
			fn_relative = (fn[0] != '/');
#endif

			if (ff.fail() && fn.size() > 0 && fn_relative && filename_path_sep_found) {
				// if the include file was not found, it is not given with an absolute path, and the
				// currently read file is given with a path, then try again relative to its directory
				ff.clear();
#ifdef _WIN32
				fixed_fn = filename.substr(0, filename.find_last_of("/\\")+1) + fn;
#else
				fixed_fn = filename.substr(0, filename.rfind('/')+1) + fn;
#endif
				ff.open(fixed_fn);
			}
			if (ff.fail() && fn.size() > 0 && fn_relative) {
				// if the include file was not found and it is not given with an absolute path, then
				// search it in the include path
				for (auto incdir : include_dirs) {
					ff.clear();
					fixed_fn = incdir + '/' + fn;
					ff.open(fixed_fn);
					if (!ff.fail()) break;
				}
			}
			if (ff.fail()) {
				output_code.push_back("`file_notfound " + fn);
			} else {
				input_file(ff, fixed_fn);
				yosys_input_files.insert(fixed_fn);
			}
			continue;
		}

		if (tok == "`file_push") {
			skip_spaces();
			std::string fn = next_token(true);
			if (!fn.empty() && fn.front() == '"' && fn.back() == '"')
				fn = fn.substr(1, fn.size()-2);
			output_code.push_back(tok + " \"" + fn + "\"");
			filename_stack.push_back(filename);
			filename = fn;
			continue;
		}

		if (tok == "`file_pop") {
			output_code.push_back(tok);
			filename = filename_stack.back();
			filename_stack.pop_back();
			continue;
		}

		if (tok == "`define") {
			std::string name, value;
			std::map<std::string, int> args;
			skip_spaces();
			name = next_token(true);
			bool here_doc_mode = false;
			int newline_count = 0;
			int state = 0;
			if (skip_spaces() != "")
				state = 3;
			while (!tok.empty()) {
				tok = next_token();
				if (tok == "\"\"\"") {
					here_doc_mode = !here_doc_mode;
					continue;
				}
				if (state == 0 && tok == "(") {
					state = 1;
					skip_spaces();
				} else
				if (state == 1) {
					if (tok == ")")
						state = 2;
					else if (tok != ",") {
						int arg_idx = args.size()+1;
						args[tok] = arg_idx;
					}
					skip_spaces();
				} else {
					if (state != 2)
						state = 3;
					if (tok == "\n") {
						if (here_doc_mode) {
							value += " ";
							newline_count++;
						} else {
							return_char('\n');
							break;
						}
					} else
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
					if (args.count(tok) > 0)
						value += stringf("`macro_%s_arg%d", name.c_str(), args.at(tok));
					else
						value += tok;
				}
			}
			while (newline_count-- > 0)
				return_char('\n');
			if (strchr("abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ$0123456789", name[0])) {
				// printf("define: >>%s<< -> >>%s<<\n", name.c_str(), value.c_str());
				defines_map[name] = value;
				if (state == 2)
					defines_with_args.insert(name);
				else
					defines_with_args.erase(name);
				global_defines_cache[name] = std::pair<std::string, bool>(value, state == 2);
			} else {
				log_file_error(filename, 0, "Invalid name for macro definition: >>%s<<.\n", name.c_str());
			}
			continue;
		}

		if (tok == "`undef") {
			std::string name;
			skip_spaces();
			name = next_token(true);
			// printf("undef: >>%s<<\n", name.c_str());
			defines_map.erase(name);
			defines_with_args.erase(name);
			global_defines_cache.erase(name);
			continue;
		}

		if (tok == "`timescale") {
			skip_spaces();
			while (!tok.empty() && tok != "\n")
				tok = next_token(true);
			if (tok == "\n")
				return_char('\n');
			continue;
		}

		if (tok == "`resetall") {
			defines_map.clear();
			defines_with_args.clear();
			global_defines_cache.clear();
			continue;
		}

		if (try_expand_macro(defines_with_args, defines_map, tok))
			continue;

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

YOSYS_NAMESPACE_END
