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

#include "preproc.h"
#include "verilog_frontend.h"
#include "kernel/log.h"
#include <assert.h>
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

struct macro_arg_t
{
	macro_arg_t(const std::string &name_, const char *default_value_)
		: name(name_),
		  has_default(default_value_ != nullptr),
		  default_value(default_value_ ? default_value_ : "")
	{}

	std::string name;
	bool        has_default;
	std::string default_value;
};

static bool all_white(const std::string &str)
{
	for (char c : str)
		if (!isspace(c))
			return false;
	return true;
}

struct arg_map_t
{
	arg_map_t()
	{}

	void add_arg(const std::string &name, const char *default_value)
	{
		if (find(name)) {
			log_error("Duplicate macro arguments with name `%s'.\n", name.c_str());
		}

		name_to_pos[name] = args.size();
		args.push_back(macro_arg_t(name, default_value));
	}

	// Find an argument by name; return nullptr if it doesn't exist. If pos is not null, write
	// the argument's position to it on success.
	const macro_arg_t *find(const std::string &name, int *pos = nullptr) const
	{
		auto it = name_to_pos.find(name);
		if (it == name_to_pos.end())
			return nullptr;

		if (pos) *pos = it->second;
		return &args[it->second];
	}

	// Construct the name for the local macro definition we use for the given argument
	// (something like macro_foobar_arg2). This doesn't include the leading backtick.
	static std::string str_token(const std::string &macro_name, int pos)
	{
		return stringf("macro_%s_arg%d", macro_name.c_str(), pos);
	}

	// Return definitions for the macro arguments (so that substituting in the macro body and
	// then performing macro expansion will do argument substitution properly).
	std::vector<std::pair<std::string, std::string>>
	get_vals(const std::string &macro_name, const std::vector<std::string> &arg_vals) const
	{
		std::vector<std::pair<std::string, std::string>> ret;
		for (int i = 0; i < GetSize(args); ++ i) {
			// The SystemVerilog rules are:
			//
			//   - If the call site specifies an argument and it's not whitespace, use
			//     it.
			//
			//   - Otherwise, if the argument has a default value, use it.
			//
			//   - Otherwise, if the call site specified whitespace, use that.
			//
			//   - Otherwise, error.
			const std::string *dflt = nullptr;
			if (args[i].has_default)
				dflt = &args[i].default_value;

			const std::string *given = nullptr;
			if (i < GetSize(arg_vals))
				given = &arg_vals[i];

			const std::string *val = nullptr;
			if (given && (! (dflt && all_white(*given))))
				val = given;
			else if (dflt)
				val = dflt;
			else if (given)
				val = given;
			else
				log_error("Cannot expand macro `%s by giving only %d argument%s "
				          "(argument %d has no default).\n",
				          macro_name.c_str(), GetSize(arg_vals),
				          (GetSize(arg_vals) == 1 ? "" : "s"), i + 1);

			assert(val);
			ret.push_back(std::make_pair(str_token(macro_name, i), * val));
		}
		return ret;
	}


	std::vector<macro_arg_t>   args;
	std::map<std::string, int> name_to_pos;
};

struct define_body_t
{
	define_body_t(const std::string &body, const arg_map_t *args = nullptr)
	  : body(body),
	    has_args(args != nullptr),
	    args(args ? *args : arg_map_t())
	{}

	std::string body;
	bool        has_args;
	arg_map_t   args;
};

define_map_t::define_map_t()
{
	add("YOSYS", "1");
}

// We must define this destructor here (rather than relying on the default), because we need to
// define it somewhere we've got a complete definition of define_body_t.
define_map_t::~define_map_t()
{}

void
define_map_t::add(const std::string &name, const std::string &txt, const arg_map_t *args)
{
	defines[name] = std::unique_ptr<define_body_t>(new define_body_t(txt, args));
}

void define_map_t::merge(const define_map_t &map)
{
	for (const auto &pr : map.defines) {
		// These contortions are so that we take a copy of each definition body in
		// map.defines.
		defines[pr.first] = std::unique_ptr<define_body_t>(new define_body_t(*pr.second));
	}
}

const define_body_t *define_map_t::find(const std::string &name) const
{
	auto it = defines.find(name);
	return (it == defines.end()) ? nullptr : it->second.get();
}

void define_map_t::erase(const std::string &name)
{
	defines.erase(name);
}

void define_map_t::clear()
{
	defines.clear();
}

void define_map_t::log() const
{
	for (auto &it : defines) {
		const std::string &name = it.first;
		const define_body_t &body = *it.second;
		Yosys::log("`define %s%s %s\n",
		           name.c_str(), body.has_args ? "()" : "", body.body.c_str());
	}
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

// Read tokens to get one argument (either a macro argument at a callsite or a default argument in a
// macro definition). Writes the argument to dest. Returns true if we finished with ')' (the end of
// the argument list); false if we finished with ','.
static bool read_argument(std::string &dest)
{
	skip_spaces();
	std::vector<char> openers;
	for (;;) {
		std::string tok = next_token(true);
		if (tok == ")") {
			if (openers.empty()) {
				while (dest.size() && (dest.back() == ' ' || dest.back() == '\t'))
					dest = dest.substr(0, dest.size() - 1);
				return true;
			}
			if (openers.back() != '(')
				log_error("Mismatched brackets in macro argument: %c and %c.\n",
				          openers.back(), tok[0]);

			openers.pop_back();
			dest += tok;
			continue;
		}
		if (tok == "]") {
			char opener = openers.empty() ? '(' : openers.back();
			if (opener != '[')
				log_error("Mismatched brackets in macro argument: %c and %c.\n",
				          opener, tok[0]);

			openers.pop_back();
			dest += tok;
			continue;
		}
		if (tok == "}") {
			char opener = openers.empty() ? '(' : openers.back();
			if (opener != '{')
				log_error("Mismatched brackets in macro argument: %c and %c.\n",
				          opener, tok[0]);

			openers.pop_back();
			dest += tok;
			continue;
		}

		if (tok == "," && openers.empty()) {
			return false;
		}

		if (tok == "(" || tok == "[" || tok == "{")
			openers.push_back(tok[0]);

		dest += tok;
	}
}

static bool try_expand_macro(define_map_t &defines, std::string &tok)
{
	if (tok == "`\"") {
		std::string literal("\"");
		// Expand string literal
		while (!input_buffer.empty()) {
			std::string ntok = next_token();
			if (ntok == "`\"") {
				insert_input(literal+"\"");
				return true;
			} else if (!try_expand_macro(defines, ntok)) {
					literal += ntok;
			}
		}
		return false; // error - unmatched `"
	}

	if (tok == "``") {
		// Swallow `` in macro expansion
		return true;
	}

	if (tok.size() <= 1 || tok[0] != '`')
		return false;

	// This token looks like a macro name (`foo).
	std::string macro_name = tok.substr(1);
	const define_body_t *body = defines.find(tok.substr(1));

	if (! body) {
		// Apparently not a name we know.
		return false;
	}

	std::string name = tok.substr(1);
	std::string skipped_spaces = skip_spaces();
	tok = next_token(false);
	if (body->has_args) {
		if (tok != "(") {
			if (tok.size() == 1 && iscntrl(tok[0])) {
				char buf[5];
				snprintf(buf, sizeof(buf), "\\x%02x", tok[0]);
				tok = buf;
			}
			log_error("Expected to find '(' to begin macro arguments for '%s', but instead found '%s'\n",
				name.c_str(), tok.c_str());
		}
		std::vector<std::string> args;
		bool done = false;
		while (!done) {
			std::string arg;
			done = read_argument(arg);
			args.push_back(arg);
		}
		for (const auto &pr : body->args.get_vals(name, args)) {
			defines.add(pr.first, pr.second);
		}
	} else {
		insert_input(tok);
		insert_input(skipped_spaces);
	}
	insert_input(body->body);
	return true;
}

// Read the arguments for a `define preprocessor directive with formal arguments. This is called
// just after reading the token containing "(". Returns the number of newlines to emit afterwards to
// keep line numbers in sync, together with the map from argument name to data (pos and default
// value).
static std::pair<int, arg_map_t>
read_define_args()
{
	// Each argument looks like one of the following:
	//
	//     identifier
	//     identifier = default_text
	//     identifier =
	//
	// The first example is an argument with no default value. The second is an argument whose
	// default value is default_text. The third is an argument with default value the empty
	// string.

	int newline_count = 0;
	arg_map_t args;

	// FSM state.
	//
	//   0: At start of identifier
	//   1: After identifier (stored in arg_name)
	//   2: After closing paren
	int state = 0;

	std::string arg_name, default_val;

	skip_spaces();
	for (;;) {
		if (state == 2)
			// We've read the closing paren.
			break;

		std::string tok = next_token();

		// Cope with escaped EOLs
		if (tok == "\\") {
			char ch = next_char();
			if (ch == '\n') {
				// Eat the \, the \n and any trailing space and keep going.
				skip_spaces();
				continue;
			} else {
				// There aren't any other situations where a backslash makes sense.
				log_error("Backslash in macro arguments (not at end of line).\n");
			}
		}

		switch (state) {
		case 0:
			// At start of argument. If the token is ')', we've presumably just seen
			// something like "`define foo() ...". Set state to 2 to finish. Otherwise,
			// the token should be a valid simple identifier, but we'll allow anything
			// here.
			if (tok == ")") {
				state = 2;
			} else {
				arg_name = tok;
				state = 1;
			}
			skip_spaces();
			break;

		case 1:
			// After argument. The token should either be an equals sign or a comma or
			// closing paren.
			if (tok == "=") {
				std::string default_val;
				//Read an argument into default_val and set state to 2 if we're at
				// the end; 0 if we hit a comma.
				state = read_argument(default_val) ? 2 : 0;
				args.add_arg(arg_name, default_val.c_str());
				skip_spaces();
				break;
			}
			if (tok == ",") {
				// Take the identifier as an argument with no default value.
				args.add_arg(arg_name, nullptr);
				state = 0;
				skip_spaces();
				break;
			}
			if (tok == ")") {
				// As with comma, but set state to 2 (end of args)
				args.add_arg(arg_name, nullptr);
				state = 2;
				skip_spaces();
				break;
			}
			log_error("Trailing contents after identifier in macro argument `%s': "
				  "expected '=', ',' or ')'.\n",
				  arg_name.c_str());

		default:
			// The only FSM states are 0-2 and we dealt with 2 at the start of the loop.
			log_assert(false);
		}
	}

	return std::make_pair(newline_count, args);
}

// Read a `define preprocessor directive. This is called just after reading the token containing
// "`define".
static void
read_define(const std::string &filename,
            define_map_t      &defines_map,
            define_map_t      &global_defines_cache)
{
	std::string name, value;
	arg_map_t args;

	skip_spaces();
	name = next_token(true);

	bool here_doc_mode = false;
	int newline_count = 0;

	// The FSM state starts at 0. If it sees space (or enters here_doc_mode), it assumes this is
	// a macro without formal arguments and jumps to state 1.
	//
	// In state 0, if it sees an opening parenthesis, it assumes this is a macro with formal
	// arguments. It reads the arguments with read_define_args() and then jumps to state 2.
	//
	// In states 1 or 2, the FSM reads tokens to the end of line (or end of here_doc): this is
	// the body of the macro definition.
	int state = 0;

	if (skip_spaces() != "")
		state = 1;

	for (;;) {
		std::string tok = next_token();
		if (tok.empty())
			break;

		// printf("define-tok: >>%s<<\n", tok != "\n" ? tok.c_str() : "NEWLINE");

		if (tok == "\"\"\"") {
			here_doc_mode = !here_doc_mode;
			continue;
		}

		if (state == 0 && tok == "(") {
			auto pr = read_define_args();
			newline_count += pr.first;
			args = pr.second;

			state = 2;
			continue;
		}

		// This token isn't an opening parenthesis immediately following the macro name, so
		// it's presumably at or after the start of the macro body. If state isn't already 2
		// (which would mean we'd parsed an argument list), set it to 1.
		if (state == 0) {
			state = 1;
		}

		if (tok == "\n") {
			if (here_doc_mode) {
				value += " ";
				newline_count++;
			} else {
				return_char('\n');
				break;
			}
			continue;
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
			continue;
		}

		// Is this token the name of a macro argument? If so, replace it with a magic symbol
		// that we'll replace with the argument value.
		int arg_pos;
		if (args.find(tok, &arg_pos)) {
			value += '`' + args.str_token(name, arg_pos);
			continue;
		}

		// This token is nothing special. Insert it verbatim into the macro body.
		value += tok;
	}

	// Append some newlines so that we don't mess up line counts in error messages.
	while (newline_count-- > 0)
		return_char('\n');

	if (strchr("abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ$0123456789", name[0])) {
		// printf("define: >>%s<< -> >>%s<<\n", name.c_str(), value.c_str());
		defines_map.add(name, value, (state == 2) ? &args : nullptr);
		global_defines_cache.add(name, value, (state == 2) ? &args : nullptr);
	} else {
		log_file_error(filename, 0, "Invalid name for macro definition: >>%s<<.\n", name.c_str());
	}
}

std::string
frontend_verilog_preproc(std::istream                 &f,
                         std::string                   filename,
                         const define_map_t           &pre_defines,
                         define_map_t                 &global_defines_cache,
                         const std::list<std::string> &include_dirs)
{
	define_map_t defines;
	defines.merge(pre_defines);
	defines.merge(global_defines_cache);

	std::vector<std::string> filename_stack;
	// We are inside pass_level levels of satisfied ifdefs, and then within
	// fail_level levels of unsatisfied ifdefs.  The unsatisfied ones are
	// always within satisfied ones — even if some condition within is true,
	// the parent condition failing renders it moot.
	int ifdef_fail_level = 0;
	int ifdef_pass_level = 0;
	// For the outermost unsatisfied ifdef, true iff that ifdef already
	// had a satisfied branch, and further elsif/else branches should be
	// considered unsatisfied even if the condition is true.
	// Meaningless if ifdef_fail_level == 0.
	bool ifdef_already_satisfied = false;

	output_code.clear();
	input_buffer.clear();
	input_buffer_charp = 0;

	input_file(f, filename);

	while (!input_buffer.empty())
	{
		std::string tok = next_token();
		// printf("token: >>%s<<\n", tok != "\n" ? tok.c_str() : "NEWLINE");

		if (tok == "`endif") {
			if (ifdef_fail_level > 0)
				ifdef_fail_level--;
			else if (ifdef_pass_level > 0)
				ifdef_pass_level--;
			else
				log_error("Found %s outside of macro conditional branch!\n", tok.c_str());
			continue;
		}

		if (tok == "`else") {
			if (ifdef_fail_level == 0) {
				if (ifdef_pass_level == 0)
					log_error("Found %s outside of macro conditional branch!\n", tok.c_str());
				ifdef_pass_level--;
				ifdef_fail_level = 1;
				ifdef_already_satisfied = true;
			} else if (ifdef_fail_level == 1 && !ifdef_already_satisfied) {
				ifdef_fail_level = 0;
				ifdef_pass_level++;
				ifdef_already_satisfied = true;
			}
			continue;
		}

		if (tok == "`elsif") {
			skip_spaces();
			std::string name = next_token(true);
			if (ifdef_fail_level == 0) {
				if (ifdef_pass_level == 0)
					log_error("Found %s outside of macro conditional branch!\n", tok.c_str());
				ifdef_pass_level--;
				ifdef_fail_level = 1;
				ifdef_already_satisfied = true;
			} else if (ifdef_fail_level == 1 && !ifdef_already_satisfied && defines.find(name)) {
				ifdef_fail_level = 0;
				ifdef_pass_level++;
				ifdef_already_satisfied = true;
			}
			continue;
		}

		if (tok == "`ifdef") {
			skip_spaces();
			std::string name = next_token(true);
			if (ifdef_fail_level > 0 || !defines.find(name)) {
				ifdef_fail_level++;
			} else {
				ifdef_pass_level++;
				ifdef_already_satisfied = true;
			}
			if (ifdef_fail_level == 1)
				ifdef_already_satisfied = false;
			continue;
		}

		if (tok == "`ifndef") {
			skip_spaces();
			std::string name = next_token(true);
			if (ifdef_fail_level > 0 || defines.find(name)) {
				ifdef_fail_level++;
			} else {
				ifdef_pass_level++;
				ifdef_already_satisfied = true;
			}
			if (ifdef_fail_level == 1)
				ifdef_already_satisfied = false;
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
			while (try_expand_macro(defines, fn)) {
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
			read_define(filename, defines, global_defines_cache);
			continue;
		}

		if (tok == "`undef") {
			std::string name;
			skip_spaces();
			name = next_token(true);
			// printf("undef: >>%s<<\n", name.c_str());
			defines.erase(name);
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
			defines.clear();
			global_defines_cache.clear();
			continue;
		}

		if (try_expand_macro(defines, tok))
			continue;

		output_code.push_back(tok);
	}

	if (ifdef_fail_level > 0 || ifdef_pass_level > 0) {
		log_error("Unterminated preprocessor conditional!\n");
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
