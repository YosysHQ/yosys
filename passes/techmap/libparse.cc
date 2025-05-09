/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "libparse.h"
#include <stdlib.h>
#include <string.h>

#include <istream>
#include <fstream>
#include <iostream>
#include <sstream>

#ifndef FILTERLIB
#include "kernel/log.h"
#endif

using namespace Yosys;

#ifndef FILTERLIB

LibertyAstCache LibertyAstCache::instance;

std::shared_ptr<const LibertyAst> LibertyAstCache::cached_ast(const std::string &fname)
{
	auto it = cached.find(fname);
	if (it == cached.end())
		return nullptr;
	if (verbose)
		log("Using cached data for liberty file `%s'\n", fname.c_str());
	return it->second;
}

void LibertyAstCache::parsed_ast(const std::string &fname, const std::shared_ptr<const LibertyAst> &ast)
{
	auto it = cache_path.find(fname);
	bool should_cache = it == cache_path.end() ? cache_by_default : it->second;
	if (!should_cache)
		return;
	if (verbose)
		log("Caching data for liberty file `%s'\n", fname.c_str());
	cached.emplace(fname, ast);
}

#endif

bool LibertyInputStream::extend_buffer_once()
{
	if (eof)
		return false;

	// To support unget we leave the last already read character in the buffer
	if (buf_pos > 1) {
		size_t move_pos = buf_pos - 1;
		memmove(buffer.data(), buffer.data() + move_pos, buf_end - move_pos);
		buf_pos -= move_pos;
		buf_end -= move_pos;
	}

	const size_t chunk_size = 4096;
	if (buffer.size() < buf_end + chunk_size) {
		buffer.resize(buf_end + chunk_size);
	}

	size_t read_size = f.rdbuf()->sgetn((char *)buffer.data() + buf_end, chunk_size);
	buf_end += read_size;
	if (read_size < chunk_size)
		eof = true;
	return read_size != 0;
}

bool LibertyInputStream::extend_buffer_at_least(size_t size) {
	while (buffered_size() < size) {
		if (!extend_buffer_once())
			return false;
	}
	return true;
}

int LibertyInputStream::get_cold()
{
	if (buf_pos == buf_end) {
		if (!extend_buffer_at_least())
			return EOF;
	}

	int c = buffer[buf_pos];
	buf_pos += 1;
	return c;
}

int LibertyInputStream::peek_cold(size_t offset)
{
	if (buf_pos + offset >= buf_end) {
		if (!extend_buffer_at_least(offset + 1))
			return EOF;
	}

	return buffer[buf_pos + offset];
}

LibertyAst::~LibertyAst()
{
	for (auto child : children)
		delete child;
	children.clear();
}

const LibertyAst *LibertyAst::find(std::string name) const
{
	for (auto child : children)
		if (child->id == name)
			return child;
	return NULL;
}

void LibertyAst::dump(FILE *f, sieve &blacklist, sieve &whitelist, std::string indent, std::string path, bool path_ok) const
{
	if (whitelist.count(path + "/*") > 0)
		path_ok = true;

	path += "/" + id;

	if (blacklist.count(id) > 0 || blacklist.count(path) > 0)
		return;
	if (whitelist.size() > 0 && whitelist.count(id) == 0 && whitelist.count(path) == 0 && !path_ok) {
		fprintf(stderr, "Automatically added to blacklist: %s\n", path.c_str());
		blacklist.insert(id);
		return;
	}

	fprintf(f, "%s%s", indent.c_str(), id.c_str());
	if (!args.empty() || !children.empty()) {
		fprintf(f, "(");
		for (size_t i = 0; i < args.size(); i++)
			fprintf(f, "%s%s", i > 0 ? ", " : "", args[i].c_str());
		fprintf(f, ")");
	}
	if (!value.empty())
		fprintf(f, " : %s", value.c_str());
	if (!children.empty()) {
		fprintf(f, " {\n");
		for (size_t i = 0; i < children.size(); i++)
			children[i]->dump(f, blacklist, whitelist, indent + "  ", path, path_ok);
		fprintf(f, "%s}\n", indent.c_str());
	} else
		fprintf(f, " ;\n");
}

#ifndef FILTERLIB
// https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
LibertyExpression LibertyExpression::parse(Lexer &s, int min_prio) {
	if (s.empty())
		return LibertyExpression{};

	char c = s.peek();
	auto lhs = LibertyExpression{};

	while (isspace(c)) {
		if (s.empty())
			return lhs;
		s.next();
		c = s.peek();
	}

	if (isalpha(c)) { // pin
		lhs.kind = Kind::PIN;
		lhs.name = s.pin();
	} else if (c == '(') { // parens
		s.next();
		lhs = parse(s);
		if (s.peek() != ')') {
			log_warning("expected ')' instead of '%c' while parsing Liberty expression '%s'\n", s.peek(), s.full_expr().c_str());
			return lhs;
		}
		s.next();
	} else if (c == '!') { // prefix NOT
		s.next();
		lhs.kind = Kind::NOT;
		lhs.children.push_back(parse(s, 7));
	} else {
		log_warning("unrecognised character '%c' while parsing Liberty expression '%s'\n", c, s.full_expr().c_str());
		return lhs;
	}

	while (true) {
		if (s.empty())
			break;
		
		c = s.peek();

		while (isspace(c)) {
			if (s.empty())
				return lhs;
			s.next();
			c = s.peek();
		}

		if (c == '\'') { // postfix NOT
			if (min_prio > 7)
				break;
			s.next();

			auto n = LibertyExpression{};
			n.kind = Kind::NOT;
			n.children.push_back(lhs);
			lhs = std::move(n);

			continue;
		} else if (c == '^') { // infix XOR
			if (min_prio > 5)
				break;
			s.next();

			auto rhs = parse(s, 6);
			auto n = LibertyExpression{};
			n.kind = Kind::XOR;
			n.children.push_back(lhs);
			n.children.push_back(rhs);
			lhs = std::move(n);

			continue;
		} else if (c == '&' || c == '*') { // infix AND
			// technically space should be considered infix AND. it seems rare in practice.
			if (min_prio > 3)
				break;
			s.next();

			auto rhs = parse(s, 4);
			auto n = LibertyExpression{};
			n.kind = Kind::AND;
			n.children.push_back(lhs);
			n.children.push_back(rhs);
			lhs = std::move(n);

			continue;
		} else if (c == '+' || c == '|') { // infix OR
			if (min_prio > 1)
				break;
			s.next();

			auto rhs = parse(s, 2);
			auto n = LibertyExpression{};
			n.kind = Kind::OR;
			n.children.push_back(lhs);
			n.children.push_back(rhs);
			lhs = std::move(n);

			continue;
		}
		break;
	}

	return lhs;
}

void LibertyExpression::get_pin_names(pool<std::string>& names) {
	if (kind == Kind::PIN) {
		names.insert(name);
	} else {
		for (auto& child : children)
			child.get_pin_names(names);
	}
}

bool LibertyExpression::eval(dict<std::string, bool>& values) {
	bool result = false;
	switch (kind) {
	case Kind::AND:
		result = true;
		for (auto& child : children)
			result &= child.eval(values);
		return result;
	case Kind::OR:
		result = false;
		for (auto& child : children)
			result |= child.eval(values);
		return result;
	case Kind::NOT:
		log_assert(children.size() == 1);
		return !children[0].eval(values);
	case Kind::XOR:
		result = false;
		for (auto& child : children)
			result ^= child.eval(values);
		return result;
	case Kind::PIN:
		return values.at(name);
	case Kind::EMPTY:
		log_assert(false);
	}
	return false;
}
#endif

int LibertyParser::lexer(std::string &str)
{
	int c;

	// eat whitespace
	do {
		c = f.get();
	} while (c == ' ' || c == '\t' || c == '\r');

	// search for identifiers, numbers, plus or minus.
	if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '_' || c == '-' || c == '+' || c == '.') {
		f.unget();
		size_t i = 1;
		while (true) {
			c = f.peek(i);
			if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '_' || c == '-' || c == '+' || c == '.')
				i += 1;
			else
				break;
		}
		str.clear();
		str.append(f.buffered_data(), f.buffered_data() + i);
		f.consume(i);

		if (str == "+" || str == "-") {
			/* Single operator is not an identifier */
			// fprintf(stderr, "LEX: char >>%s<<\n", str.c_str());
			return str[0];
		}
		else {
			// fprintf(stderr, "LEX: identifier >>%s<<\n", str.c_str());
			return 'v';
		}
	}

	// if it wasn't an identifer, number of array range,
	// maybe it's a string?
	if (c == '"') {
		size_t i = 0;
		while (true) {
			c = f.peek(i);
			line += (c == '\n');
			if (c != '"')
				i += 1;
			else
				break;
		}
		str.clear();
#ifdef FILTERLIB
		f.unget();
		str.append(f.buffered_data(), f.buffered_data() + i + 2);
		f.consume(i + 2);
#else
		str.append(f.buffered_data(), f.buffered_data() + i);
		f.consume(i + 1);
#endif
		return 'v';
	}

	// if it wasn't a string, perhaps it's a comment or a forward slash?
	if (c == '/') {
		c = f.get();
		if (c == '*') {         // start of '/*' block comment
			int last_c = 0;
			while (c > 0 && (last_c != '*' || c != '/')) {
				last_c = c;
				c = f.get();
				if (c == '\n')
					line++;
			}
			return lexer(str);
		} else if (c == '/') {  // start of '//' line comment
			while (c > 0 && c != '\n')
				c = f.get();
			line++;
			return lexer(str);
		}
		f.unget();
		// fprintf(stderr, "LEX: char >>/<<\n");
		return '/';             // a single '/' charater.
	}

	// check for a backslash
	if (c == '\\') {
		c = f.get();		
		if (c == '\r')
			c = f.get();
		if (c == '\n') {
			line++;
			return lexer(str);
		}
		f.unget();
		return '\\';
	}

	// check for a new line
	if (c == '\n') {
		line++;
		return 'n';
	}

	// anything else, such as ';' will get passed
	// through as literal items.

	// if (c >= 32 && c < 255)
	// 	fprintf(stderr, "LEX: char >>%c<<\n", c);
	// else
	// 	fprintf(stderr, "LEX: char %d\n", c);
	return c;
}

void LibertyParser::report_unexpected_token(int tok)
{
	std::string eReport;
	switch(tok)
	{
	case 'n':
		error("Unexpected newline.");
		break;
	case '[':
	case ']':
	case '}':
	case '{':
	case '\"':
	case ':':
		eReport = "Unexpected '";
		eReport += static_cast<char>(tok);
		eReport += "'.";
		error(eReport);
		break;
	case EOF:
		error("Unexpected end of file");
		break;
	default:
		eReport = "Unexpected token: ";
		eReport += static_cast<char>(tok);
		error(eReport);
	}
}

// FIXME: the AST needs to be extended to store
//        these vector ranges.
void LibertyParser::parse_vector_range(int tok)
{
	// parse vector range [A] or [A:B]
	std::string arg;
	tok = lexer(arg);
	if (tok != 'v')
	{
		// expected a vector array index
		error("Expected a number.");
	}
	else
	{
		// fixme: check for number A
	}
	tok = lexer(arg);
	// optionally check for : in case of [A:B]
	// if it isn't we just expect ']'
	// as we have [A]
	if (tok == ':')
	{
		tok = lexer(arg);
		if (tok != 'v')
		{
			// expected a vector array index
			error("Expected a number.");
		}
		else
		{
			// fixme: check for number B
			tok = lexer(arg);
		}
	}
	// expect a closing bracket of array range
	if (tok != ']')
	{
		error("Expected ']' on array range.");
	}
}

LibertyAst *LibertyParser::parse(bool top_level)
{
	std::string str;

	int tok = lexer(str);

	// there are liberty files in the wild that
	// have superfluous ';' at the end of
	// a  { ... }. We simply ignore a ';' here.
	// and get to the next statement.

	while ((tok == 'n') || (tok == ';'))
		tok = lexer(str);

	if (tok == EOF) {
		if (top_level)
			return NULL;
		report_unexpected_token(tok);
	}

	if (tok == '}')
		return NULL;

	if (tok != 'v') {
		report_unexpected_token(tok);	
	}

	LibertyAst *ast = new LibertyAst;
	ast->id = str;

	while (1)
	{
		tok = lexer(str);

		// allow both ';' and new lines to 
		// terminate a statement.
		if ((tok == ';') || (tok == 'n'))
			break;

		if (tok == ':' && ast->value.empty()) {
			tok = lexer(ast->value);
			if (tok == 'v') {
				tok = lexer(str);
				if (tok == '[') {
					parse_vector_range(tok);
					tok = lexer(str);
				}
			}
			while (tok == '+' || tok == '-' || tok == '*' || tok == '/' || tok == '!') {
				ast->value += tok;
				tok = lexer(str);
				if (tok != 'v')
					error();
				ast->value += str;
				tok = lexer(str);
			}
			
			// In a liberty file, all key : value pairs should end in ';'
			// However, there are some liberty files in the wild that
			// just have a newline. We'll be kind and accept a newline
			// instead of the ';' too..
			if ((tok == ';') || (tok == 'n'))
				break;
			else
				error();
			continue;
		}

		if (tok == '(') {
			while (1) {
				std::string arg;
				tok = lexer(arg);
				if (tok == ',')
					continue;
				if (tok == ')')
					break;
				
				if (tok == '[')
				{
					parse_vector_range(tok);
					continue;           
				}
				if (tok == 'n')
					continue;
				if (tok != 'v') {
					report_unexpected_token(tok);
				}
				ast->args.push_back(arg);
			}
			continue;
		}

		if (tok == '{') {
			bool terminated = false;
			while (1) {
				LibertyAst *child = parse(false);
				if (child == NULL) {
					terminated = true;
					break;
				}
				ast->children.push_back(child);
			}
			if (!terminated) {
				report_unexpected_token(EOF);
			}
			break;
		}

		report_unexpected_token(tok);
	}

	return ast;
}

#ifndef FILTERLIB

void LibertyParser::error() const
{
	log_error("Syntax error in liberty file on line %d.\n", line);
}

void LibertyParser::error(const std::string &str) const
{
	std::stringstream ss;
	ss << "Syntax error in liberty file on line " << line << ".\n";
	ss << "  " << str << "\n";
	log_error("%s", ss.str().c_str());
}

#else

void LibertyParser::error() const
{
	fprintf(stderr, "Syntax error in liberty file on line %d.\n", line);
	exit(1);
}

void LibertyParser::error(const std::string &str) const
{
	std::stringstream ss;
	ss << "Syntax error in liberty file on line " << line << ".\n";
	ss << "  " << str << "\n";
	printf("%s", ss.str().c_str());
	exit(1);
}

/**** BEGIN: http://svn.clairexen.net/tools/trunk/examples/check.h ****/

#define CHECK_NV(result, check)                                      \
   do {                                                              \
	 auto _R = (result);                                             \
	 if (!(_R check)) {                                              \
	   fprintf(stderr, "Error from '%s' (%ld %s) in %s:%d.\n",       \
			   #result, (long int)_R, #check, __FILE__, __LINE__);   \
	   abort();                                                      \
	 }                                                               \
   } while(0)

#define CHECK_COND(result)                                           \
   do {                                                              \
	 if (!(result)) {                                                \
	   fprintf(stderr, "Error from '%s' in %s:%d.\n",                \
			   #result, __FILE__, __LINE__);                         \
	   abort();                                                      \
	 }                                                               \
   } while(0)

/**** END: http://svn.clairexen.net/tools/trunk/examples/check.h ****/

const LibertyAst *find_non_null(const LibertyAst *node, const char *name)
{
	const LibertyAst *ret = node->find(name);
	if (ret == NULL)
		fprintf(stderr, "Error: expected to find `%s' node.\n", name);
	return ret;
}

std::string func2vl(std::string str)
{
	for (size_t pos = str.find_first_of("\" \t"); pos != std::string::npos; pos = str.find_first_of("\" \t")) {
		char c_left = pos > 0 ? str[pos-1] : ' ';
		char c_right = pos+1 < str.size() ? str[pos+1] : ' ';
		if (std::string("\" \t*+").find(c_left) != std::string::npos)
			str.erase(pos, 1);
		else if (std::string("\" \t*+").find(c_right) != std::string::npos)
			str.erase(pos, 1);
		else
			str[pos] = '*';
	}

	std::vector<size_t> group_start;
	for (size_t pos = 0; pos < str.size(); pos++) {
		if (str[pos] == '(')
			group_start.push_back(pos);
		if (str[pos] == ')' && group_start.size() > 0) {
			if (pos+1 < str.size() && str[pos+1] == '\'') {
				std::string group = str.substr(group_start.back(), pos-group_start.back()+1);
				str[group_start.back()] = '~';
				str.replace(group_start.back()+1, group.size(), group);
				pos++;
			}
			group_start.pop_back();
		}
		if (str[pos] == '\'' && pos > 0) {
			size_t start = str.find_last_of("()'*+^&| ", pos-1)+1;
			std::string group = str.substr(start, pos-start);
			str[start] = '~';
			str.replace(start+1, group.size(), group);
		}
		if (str[pos] == '*')
			str[pos] = '&';
		if (str[pos] == '+')
			str[pos] = '|';
	}

	return str;
}

void event2vl(const LibertyAst *ast, std::string &edge, std::string &expr)
{
	edge.clear();
	expr.clear();

	if (ast != NULL) {
		expr = func2vl(ast->value);
		if (expr.size() > 0 && expr[0] == '~')
			edge = "negedge " + expr.substr(1);
		else
			edge = "posedge " + expr;
	}
}

void clear_preset_var(std::string var, std::string type)
{
	if (type.find('L') != std::string::npos) {
		printf("      %s <= 0;\n", var.c_str());
		return;
	}
	if (type.find('H') != std::string::npos) {
		printf("      %s <= 1;\n", var.c_str());
		return;
	}
	if (type.find('T') != std::string::npos) {
		printf("      %s <= ~%s;\n", var.c_str(), var.c_str());
		return;
	}
	if (type.find('X') != std::string::npos) {
		printf("      %s <= 'bx;\n", var.c_str());
		return;
	}
}

void gen_verilogsim_cell(const LibertyAst *ast)
{
	if (ast->find("statetable") != NULL)
		return;

	CHECK_NV(ast->args.size(), == 1);
	printf("module %s (", ast->args[0].c_str());
	bool first = true;
	for (auto child : ast->children) {
		if (child->id != "pin")
			continue;
		CHECK_NV(child->args.size(), == 1);
		printf("%s%s", first ? "" : ", ", child->args[0].c_str());
		first = false;
	}
	printf(");\n");

	for (auto child : ast->children) {
		if (child->id != "ff" && child->id != "latch")
			continue;
		printf("  reg ");
		first = true;
		for (auto arg : child->args) {
			printf("%s%s", first ? "" : ", ", arg.c_str());
			first = false;
		}
		printf(";\n");
	}

	for (auto child : ast->children) {
		if (child->id != "pin")
			continue;
		CHECK_NV(child->args.size(), == 1);
		const LibertyAst *dir = find_non_null(child, "direction");
		const LibertyAst *func = child->find("function");
		printf("  %s %s;\n", dir->value.c_str(), child->args[0].c_str());
		if (func != NULL)
			printf("  assign %s = %s; // %s\n", child->args[0].c_str(), func2vl(func->value).c_str(), func->value.c_str());
	}

	for (auto child : ast->children)
	{
		if (child->id != "ff" || child->args.size() != 2)
			continue;

		std::string iq_var = child->args[0];
		std::string iqn_var = child->args[1];

		std::string clock_edge, clock_expr;
		event2vl(child->find("clocked_on"), clock_edge, clock_expr);

		std::string clear_edge, clear_expr;
		event2vl(child->find("clear"), clear_edge, clear_expr);

		std::string preset_edge, preset_expr;
		event2vl(child->find("preset"), preset_edge, preset_expr);

		std::string edge = "";
		if (!clock_edge.empty())
			edge += (edge.empty() ? "" : ", ") + clock_edge;
		if (!clear_edge.empty())
			edge += (edge.empty() ? "" : ", ") + clear_edge;
		if (!preset_edge.empty())
			edge += (edge.empty() ? "" : ", ") + preset_edge;

		if (edge.empty())
			continue;

		printf("  always @(%s) begin\n", edge.c_str());

		const char *else_prefix = "";
		if (!clear_expr.empty() && !preset_expr.empty()) {
			printf("    %sif ((%s) && (%s)) begin\n", else_prefix, clear_expr.c_str(), preset_expr.c_str());
			clear_preset_var(iq_var, find_non_null(child, "clear_preset_var1")->value);
			clear_preset_var(iqn_var, find_non_null(child, "clear_preset_var2")->value);
			printf("    end\n");
			else_prefix = "else ";
		}
		if (!clear_expr.empty()) {
			printf("    %sif (%s) begin\n", else_prefix, clear_expr.c_str());
			printf("      %s <= 0;\n", iq_var.c_str());
			printf("      %s <= 1;\n", iqn_var.c_str());
			printf("    end\n");
			else_prefix = "else ";
		}
		if (!preset_expr.empty()) {
			printf("    %sif (%s) begin\n", else_prefix, preset_expr.c_str());
			printf("      %s <= 1;\n", iq_var.c_str());
			printf("      %s <= 0;\n", iqn_var.c_str());
			printf("    end\n");
			else_prefix = "else ";
		}
		if (*else_prefix)
			printf("    %sbegin\n", else_prefix);
		std::string expr = find_non_null(child, "next_state")->value;
		printf("      // %s\n", expr.c_str());
		printf("      %s <= %s;\n", iq_var.c_str(), func2vl(expr).c_str());
		printf("      %s <= ~(%s);\n", iqn_var.c_str(), func2vl(expr).c_str());
		if (*else_prefix)
			printf("    end\n");

		printf("  end\n");
	}

	for (auto child : ast->children)
	{
		if (child->id != "latch" || child->args.size() != 2)
			continue;

		std::string iq_var = child->args[0];
		std::string iqn_var = child->args[1];

		std::string enable_edge, enable_expr;
		event2vl(child->find("enable"), enable_edge, enable_expr);

		std::string clear_edge, clear_expr;
		event2vl(child->find("clear"), clear_edge, clear_expr);

		std::string preset_edge, preset_expr;
		event2vl(child->find("preset"), preset_edge, preset_expr);

		printf("  always @* begin\n");

		const char *else_prefix = "";
		if (!clear_expr.empty() && !preset_expr.empty()) {
			printf("    %sif ((%s) && (%s)) begin\n", else_prefix, clear_expr.c_str(), preset_expr.c_str());
			clear_preset_var(iq_var, find_non_null(child, "clear_preset_var1")->value);
			clear_preset_var(iqn_var, find_non_null(child, "clear_preset_var2")->value);
			printf("    end\n");
			else_prefix = "else ";
		}
		if (!clear_expr.empty()) {
			printf("    %sif (%s) begin\n", else_prefix, clear_expr.c_str());
			printf("      %s <= 0;\n", iq_var.c_str());
			printf("      %s <= 1;\n", iqn_var.c_str());
			printf("    end\n");
			else_prefix = "else ";
		}
		if (!preset_expr.empty()) {
			printf("    %sif (%s) begin\n", else_prefix, preset_expr.c_str());
			printf("      %s <= 1;\n", iq_var.c_str());
			printf("      %s <= 0;\n", iqn_var.c_str());
			printf("    end\n");
			else_prefix = "else ";
		}
		if (!enable_expr.empty()) {
			printf("    %sif (%s) begin\n", else_prefix, enable_expr.c_str());
			std::string expr = find_non_null(child, "data_in")->value;
			printf("      %s <= %s;\n", iq_var.c_str(), func2vl(expr).c_str());
			printf("      %s <= ~(%s);\n", iqn_var.c_str(), func2vl(expr).c_str());
			printf("    end\n");
			else_prefix = "else ";
		}

		printf("  end\n");
	}

	printf("endmodule\n");
}

void gen_verilogsim(const LibertyAst *ast)
{
	CHECK_COND(ast->id == "library");

	for (auto child : ast->children)
		if (child->id == "cell" && !child->find("dont_use"))
			gen_verilogsim_cell(child);
}

void usage()
{
	fprintf(stderr, "Usage: filterlib [rules-file [liberty-file]]\n");
	fprintf(stderr, "   or: filterlib -verilogsim [liberty-file]\n");
	exit(1);
}

int main(int argc, char **argv)
{
	bool flag_verilogsim = false;
	std::set<std::string> whitelist, blacklist;

	if (argc > 3)
		usage();

	if (argc > 1)
	{
		if (!strcmp(argv[1], "-verilogsim"))
			flag_verilogsim = true;
		if (!strcmp(argv[1], "-") || !strcmp(argv[1], "-verilogsim"))
		{
			whitelist.insert("/library");
			whitelist.insert("/library/cell");
			whitelist.insert("/library/cell/area");
			whitelist.insert("/library/cell/cell_footprint");
			whitelist.insert("/library/cell/dont_touch");
			whitelist.insert("/library/cell/dont_use");
			whitelist.insert("/library/cell/ff");
			whitelist.insert("/library/cell/ff/*");
			whitelist.insert("/library/cell/latch");
			whitelist.insert("/library/cell/latch/*");
			whitelist.insert("/library/cell/pin");
			whitelist.insert("/library/cell/pin/clock");
			whitelist.insert("/library/cell/pin/direction");
			whitelist.insert("/library/cell/pin/driver_type");
			whitelist.insert("/library/cell/pin/function");
			whitelist.insert("/library/cell/pin_opposite");
			whitelist.insert("/library/cell/pin/state_function");
			whitelist.insert("/library/cell/pin/three_state");
			whitelist.insert("/library/cell/statetable");
			whitelist.insert("/library/cell/statetable/*");
		}
		else
		{
			FILE *f = fopen(argv[1], "r");
			if (f == NULL) {
				fprintf(stderr, "Can't open rules file `%s'.\n", argv[1]);
				usage();
			}

			char buffer[1024];
			while (fgets(buffer, 1024, f) != NULL)
			{
				char mode = 0;
				std::string id;
				for (char *p = buffer; *p; p++)
				{
					if (*p == '-' || *p == '+') {
						if (mode != 0)
							goto syntax_error;
						mode = *p;
						continue;
					}
					if (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n' || *p == '#') {
						if (!id.empty()) {
							if (mode == '-')
								blacklist.insert(id);
							else
							if (mode == '+')
								whitelist.insert(id);
							else
								goto syntax_error;
						}
						id.clear();
						if (*p == '#')
							break;
						continue;
					}
					id += *p;
					continue;

				syntax_error:
					fprintf(stderr, "Syntax error in rules file:\n%s", buffer);
					exit(1);
				}
			}
		}
	}

	std::istream *f = &std::cin;

	if (argc == 3) {
		std::ifstream *ff = new std::ifstream;
		ff->open(argv[2]);
		if (ff->fail()) {
			delete ff;
			fprintf(stderr, "Can't open liberty file `%s'.\n", argv[2]);
			usage();
		}
		f = ff;
	}

	LibertyParser parser(*f);
	if (parser.ast) {
		if (flag_verilogsim)
			gen_verilogsim(parser.ast);
		else
			parser.ast->dump(stdout, blacklist, whitelist);
	}

	if (argc == 3)
		delete f;

	return 0;
}

#endif

