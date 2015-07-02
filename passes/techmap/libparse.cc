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
 */

#include "libparse.h"
#include <stdlib.h>
#include <string.h>

#include <istream>
#include <fstream>
#include <iostream>

#ifndef FILTERLIB
#include "kernel/log.h"
#endif

using namespace Yosys;

std::set<std::string> LibertyAst::blacklist;
std::set<std::string> LibertyAst::whitelist;

LibertyAst::~LibertyAst()
{
	for (auto child : children)
		delete child;
	children.clear();
}

LibertyAst *LibertyAst::find(std::string name)
{
	for (auto child : children)
		if (child->id == name)
			return child;
	return NULL;
}

void LibertyAst::dump(FILE *f, std::string indent, std::string path, bool path_ok)
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
			children[i]->dump(f, indent + "  ", path, path_ok);
		fprintf(f, "%s}\n", indent.c_str());
	} else
		fprintf(f, " ;\n");
}

int LibertyParser::lexer(std::string &str)
{
	int c;

	do {
		c = f.get();
	} while (c == ' ' || c == '\t' || c == '\r');

	if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '_' || c == '-' || c == '+' || c == '.') {
		str = c;
		while (1) {
			c = f.get();
			if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '_' || c == '-' || c == '+' || c == '.')
				str += c;
			else
				break;
		}
		f.unget();
		// fprintf(stderr, "LEX: identifier >>%s<<\n", str.c_str());
		return 'v';
	}

	if (c == '"') {
		str = "";
		while (1) {
			c = f.get();
			if (c == '\n')
				line++;
			if (c == '"')
				break;
			str += c;
		}
		// fprintf(stderr, "LEX: string >>%s<<\n", str.c_str());
		return 'v';
	}

	if (c == '/') {
		c = f.get();
		if (c == '*') {
			int last_c = 0;
			while (c > 0 && (last_c != '*' || c != '/')) {
				last_c = c;
				c = f.get();
				if (c == '\n')
					line++;
			}
			return lexer(str);
		} else if (c == '/') {
			while (c > 0 && c != '\n')
				c = f.get();
			line++;
			return lexer(str);
		}
		f.unget();
		// fprintf(stderr, "LEX: char >>/<<\n");
		return '/';
	}

	if (c == '\\') {
		c = f.get();
		if (c == '\r')
			c = f.get();
		if (c == '\n')
			return lexer(str);
		f.unget();
		return '\\';
	}

	if (c == '\n') {
		line++;
		return ';';
	}

	// if (c >= 32 && c < 255)
	// 	fprintf(stderr, "LEX: char >>%c<<\n", c);
	// else
	// 	fprintf(stderr, "LEX: char %d\n", c);
	return c;
}

LibertyAst *LibertyParser::parse()
{
	std::string str;

	int tok = lexer(str);

	while (tok == ';')
		tok = lexer(str);

	if (tok == '}' || tok < 0)
		return NULL;

	if (tok != 'v')
		error();

	LibertyAst *ast = new LibertyAst;
	ast->id = str;

	while (1)
	{
		tok = lexer(str);

		if (tok == ';')
			break;

		if (tok == ':' && ast->value.empty()) {
			tok = lexer(ast->value);
			if (tok != 'v')
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
				if (tok != 'v')
					error();
				ast->args.push_back(arg);
			}
			continue;
		}

		if (tok == '{') {
			while (1) {
				LibertyAst *child = parse();
				if (child == NULL)
					break;
				ast->children.push_back(child);
			}
			break;
		}

		error();
	}

	return ast;
}

#ifndef FILTERLIB

void LibertyParser::error()
{
	log_error("Syntax error in line %d.\n", line);
}

#else

void LibertyParser::error()
{
	fprintf(stderr, "Syntax error in line %d.\n", line);
	exit(1);
}

/**** BEGIN: http://svn.clifford.at/tools/trunk/examples/check.h ****/

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

/**** END: http://svn.clifford.at/tools/trunk/examples/check.h ****/

LibertyAst *find_non_null(LibertyAst *node, const char *name)
{
	LibertyAst *ret = node->find(name);
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

void event2vl(LibertyAst *ast, std::string &edge, std::string &expr)
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

void gen_verilogsim_cell(LibertyAst *ast)
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
		LibertyAst *dir = find_non_null(child, "direction");
		LibertyAst *func = child->find("function");
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

void gen_verilogsim(LibertyAst *ast)
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

	if (argc > 3)
		usage();

	if (argc > 1)
	{
		if (!strcmp(argv[1], "-verilogsim"))
			flag_verilogsim = true;
		if (!strcmp(argv[1], "-") || !strcmp(argv[1], "-verilogsim"))
		{
			LibertyAst::whitelist.insert("/library");
			LibertyAst::whitelist.insert("/library/cell");
			LibertyAst::whitelist.insert("/library/cell/area");
			LibertyAst::whitelist.insert("/library/cell/cell_footprint");
			LibertyAst::whitelist.insert("/library/cell/dont_touch");
			LibertyAst::whitelist.insert("/library/cell/dont_use");
			LibertyAst::whitelist.insert("/library/cell/ff");
			LibertyAst::whitelist.insert("/library/cell/ff/*");
			LibertyAst::whitelist.insert("/library/cell/latch");
			LibertyAst::whitelist.insert("/library/cell/latch/*");
			LibertyAst::whitelist.insert("/library/cell/pin");
			LibertyAst::whitelist.insert("/library/cell/pin/clock");
			LibertyAst::whitelist.insert("/library/cell/pin/direction");
			LibertyAst::whitelist.insert("/library/cell/pin/driver_type");
			LibertyAst::whitelist.insert("/library/cell/pin/function");
			LibertyAst::whitelist.insert("/library/cell/pin_opposite");
			LibertyAst::whitelist.insert("/library/cell/pin/state_function");
			LibertyAst::whitelist.insert("/library/cell/pin/three_state");
			LibertyAst::whitelist.insert("/library/cell/statetable");
			LibertyAst::whitelist.insert("/library/cell/statetable/*");
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
								LibertyAst::blacklist.insert(id);
							else
							if (mode == '+')
								LibertyAst::whitelist.insert(id);
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
			parser.ast->dump(stdout);
	}

	if (argc == 3)
		delete f;

	return 0;
}

#endif

