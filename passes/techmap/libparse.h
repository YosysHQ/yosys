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

#ifndef LIBPARSE_H
#define LIBPARSE_H

#include "kernel/yosys.h"
#include <stdio.h>
#include <string>
#include <vector>
#include <set>

namespace Yosys
{
	struct LibertyAst
	{
		std::string id, value;
		std::vector<std::string> args;
		std::vector<LibertyAst*> children;
		~LibertyAst();
		const LibertyAst *find(std::string name) const;

		typedef std::set<std::string> sieve;
		void dump(FILE *f, sieve &blacklist, sieve &whitelist, std::string indent = "", std::string path = "", bool path_ok = false) const;
	};

	struct LibertyExpression
	{
		struct Lexer {
			std::string s, expr;

			Lexer(std::string s) : s{s}, expr{s} {}

			bool empty() { return s.empty();}
			char peek() { return s[0]; }
			std::string full_expr() { return expr; }

			char next() {
				char c = s[0];
				s = s.substr(1, s.size());
				return c;
			}

			std::string pin() {
				auto length = s.find_first_of("\t()'!^*& +|");
				if (length == std::string::npos) {
					// nothing found so use size of s
					length = s.size();
				}
				auto pin = s.substr(0, length);
				s = s.substr(length, s.size());
				return pin;
			}
		};

		enum Kind {
			AND,
			OR,
			NOT,
			XOR,
			// the standard specifies constants, but they're probably rare in practice.
			PIN,
			EMPTY
		};

		Kind kind;
		std::string name;
		std::vector<LibertyExpression> children;

		LibertyExpression() : kind(Kind::EMPTY) {}

		static LibertyExpression parse(Lexer &s, int min_prio = 0);
		void get_pin_names(pool<std::string>& names);
		bool eval(dict<std::string, bool>& values);
	};

	class LibertyMergedCells;
	class LibertyParser
	{
		friend class LibertyMergedCells;
	private:
		std::istream &f;
		int line;

		/* lexer return values:
		   'v': identifier, string, array range [...] -> str holds the token string
		   'n': newline
		   anything else is a single character.
		*/
		int lexer(std::string &str);

		LibertyAst *parse();
		void error() const;
		void error(const std::string &str) const;

	public:
		const LibertyAst *ast;

		LibertyParser(std::istream &f) : f(f), line(1), ast(parse()) {}
		~LibertyParser() { if (ast) delete ast; }
	};

	class LibertyMergedCells
	{
		std::vector<const LibertyAst *> asts;

	public:
		std::vector<const LibertyAst *> cells;
		void merge(LibertyParser &parser)
		{
			if (parser.ast) {
				const LibertyAst *ast = parser.ast;
				asts.push_back(ast);
				// The parser no longer owns its top level ast, but we do.
				// sketchy zone
				parser.ast = nullptr;
				if (ast->id != "library")
					parser.error("Top level entity isn't \"library\".\n");
				for (const LibertyAst *cell : ast->children)
					if (cell->id == "cell" && cell->args.size() == 1)
						cells.push_back(cell);
			}
		}
		~LibertyMergedCells()
		{
			for (auto ast : asts)
				delete ast;
		}
	};

}

#endif
