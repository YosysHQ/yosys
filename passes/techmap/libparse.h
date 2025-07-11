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

/**
 * This file is likely to change in the near future.
 * Rely on it in your plugins at your own peril
 */

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
		std::string str(int indent = 0);
	private:
		static bool is_nice_binop(char c);
	};

	class LibertyInputStream {
		std::istream &f;
		std::vector<unsigned char> buffer;
		size_t buf_pos = 0;
		size_t buf_end = 0;
		bool eof = false;

		bool extend_buffer_once();
		bool extend_buffer_at_least(size_t size = 1);

		YS_COLD int get_cold();
		YS_COLD int peek_cold(size_t offset);

	public:
		LibertyInputStream(std::istream &f) : f(f) {}

		size_t buffered_size() { return buf_end - buf_pos; }
		const unsigned char *buffered_data() { return buffer.data() + buf_pos; }

		int get() {
			if (buf_pos == buf_end)
				return get_cold();
			int c = buffer[buf_pos];
			buf_pos += 1;
			return c;
		}

		int peek(size_t offset = 0) {
			if (buf_pos + offset >= buf_end)
				return peek_cold(offset);
			return buffer[buf_pos + offset];
		}

		void consume(size_t n = 1) {
			buf_pos += n;
		}

		void unget() {
			buf_pos -= 1;
		}
	};

#ifndef FILTERLIB
	class LibertyAstCache {
		LibertyAstCache() {};
		~LibertyAstCache() {};
	public:
		dict<std::string, std::shared_ptr<const LibertyAst>> cached;

		bool cache_by_default = false;
		bool verbose = false;
		dict<std::string, bool> cache_path;

		std::shared_ptr<const LibertyAst> cached_ast(const std::string &fname);
		void parsed_ast(const std::string &fname, const std::shared_ptr<const LibertyAst> &ast);
		static LibertyAstCache instance;
	};
#endif

	class LibertyMergedCells;
	class LibertyParser
	{
		friend class LibertyMergedCells;
	private:
		LibertyInputStream f;
		int line;

		/* lexer return values:
		   'v': identifier, string, array range [...] -> str holds the token string
		   'n': newline
		   anything else is a single character.
		*/
		int lexer(std::string &str);

		void report_unexpected_token(int tok);
		void parse_vector_range(int tok);
		LibertyAst *parse(bool top_level);
		void error() const;
		void error(const std::string &str) const;

	public:
		std::shared_ptr<const LibertyAst> shared_ast;
		const LibertyAst *ast = nullptr;

		LibertyParser(std::istream &f) : f(f), line(1) {
			shared_ast.reset(parse(true));
			ast = shared_ast.get();
			if (!ast) {
#ifdef FILTERLIB
				fprintf(stderr, "No entries found in liberty file.\n");
				exit(1);
#else
				log_error("No entries found in liberty file.\n");
#endif
			}
		}

#ifndef FILTERLIB
		LibertyParser(std::istream &f, const std::string &fname) : f(f), line(1) {
			shared_ast = LibertyAstCache::instance.cached_ast(fname);
			if (!shared_ast) {
				shared_ast.reset(parse(true));
				LibertyAstCache::instance.parsed_ast(fname, shared_ast);
			}
			ast = shared_ast.get();
			if (!ast) {
				log_error("No entries found in liberty file `%s'.\n", fname.c_str());
			}
		}
#endif
	};

	class LibertyMergedCells
	{
		std::vector<std::shared_ptr<const LibertyAst>> asts;

	public:
		std::vector<const LibertyAst *> cells;
		void merge(LibertyParser &parser)
		{
			if (parser.ast) {
				const LibertyAst *ast = parser.ast;
				asts.push_back(parser.shared_ast);
				if (ast->id != "library")
					parser.error("Top level entity isn't \"library\".\n");
				for (const LibertyAst *cell : ast->children)
					if (cell->id == "cell" && cell->args.size() == 1)
						cells.push_back(cell);
			}
		}
	};

}

#endif
