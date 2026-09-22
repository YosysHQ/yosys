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
#include <algorithm>
#include <array>
#include <span>
#include <string>
#include <string_view>
#include <vector>
#include <set>

/**
 * This file is likely to change in the near future.
 * Rely on it in your plugins at your own peril
 */

namespace Yosys
{
	class LibertyFilter
	{
		std::span<const std::string_view> allowed;
		bool unrestricted;
	public:
		constexpr LibertyFilter() : allowed{}, unrestricted(true) {}
		constexpr explicit LibertyFilter(std::span<const std::string_view> sorted_ids)
				: allowed(sorted_ids), unrestricted(false) {}

		constexpr bool allows(std::string_view id) const {
			return unrestricted || std::binary_search(allowed.begin(), allowed.end(), id);
		}

		constexpr bool covers(const LibertyFilter &other) const {
			if (unrestricted)
				return true;
			if (other.unrestricted)
				return false;
			return std::includes(allowed.begin(), allowed.end(),
					other.allowed.begin(), other.allowed.end());
		}

		static constexpr LibertyFilter all() { return {}; }
	};

	template <std::size_t N>
	consteval std::array<std::string_view, N> liberty_names(const char *const (&ids)[N])
	{
		std::array<std::string_view, N> sorted{};
		for (std::size_t i = 0; i < N; i++)
			sorted[i] = ids[i];
		std::sort(sorted.begin(), sorted.end());
		if (std::adjacent_find(sorted.begin(), sorted.end()) != sorted.end())
			throw "duplicate id in liberty name list";
		return sorted;
	}

	template <std::size_t A, std::size_t B>
	consteval std::array<std::string_view, A + B> merge_names(
			const std::array<std::string_view, A> &a, const std::array<std::string_view, B> &b)
	{
		std::array<std::string_view, A + B> merged{};
		std::merge(a.begin(), a.end(), b.begin(), b.end(), merged.begin());
		return merged;
	}

	template <std::size_t A, std::size_t B, typename... Rest>
	consteval auto merge_names(const std::array<std::string_view, A> &a,
			const std::array<std::string_view, B> &b, const Rest &... rest)
	{
		return merge_names(merge_names(a, b), rest...);
	}

	inline constexpr auto liberty_common_names = liberty_names({
		"library", "cell", "area",
	});

	inline constexpr auto liberty_pin_names = liberty_names({
		"pin", "direction",
	});

	inline constexpr auto liberty_ff_names = liberty_names({
		"ff", "clocked_on", "next_state", "clear", "preset",
	});

	inline constexpr auto read_liberty_names = merge_names(
		liberty_common_names, liberty_pin_names, liberty_ff_names,
		liberty_names({
			"bus", "type", "statetable", "ff_bank", "latch", "latch_bank",
			"bus_type", "capacitance", "function", "three_state",
			"base_type", "data_type", "bit_width", "bit_from", "bit_to", "downto",
			"data_in", "enable", "clear_preset_var1", "clear_preset_var2",
		}));

	inline constexpr auto dfflibmap_names = merge_names(
		liberty_common_names, liberty_pin_names, liberty_ff_names,
		liberty_names({
			"dont_use", "function",
		}));

	inline constexpr auto clockgate_names = merge_names(
		liberty_common_names, liberty_pin_names,
		liberty_names({
			"dont_use", "clock_gating_integrated_cell",
			"clock_gate_clock_pin", "clock_gate_enable_pin",
			"clock_gate_out_pin", "clock_gate_test_pin",
		}));

	inline constexpr auto stat_liberty_names = merge_names(
		liberty_common_names,
		liberty_names({
			"ff", "port_names",
			"single_area_parameterised", "double_area_parameterised",
		}));

	inline constexpr auto liberty_synthesis_names =
			merge_names(read_liberty_names, dfflibmap_names, clockgate_names, stat_liberty_names);

	inline constexpr LibertyFilter liberty_synth_filter{liberty_synthesis_names};

	static_assert(liberty_synth_filter.covers(LibertyFilter{read_liberty_names}));
	static_assert(liberty_synth_filter.covers(LibertyFilter{dfflibmap_names}));
	static_assert(liberty_synth_filter.covers(LibertyFilter{clockgate_names}));
	static_assert(liberty_synth_filter.covers(LibertyFilter{stat_liberty_names}));
	static_assert(!liberty_synth_filter.allows("timing"));
	static_assert(!liberty_synth_filter.allows("internal_power"));

	struct LibertyAst
	{
		std::string id, value;
		std::vector<std::string> args;
		std::vector<LibertyAst*> children;
		LibertyFilter filter;
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
				auto length = s.find_first_of("\t()'!^*& +|\"");
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
		void get_pin_names(std::unordered_set<std::string>& names);
		bool eval(std::unordered_map<std::string, bool>& values);
		std::string sexpr_str(int indent = 0);
		std::string vlog_str();
	private:
		static bool char_is_nice_binop(char c);
		bool is_binop();
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
		struct CacheEntry {
			LibertyFilter filter;
			std::shared_ptr<const LibertyAst> ast;
		};

		dict<std::string, CacheEntry> cached;

		bool cache_by_default = false;
		bool verbose = false;
		dict<std::string, bool> cache_path;

		std::shared_ptr<const LibertyAst> cached_ast(const std::string &fname, const LibertyFilter &filter);
		void parsed_ast(const std::string &fname, const LibertyFilter &filter,
				const std::shared_ptr<const LibertyAst> &ast);
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
		LibertyFilter filter;

		struct ParseResult {
			enum Kind { Node, Skipped, Closed } kind;
			LibertyAst *ast;

			static ParseResult node(LibertyAst *ast) { return {Node, ast}; }
			static ParseResult skipped() { return {Skipped, nullptr}; }
			static ParseResult closed() { return {Closed, nullptr}; }
		};

		/* lexer return values:
		   'v': identifier, string, array range [...] -> str holds the token string
		   'n': newline
		   anything else is a single character.
		*/
		int lexer_inner(std::string &str);
		int lexer(std::string &str);

		void report_unexpected_token(int tok);
		void parse_vector_range(int tok);
		int consume_wrecked_str(int tok, std::string& out_str);
		ParseResult try_parse(bool top_level, bool skipping);
		LibertyAst *parse(bool top_level, bool skipping);
		void error() const;
		void error(const std::string &str) const;

	public:
		std::shared_ptr<const LibertyAst> shared_ast;
		const LibertyAst *ast = nullptr;

		LibertyParser(std::istream &f, LibertyFilter filter = LibertyFilter::all())
				: f(f), line(1), filter(filter) {
			shared_ast.reset(parse(true, false));
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
		LibertyParser(std::istream &f, const std::string &fname,
				LibertyFilter filter = LibertyFilter::all()) : f(f), line(1), filter(filter) {
			shared_ast = LibertyAstCache::instance.cached_ast(fname, filter);
			if (!shared_ast) {
				shared_ast.reset(parse(true, false));
				LibertyAstCache::instance.parsed_ast(fname, filter, shared_ast);
			}
			ast = shared_ast.get();
			if (!ast) {
				log_error("No entries found in liberty file `%s'.\n", fname);
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
