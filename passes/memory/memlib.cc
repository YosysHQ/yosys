/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
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

#include "memlib.h"

#include <ctype.h>

USING_YOSYS_NAMESPACE

using namespace MemLibrary;

PRIVATE_NAMESPACE_BEGIN

typedef dict<std::string, Const> Options;

struct ClockDef {
	ClkPolKind kind;
	std::string name;
};

struct RawWrTransDef {
	WrTransTargetKind target_kind;
	std::string target_group;
	WrTransKind kind;
};

struct PortWidthDef {
	bool tied;
	std::vector<int> wr_widths;
	std::vector<int> rd_widths;
};

struct SrstDef {
	ResetValKind val;
	SrstKind kind;
	bool block_wr;
};

struct Empty {};

template<typename T> struct Capability {
	T val;
	Options opts, portopts;

	Capability(T val, Options opts, Options portopts) : val(val), opts(opts), portopts(portopts) {}
};

template<typename T> using Caps = std::vector<Capability<T>>;

struct PortGroupDef {
	PortKind kind;
	dict<std::string, pool<Const>> portopts;
	std::vector<std::string> names;
	Caps<Empty> forbid;
	Caps<ClockDef> clock;
	Caps<Empty> clken;
	Caps<Empty> wrbe_separate;
	Caps<PortWidthDef> width;
	Caps<Empty> rden;
	Caps<RdWrKind> rdwr;
	Caps<ResetValKind> rdinit;
	Caps<ResetValKind> rdarst;
	Caps<SrstDef> rdsrst;
	Caps<std::string> wrprio;
	Caps<RawWrTransDef> wrtrans;
	Caps<Empty> optional;
	Caps<Empty> optional_rw;
};

struct WidthsDef {
	std::vector<int> widths;
	WidthMode mode;
};

struct ResourceDef {
	std::string name;
	int count;
};

struct RamDef {
	IdString id;
	dict<std::string, pool<Const>> opts;
	RamKind kind;
	Caps<Empty> forbid;
	Caps<Empty> prune_rom;
	Caps<PortGroupDef> ports;
	Caps<int> abits;
	Caps<WidthsDef> widths;
	Caps<ResourceDef> resource;
	Caps<double> cost;
	Caps<double> widthscale;
	Caps<int> byte;
	Caps<MemoryInitKind> init;
	Caps<std::string> style;
};

struct Parser {
	std::string filename;
	std::ifstream infile;
	int line_number = 0;
	Library &lib;
	const pool<std::string> &defines;
	pool<std::string> &defines_unused;
	std::vector<std::string> tokens;
	int token_idx = 0;
	bool eof = false;

	std::vector<std::pair<std::string, Const>> option_stack;
	std::vector<std::pair<std::string, Const>> portoption_stack;
	RamDef ram;
	PortGroupDef port;
	bool active = true;

	Parser(std::string filename, Library &lib, const pool<std::string> &defines, pool<std::string> &defines_unused) : filename(filename), lib(lib), defines(defines), defines_unused(defines_unused) {
		// Note: this rewrites the filename we're opening, but not
		// the one we're storing — this is actually correct, so that
		// we keep the original filename for diagnostics.
		rewrite_filename(filename);
		infile.open(filename);
		if (infile.fail()) {
			log_error("failed to open %s\n", filename.c_str());
		}
		parse();
		infile.close();
	}

	std::string peek_token() {
		if (eof)
			return "";

		if (token_idx < GetSize(tokens))
			return tokens[token_idx];

		tokens.clear();
		token_idx = 0;

		std::string line;
		while (std::getline(infile, line)) {
			line_number++;
			for (string tok = next_token(line); !tok.empty(); tok = next_token(line)) {
				if (tok[0] == '#')
					break;
				if (tok[tok.size()-1] == ';') {
					tokens.push_back(tok.substr(0, tok.size()-1));
					tokens.push_back(";");
				} else {
					tokens.push_back(tok);
				}
			}
			if (!tokens.empty())
				return tokens[token_idx];
		}

		eof = true;
		return "";
	}

	std::string get_token() {
		std::string res = peek_token();
		if (!eof)
			token_idx++;
		return res;
	}

	void eat_token(std::string expected) {
		std::string token = get_token();
		if (token != expected) {
			log_error("%s:%d: expected `%s`, got `%s`.\n", filename.c_str(), line_number, expected.c_str(), token.c_str());
		}
	}

	IdString get_id() {
		std::string token = get_token();
		if (token.empty() || (token[0] != '$' && token[0] != '\\')) {
			log_error("%s:%d: expected id string, got `%s`.\n", filename.c_str(), line_number, token.c_str());
		}
		return IdString(token);
	}

	std::string get_name() {
		std::string res = get_token();
		bool valid = true;
		// Basic sanity check.
		if (res.empty() || (!isalpha(res[0]) && res[0] != '_'))
			valid = false;
		for (char c: res)
			if (!isalnum(c) && c != '_')
				valid = false;
		if (!valid)
			log_error("%s:%d: expected name, got `%s`.\n", filename.c_str(), line_number, res.c_str());
		return res;
	}

	std::string get_string() {
		std::string token = get_token();
		if (token.size() < 2 || token[0] != '"' || token[token.size()-1] != '"') {
			log_error("%s:%d: expected string, got `%s`.\n", filename.c_str(), line_number, token.c_str());
		}
		return token.substr(1, token.size()-2);
	}

	bool peek_string() {
		std::string token = peek_token();
		return !token.empty() && token[0] == '"';
	}

	int get_int() {
		std::string token = get_token();
		char *endptr;
		long res = strtol(token.c_str(), &endptr, 0);
		if (token.empty() || *endptr || res > INT_MAX) {
			log_error("%s:%d: expected int, got `%s`.\n", filename.c_str(), line_number, token.c_str());
		}
		return res;
	}

	double get_double() {
		std::string token = get_token();
		char *endptr;
		double res = strtod(token.c_str(), &endptr);
		if (token.empty() || *endptr) {
			log_error("%s:%d: expected float, got `%s`.\n", filename.c_str(), line_number, token.c_str());
		}
		return res;
	}

	bool peek_int() {
		std::string token = peek_token();
		return !token.empty() && isdigit(token[0]);
	}

	void get_semi() {
		std::string token = get_token();
		if (token != ";") {
			log_error("%s:%d: expected `;`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
		}
	}

	Const get_value() {
		std::string token = peek_token();
		if (!token.empty() && token[0] == '"') {
			std::string s = get_string();
			return Const(s);
		} else {
			return Const(get_int());
		}
	}

	bool enter_ifdef(bool polarity) {
		bool res = active;
		std::string name = get_name();
		defines_unused.erase(name);
		if (active) {
			if (defines.count(name)) {
				active = polarity;
			} else {
				active = !polarity;
			}
		}
		return res;
	}

	void enter_else(bool save) {
		get_token();
		active = !active && save;
	}

	void enter_option() {
		std::string name = get_string();
		Const val = get_value();
		if (active) {
			ram.opts[name].insert(val);
		}
		option_stack.push_back({name, val});
	}

	void exit_option() {
		option_stack.pop_back();
	}

	Options get_options() {
		Options res;
		for (auto it: option_stack)
			res[it.first] = it.second;
		return res;
	}

	void enter_portoption() {
		std::string name = get_string();
		Const val = get_value();
		if (active) {
			port.portopts[name].insert(val);
		}
		portoption_stack.push_back({name, val});
	}

	void exit_portoption() {
		portoption_stack.pop_back();
	}

	Options get_portoptions() {
		Options res;
		for (auto it: portoption_stack)
			res[it.first] = it.second;
		return res;
	}

	template<typename T> void add_cap(Caps<T> &caps, T val) {
		if (active)
			caps.push_back(Capability<T>(val, get_options(), get_portoptions()));
	}

	void parse_port_block() {
		if (peek_token() == "{") {
			get_token();
			while (peek_token() != "}")
				parse_port_item();
			get_token();
		} else {
			parse_port_item();
		}
	}

	void parse_ram_block() {
		if (peek_token() == "{") {
			get_token();
			while (peek_token() != "}")
				parse_ram_item();
			get_token();
		} else {
			parse_ram_item();
		}
	}

	void parse_top_block() {
		if (peek_token() == "{") {
			get_token();
			while (peek_token() != "}")
				parse_top_item();
			get_token();
		} else {
			parse_top_item();
		}
	}

	void parse_port_item() {
		std::string token = get_token();
		if (token == "ifdef") {
			bool save = enter_ifdef(true);
			parse_port_block();
			if (peek_token() == "else") {
				enter_else(save);
				parse_port_block();
			}
			active = save;
		} else if (token == "ifndef") {
			bool save = enter_ifdef(false);
			parse_port_block();
			if (peek_token() == "else") {
				enter_else(save);
				parse_port_block();
			}
			active = save;
		} else if (token == "option") {
			enter_option();
			parse_port_block();
			exit_option();
		} else if (token == "portoption") {
			enter_portoption();
			parse_port_block();
			exit_portoption();
		} else if (token == "clock") {
			if (port.kind == PortKind::Ar) {
				log_error("%s:%d: `clock` not allowed in async read port.\n", filename.c_str(), line_number);
			}
			ClockDef def;
			token = get_token();
			if (token == "anyedge") {
				def.kind = ClkPolKind::Anyedge;
			} else if (token == "posedge") {
				def.kind = ClkPolKind::Posedge;
			} else if (token == "negedge") {
				def.kind = ClkPolKind::Negedge;
			} else {
				log_error("%s:%d: expected `posedge`, `negedge`, or `anyedge`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			if (peek_string()) {
				def.name = get_string();
			}
			get_semi();
			add_cap(port.clock, def);
		} else if (token == "clken") {
			if (port.kind == PortKind::Ar) {
				log_error("%s:%d: `clken` not allowed in async read port.\n", filename.c_str(), line_number);
			}
			get_semi();
			add_cap(port.clken, {});
		} else if (token == "wrbe_separate") {
			if (port.kind == PortKind::Ar || port.kind == PortKind::Sr) {
				log_error("%s:%d: `wrbe_separate` not allowed in read port.\n", filename.c_str(), line_number);
			}
			get_semi();
			add_cap(port.wrbe_separate, {});
		} else if (token == "width") {
			PortWidthDef def;
			token = peek_token();
			bool is_rw = port.kind == PortKind::Srsw || port.kind == PortKind::Arsw;
			if (token == "tied") {
				get_token();
				if (!is_rw)
					log_error("%s:%d: `tied` only makes sense for read+write ports.\n", filename.c_str(), line_number);
				while (peek_int())
					def.wr_widths.push_back(get_int());
				def.tied = true;
			} else if (token == "mix") {
				get_token();
				if (!is_rw)
					log_error("%s:%d: `mix` only makes sense for read+write ports.\n", filename.c_str(), line_number);
				while (peek_int())
					def.wr_widths.push_back(get_int());
				def.rd_widths = def.wr_widths;
				def.tied = false;
			} else if (token == "rd") {
				get_token();
				if (!is_rw)
					log_error("%s:%d: `rd` only makes sense for read+write ports.\n", filename.c_str(), line_number);
				do {
					def.rd_widths.push_back(get_int());
				} while (peek_int());
				eat_token("wr");
				do {
					def.wr_widths.push_back(get_int());
				} while (peek_int());
				def.tied = false;
			} else if (token == "wr") {
				get_token();
				if (!is_rw)
					log_error("%s:%d: `wr` only makes sense for read+write ports.\n", filename.c_str(), line_number);
				do {
					def.wr_widths.push_back(get_int());
				} while (peek_int());
				eat_token("rd");
				do {
					def.rd_widths.push_back(get_int());
				} while (peek_int());
				def.tied = false;
			} else {
				do {
					def.wr_widths.push_back(get_int());
				} while (peek_int());
				def.tied = true;
			}
			get_semi();
			add_cap(port.width, def);
		} else if (token == "rden") {
			if (port.kind != PortKind::Sr && port.kind != PortKind::Srsw)
				log_error("%s:%d: `rden` only allowed on sync read ports.\n", filename.c_str(), line_number);
			get_semi();
			add_cap(port.rden, {});
		} else if (token == "rdwr") {
			if (port.kind != PortKind::Srsw)
				log_error("%s:%d: `rdwr` only allowed on sync read+write ports.\n", filename.c_str(), line_number);
			RdWrKind kind;
			token = get_token();
			if (token == "undefined") {
				kind = RdWrKind::Undefined;
			} else if (token == "no_change") {
				kind = RdWrKind::NoChange;
			} else if (token == "new") {
				kind = RdWrKind::New;
			} else if (token == "old") {
				kind = RdWrKind::Old;
			} else if (token == "new_only") {
				kind = RdWrKind::NewOnly;
			} else {
				log_error("%s:%d: expected `undefined`, `new`, `old`, `new_only`, or `no_change`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			get_semi();
			add_cap(port.rdwr, kind);
		} else if (token == "rdinit") {
			if (port.kind != PortKind::Sr && port.kind != PortKind::Srsw)
				log_error("%s:%d: `%s` only allowed on sync read ports.\n", filename.c_str(), line_number, token.c_str());
			ResetValKind kind;
			token = get_token();
			if (token == "none") {
				kind = ResetValKind::None;
			} else if (token == "zero") {
				kind = ResetValKind::Zero;
			} else if (token == "any") {
				kind = ResetValKind::Any;
			} else if (token == "no_undef") {
				kind = ResetValKind::NoUndef;
			} else {
				log_error("%s:%d: expected `none`, `zero`, `any`, or `no_undef`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			get_semi();
			add_cap(port.rdinit, kind);
		} else if (token == "rdarst") {
			if (port.kind != PortKind::Sr && port.kind != PortKind::Srsw)
				log_error("%s:%d: `%s` only allowed on sync read ports.\n", filename.c_str(), line_number, token.c_str());
			ResetValKind kind;
			token = get_token();
			if (token == "none") {
				kind = ResetValKind::None;
			} else if (token == "zero") {
				kind = ResetValKind::Zero;
			} else if (token == "any") {
				kind = ResetValKind::Any;
			} else if (token == "no_undef") {
				kind = ResetValKind::NoUndef;
			} else if (token == "init") {
				kind = ResetValKind::Init;
			} else {
				log_error("%s:%d: expected `none`, `zero`, `any`, `no_undef`, or `init`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			get_semi();
			add_cap(port.rdarst, kind);
		} else if (token == "rdsrst") {
			if (port.kind != PortKind::Sr && port.kind != PortKind::Srsw)
				log_error("%s:%d: `%s` only allowed on sync read ports.\n", filename.c_str(), line_number, token.c_str());
			SrstDef def;
			token = get_token();
			if (token == "none") {
				def.val = ResetValKind::None;
			} else if (token == "zero") {
				def.val = ResetValKind::Zero;
			} else if (token == "any") {
				def.val = ResetValKind::Any;
			} else if (token == "no_undef") {
				def.val = ResetValKind::NoUndef;
			} else if (token == "init") {
				def.val = ResetValKind::Init;
			} else {
				log_error("%s:%d: expected `none`, `zero`, `any`, `no_undef`, or `init`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			if (def.val == ResetValKind::None) {
				def.kind = SrstKind::None;
			} else {
				token = get_token();
				if (token == "ungated") {
					def.kind = SrstKind::Ungated;
				} else if (token == "gated_clken") {
					def.kind = SrstKind::GatedClkEn;
				} else if (token == "gated_rden") {
					def.kind = SrstKind::GatedRdEn;
				} else {
					log_error("%s:%d: expected `ungated`, `gated_clken` or `gated_rden`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
				}
			}
			def.block_wr = false;
			if (peek_token() == "block_wr") {
				get_token();
				def.block_wr = true;
			}
			get_semi();
			add_cap(port.rdsrst, def);
		} else if (token == "wrprio") {
			if (port.kind == PortKind::Ar || port.kind == PortKind::Sr)
				log_error("%s:%d: `wrprio` only allowed on write ports.\n", filename.c_str(), line_number);
			do {
				add_cap(port.wrprio, get_string());
			} while (peek_string());
			get_semi();
		} else if (token == "wrtrans") {
			if (port.kind == PortKind::Ar || port.kind == PortKind::Sr)
				log_error("%s:%d: `wrtrans` only allowed on write ports.\n", filename.c_str(), line_number);
			token = peek_token();
			RawWrTransDef def;
			if (token == "all") {
				def.target_kind = WrTransTargetKind::All;
				get_token();
			} else {
				def.target_kind = WrTransTargetKind::Group;
				def.target_group = get_string();
			}
			token = get_token();
			if (token == "new") {
				def.kind = WrTransKind::New;
			} else if (token == "old") {
				def.kind = WrTransKind::Old;
			} else {
				log_error("%s:%d: expected `new` or `old`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			get_semi();
			add_cap(port.wrtrans, def);
		} else if (token == "forbid") {
			get_semi();
			add_cap(port.forbid, {});
		} else if (token == "optional") {
			get_semi();
			add_cap(port.optional, {});
		} else if (token == "optional_rw") {
			get_semi();
			add_cap(port.optional_rw, {});
		} else if (token == "") {
			log_error("%s:%d: unexpected EOF while parsing port item.\n", filename.c_str(), line_number);
		} else {
			log_error("%s:%d: unknown port-level item `%s`.\n", filename.c_str(), line_number, token.c_str());
		}
	}

	void parse_ram_item() {
		std::string token = get_token();
		if (token == "ifdef") {
			bool save = enter_ifdef(true);
			parse_ram_block();
			if (peek_token() == "else") {
				enter_else(save);
				parse_ram_block();
			}
			active = save;
		} else if (token == "ifndef") {
			bool save = enter_ifdef(false);
			parse_ram_block();
			if (peek_token() == "else") {
				enter_else(save);
				parse_ram_block();
			}
			active = save;
		} else if (token == "option") {
			enter_option();
			parse_ram_block();
			exit_option();
		} else if (token == "prune_rom") {
			get_semi();
			add_cap(ram.prune_rom, {});
		} else if (token == "forbid") {
			get_semi();
			add_cap(ram.forbid, {});
		} else if (token == "abits") {
			int val = get_int();
			if (val < 0)
				log_error("%s:%d: abits %d nagative.\n", filename.c_str(), line_number, val);
			get_semi();
			add_cap(ram.abits, val);
		} else if (token == "width") {
			WidthsDef def;
			int w = get_int();
			if (w <= 0)
				log_error("%s:%d: width %d not positive.\n", filename.c_str(), line_number, w);
			def.widths.push_back(w);
			def.mode = WidthMode::Single;
			get_semi();
			add_cap(ram.widths, def);
		} else if (token == "widths") {
			WidthsDef def;
			int last = 0;
			do {
				int w = get_int();
				if (w <= 0)
					log_error("%s:%d: width %d not positive.\n", filename.c_str(), line_number, w);
				if (w < last * 2)
					log_error("%s:%d: width %d smaller than %d required for progression.\n", filename.c_str(), line_number, w, last * 2);
				last = w;
				def.widths.push_back(w);
			} while(peek_int());
			token = get_token();
			if (token == "global") {
				def.mode = WidthMode::Global;
			} else if (token == "per_port") {
				def.mode = WidthMode::PerPort;
			} else {
				log_error("%s:%d: expected `global`, or `per_port`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			get_semi();
			add_cap(ram.widths, def);
		} else if (token == "resource") {
			ResourceDef def;
			def.name = get_string();
			if (peek_int())
				def.count = get_int();
			else
				def.count = 1;
			get_semi();
			add_cap(ram.resource, def);
		} else if (token == "cost") {
			add_cap(ram.cost, get_double());
			get_semi();
		} else if (token == "widthscale") {
			if (peek_int()) {
				add_cap(ram.widthscale, get_double());
			} else {
				add_cap(ram.widthscale, 0.0);
			}
			get_semi();
		} else if (token == "byte") {
			int val = get_int();
			if (val <= 0)
				log_error("%s:%d: byte width %d not positive.\n", filename.c_str(), line_number, val);
			add_cap(ram.byte, val);
			get_semi();
		} else if (token == "init") {
			MemoryInitKind kind;
			token = get_token();
			if (token == "zero") {
				kind = MemoryInitKind::Zero;
			} else if (token == "any") {
				kind = MemoryInitKind::Any;
			} else if (token == "no_undef") {
				kind = MemoryInitKind::NoUndef;
			} else if (token == "none") {
				kind = MemoryInitKind::None;
			} else {
				log_error("%s:%d: expected `zero`, `any`, `none`, or `no_undef`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			get_semi();
			add_cap(ram.init, kind);
		} else if (token == "style") {
			do {
				std::string val = get_string();
				for (auto &c: val)
					c = std::tolower(c);
				add_cap(ram.style, val);
			} while (peek_string());
			get_semi();
		} else if (token == "port") {
			port = PortGroupDef();
			token = get_token();
			if (token == "ar") {
				port.kind = PortKind::Ar;
			} else if (token == "sr") {
				port.kind = PortKind::Sr;
			} else if (token == "sw") {
				port.kind = PortKind::Sw;
			} else if (token == "arsw") {
				port.kind = PortKind::Arsw;
			} else if (token == "srsw") {
				port.kind = PortKind::Srsw;
			} else {
				log_error("%s:%d: expected `ar`, `sr`, `sw`, `arsw`, or `srsw`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			do {
				port.names.push_back(get_string());
			} while (peek_string());
			parse_port_block();
			if (active)
				add_cap(ram.ports, port);
		} else if (token == "") {
			log_error("%s:%d: unexpected EOF while parsing ram item.\n", filename.c_str(), line_number);
		} else {
			log_error("%s:%d: unknown ram-level item `%s`.\n", filename.c_str(), line_number, token.c_str());
		}
	}

	void parse_top_item() {
		std::string token = get_token();
		if (token == "ifdef") {
			bool save = enter_ifdef(true);
			parse_top_block();
			if (peek_token() == "else") {
				enter_else(save);
				parse_top_block();
			}
			active = save;
		} else if (token == "ifndef") {
			bool save = enter_ifdef(false);
			parse_top_block();
			if (peek_token() == "else") {
				enter_else(save);
				parse_top_block();
			}
			active = save;
		} else if (token == "ram") {
			int orig_line = line_number;
			ram = RamDef();
			token = get_token();
			if (token == "distributed") {
				ram.kind = RamKind::Distributed;
			} else if (token == "block") {
				ram.kind = RamKind::Block;
			} else if (token == "huge") {
				ram.kind = RamKind::Huge;
			} else {
				log_error("%s:%d: expected `distributed`, `block`, or `huge`, got `%s`.\n", filename.c_str(), line_number, token.c_str());
			}
			ram.id = get_id();
			parse_ram_block();
			if (active) {
				compile_ram(orig_line);
			}
		} else if (token == "") {
			log_error("%s:%d: unexpected EOF while parsing top item.\n", filename.c_str(), line_number);
		} else {
			log_error("%s:%d: unknown top-level item `%s`.\n", filename.c_str(), line_number, token.c_str());
		}
	}

	bool opts_ok(const Options &def, const Options &var) {
		for (auto &it: def)
			if (var.at(it.first) != it.second)
				return false;
		return true;
	}

	template<typename T> const T *find_single_cap(const Caps<T> &caps, const Options &opts, const Options &portopts, const char *name) {
		const T *res = nullptr;
		for (auto &cap: caps) {
			if (!opts_ok(cap.opts, opts))
				continue;
			if (!opts_ok(cap.portopts, portopts))
				continue;
			if (res)
				log_error("%s:%d: duplicate %s cap.\n", filename.c_str(), line_number, name);
			res = &cap.val;
		}
		return res;
	}

	std::vector<Options> make_opt_combinations(const dict<std::string, pool<Const>> &opts) {
		std::vector<Options> res;
		res.push_back(Options());
		for (auto &it: opts) {
			std::vector<Options> new_res;
			for (auto &val: it.second) {
				for (Options o: res) {
					o[it.first] = val;
					new_res.push_back(o);
				}
			}
			res = new_res;
		}
		return res;
	}

	void compile_portgroup(Ram &cram, PortGroupDef &pdef, dict<std::string, int> &clk_ids, const dict<std::string, int> &port_ids, int orig_line) {
		PortGroup grp;
		grp.optional = find_single_cap(pdef.optional, cram.options, Options(), "optional");
		grp.optional_rw = find_single_cap(pdef.optional_rw, cram.options, Options(), "optional_rw");
		grp.names = pdef.names;
		for (auto portopts: make_opt_combinations(pdef.portopts)) {
			bool forbidden = false;
			for (auto &fdef: ram.forbid) {
				if (opts_ok(fdef.opts, cram.options) && opts_ok(fdef.portopts, portopts)) {
					forbidden = true;
				}
			}
			if (forbidden)
				continue;
			PortVariant var;
			var.options = portopts;
			var.kind = pdef.kind;
			if (pdef.kind != PortKind::Ar) {
				const ClockDef *cdef = find_single_cap(pdef.clock, cram.options, portopts, "clock");
				if (!cdef)
					log_error("%s:%d: missing clock capability.\n", filename.c_str(), orig_line);
				var.clk_pol = cdef->kind;
				if (cdef->name.empty()) {
					var.clk_shared = -1;
				} else {
					auto it = clk_ids.find(cdef->name);
					bool anyedge = cdef->kind == ClkPolKind::Anyedge;
					if (it == clk_ids.end()) {
						clk_ids[cdef->name] = var.clk_shared = GetSize(cram.shared_clocks);
						RamClock clk;
						clk.name = cdef->name;
						clk.anyedge = anyedge;
						cram.shared_clocks.push_back(clk);
					} else {
						var.clk_shared = it->second;
						if (cram.shared_clocks[var.clk_shared].anyedge != anyedge) {
							log_error("%s:%d: named clock \"%s\" used with both posedge/negedge and anyedge clocks.\n", filename.c_str(), orig_line, cdef->name.c_str());
						}
					}
				}
				var.clk_en = find_single_cap(pdef.clken, cram.options, portopts, "clken");
			}
			const PortWidthDef *wdef = find_single_cap(pdef.width, cram.options, portopts, "width");
			if (wdef) {
				if (cram.width_mode != WidthMode::PerPort)
					log_error("%s:%d: per-port width doesn't make sense for tied dbits.\n", filename.c_str(), orig_line);
				compile_widths(var, cram.dbits, *wdef);
			} else {
				var.width_tied = true;
				var.min_wr_wide_log2 = 0;
				var.min_rd_wide_log2 = 0;
				var.max_wr_wide_log2 = GetSize(cram.dbits) - 1;
				var.max_rd_wide_log2 = GetSize(cram.dbits) - 1;
			}
			if (pdef.kind == PortKind::Srsw || pdef.kind == PortKind::Sr) {
				const RdWrKind *rdwr = find_single_cap(pdef.rdwr, cram.options, portopts, "rdwr");
				var.rdwr = rdwr ? *rdwr : RdWrKind::Undefined;
				var.rd_en = find_single_cap(pdef.rden, cram.options, portopts, "rden");
				const ResetValKind *iv = find_single_cap(pdef.rdinit, cram.options, portopts, "rdinit");
				var.rdinitval = iv ? *iv : ResetValKind::None;
				const ResetValKind *arv = find_single_cap(pdef.rdarst, cram.options, portopts, "rdarst");
				var.rdarstval = arv ? *arv : ResetValKind::None;
				const SrstDef *srv = find_single_cap(pdef.rdsrst, cram.options, portopts, "rdsrst");
				if (srv) {
					var.rdsrstval = srv->val;
					var.rdsrstmode = srv->kind;
					var.rdsrst_block_wr = srv->block_wr;
					if (srv->kind == SrstKind::GatedClkEn && !var.clk_en)
						log_error("%s:%d: `gated_clken` used without `clken`.\n", filename.c_str(), orig_line);
					if (srv->kind == SrstKind::GatedRdEn && !var.rd_en)
						log_error("%s:%d: `gated_rden` used without `rden`.\n", filename.c_str(), orig_line);
				} else {
					var.rdsrstval = ResetValKind::None;
					var.rdsrstmode = SrstKind::None;
					var.rdsrst_block_wr = false;
				}
				if (var.rdarstval == ResetValKind::Init || var.rdsrstval == ResetValKind::Init) {
					if (var.rdinitval != ResetValKind::Any && var.rdinitval != ResetValKind::NoUndef) {
						log_error("%s:%d: reset value `init` has to be paired with `any` or `no_undef` initial value.\n", filename.c_str(), orig_line);
					}
				}
			}
			var.wrbe_separate = find_single_cap(pdef.wrbe_separate, cram.options, portopts, "wrbe_separate");
			if (var.wrbe_separate && cram.byte == 0) {
				log_error("%s:%d: `wrbe_separate` used without `byte`.\n", filename.c_str(), orig_line);
			}
			for (auto &def: pdef.wrprio) {
				if (!opts_ok(def.opts, cram.options))
					continue;
				if (!opts_ok(def.portopts, portopts))
					continue;
				var.wrprio.push_back(port_ids.at(def.val));
			}
			for (auto &def: pdef.wrtrans) {
				if (!opts_ok(def.opts, cram.options))
					continue;
				if (!opts_ok(def.portopts, portopts))
					continue;
				WrTransDef tdef;
				tdef.target_kind = def.val.target_kind;
				if (def.val.target_kind == WrTransTargetKind::Group)
					tdef.target_group = port_ids.at(def.val.target_group);
				tdef.kind = def.val.kind;
				var.wrtrans.push_back(tdef);
			}
			grp.variants.push_back(var);
		}
		if (grp.variants.empty()) {
			log_error("%s:%d: all port option combinations are forbidden.\n", filename.c_str(), orig_line);
		}
		cram.port_groups.push_back(grp);
	}

	void compile_ram(int orig_line) {
		if (ram.abits.empty())
			log_error("%s:%d: `dims` capability should be specified.\n", filename.c_str(), orig_line);
		if (ram.widths.empty())
			log_error("%s:%d: `widths` capability should be specified.\n", filename.c_str(), orig_line);
		if (ram.ports.empty())
			log_error("%s:%d: at least one port group should be specified.\n", filename.c_str(), orig_line);
		for (auto opts: make_opt_combinations(ram.opts)) {
			bool forbidden = false;
			for (auto &fdef: ram.forbid) {
				if (opts_ok(fdef.opts, opts)) {
					forbidden = true;
				}
			}
			if (forbidden)
				continue;
			Ram cram;
			cram.id = ram.id;
			cram.kind = ram.kind;
			cram.options = opts;
			cram.prune_rom = find_single_cap(ram.prune_rom, opts, Options(), "prune_rom");
			const int *abits = find_single_cap(ram.abits, opts, Options(), "abits");
			if (!abits)
				continue;
			cram.abits = *abits;
			const WidthsDef *widths = find_single_cap(ram.widths, opts, Options(), "widths");
			if (!widths)
				continue;
			cram.dbits = widths->widths;
			cram.width_mode = widths->mode;
			const ResourceDef *resource = find_single_cap(ram.resource, opts, Options(), "resource");
			if (resource) {
				cram.resource_name = resource->name;
				cram.resource_count = resource->count;
			} else {
				cram.resource_count = 1;
			}
			cram.cost = 0;
			for (auto &cap: ram.cost) {
				if (opts_ok(cap.opts, opts))
					cram.cost += cap.val;
			}
			const double *widthscale = find_single_cap(ram.widthscale, opts, Options(), "widthscale");
			if (widthscale)
				cram.widthscale = *widthscale ? *widthscale : cram.cost;
			else
				cram.widthscale = 0;
			const int *byte = find_single_cap(ram.byte, opts, Options(), "byte");
			cram.byte = byte ? *byte : 0;
			if (GetSize(cram.dbits) - 1 > cram.abits)
				log_error("%s:%d: abits %d too small for dbits progression.\n", filename.c_str(), line_number, cram.abits);
			validate_byte(widths->widths, cram.byte);
			const MemoryInitKind *ik = find_single_cap(ram.init, opts, Options(), "init");
			cram.init = ik ? *ik : MemoryInitKind::None;
			for (auto &sdef: ram.style)
				if (opts_ok(sdef.opts, opts))
					cram.style.push_back(sdef.val);
			dict<std::string, int> port_ids;
			int ctr = 0;
			for (auto &pdef: ram.ports) {
				if (!opts_ok(pdef.opts, opts))
					continue;
				for (auto &name: pdef.val.names)
					port_ids[name] = ctr;
				ctr++;
			}
			dict<std::string, int> clk_ids;
			for (auto &pdef: ram.ports) {
				if (!opts_ok(pdef.opts, opts))
					continue;
				compile_portgroup(cram, pdef.val, clk_ids, port_ids, orig_line);
			}
			lib.rams.push_back(cram);
		}
	}

	void validate_byte(const std::vector<int> &widths, int byte) {
		if (byte == 0)
			return;
		if (byte >= widths.back())
			return;
		if (widths[0] % byte == 0) {
			for (int j = 1; j < GetSize(widths); j++)
				if (widths[j] % byte != 0)
					log_error("%s:%d: width progression past byte width %d is not divisible.\n", filename.c_str(), line_number, byte);
			return;
		}
		for (int i = 0; i < GetSize(widths); i++) {
			if (widths[i] == byte) {
				for (int j = i + 1; j < GetSize(widths); j++)
					if (widths[j] % byte != 0)
						log_error("%s:%d: width progression past byte width %d is not divisible.\n", filename.c_str(), line_number, byte);
				return;
			}
		}
		log_error("%s:%d: byte width %d invalid for dbits.\n", filename.c_str(), line_number, byte);
	}

	void compile_widths(PortVariant &var, const std::vector<int> &widths, const PortWidthDef &width) {
		var.width_tied = width.tied;
		auto wr_widths = compile_widthdef(widths, width.wr_widths);
		var.min_wr_wide_log2 = wr_widths.first;
		var.max_wr_wide_log2 = wr_widths.second;
		if (width.tied) {
			var.min_rd_wide_log2 = wr_widths.first;
			var.max_rd_wide_log2 = wr_widths.second;
		} else {
			auto rd_widths = compile_widthdef(widths, width.rd_widths);
			var.min_rd_wide_log2 = rd_widths.first;
			var.max_rd_wide_log2 = rd_widths.second;
		}
	}

	std::pair<int, int> compile_widthdef(const std::vector<int> &dbits, const std::vector<int> &widths) {
		if (widths.empty())
			return {0, GetSize(dbits) - 1};
		for (int i = 0; i < GetSize(dbits); i++) {
			if (dbits[i] == widths[0]) {
				for (int j = 0; j < GetSize(widths); j++) {
					if (i+j >= GetSize(dbits) || dbits[i+j] != widths[j]) {
						log_error("%s:%d: port width %d doesn't match dbits progression.\n", filename.c_str(), line_number, widths[j]);
					}
				}
				return {i, i + GetSize(widths) - 1};
			}
		}
		log_error("%s:%d: port width %d invalid for dbits.\n", filename.c_str(), line_number, widths[0]);
	}

	void parse() {
		while (peek_token() != "")
			parse_top_item();
	}
};

PRIVATE_NAMESPACE_END

Library MemLibrary::parse_library(const std::vector<std::string> &filenames, const pool<std::string> &defines) {
	Library res;
	pool<std::string> defines_unused = defines;
	for (auto &file: filenames) {
		Parser(file, res, defines, defines_unused);
	}
	for (auto def: defines_unused) {
		log_warning("define %s not used in the library.\n", def.c_str());
	}
	return res;
}
