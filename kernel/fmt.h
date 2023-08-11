/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  whitequark <whitequark@whitequark.org>
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

#ifndef FMT_H
#define FMT_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

// Verilog format argument, such as the arguments in:
//   $display("foo %d bar %01x", 4'b0, $signed(2'b11))
struct VerilogFmtArg {
	enum {
		STRING  = 0,
		INTEGER = 1,
		TIME    = 2,
	} type;

	// All types
	std::string filename;
	unsigned first_line;

	// STRING type
	std::string str;

	// INTEGER type
	RTLIL::SigSpec sig;
	bool signed_ = false;

	// TIME type
	bool realtime = false;
};

// RTLIL format part, such as the substitutions in:
//   "foo {4:> 4du} bar {2:<01hs}"
struct FmtPart {
	enum {
		STRING  	= 0,
		INTEGER 	= 1,
		CHARACTER = 2,
		TIME    	= 3,
	} type;

	// STRING type
	std::string str;

	// INTEGER/CHARACTER types
	RTLIL::SigSpec sig;

	// INTEGER/CHARACTER/TIME types
	enum {
		RIGHT	= 0,
		LEFT	= 1,
	} justify = RIGHT;
	char padding = '\0';
	size_t width = 0;
	
	// INTEGER type
	unsigned base = 10;
	bool signed_ = false;
	bool plus = false;

	// TIME type
	bool realtime = false;
};

struct Fmt {
public:
	std::vector<FmtPart> parts;

	void append_string(const std::string &str);

	void parse_rtlil(const RTLIL::Cell *cell);
	void emit_rtlil(RTLIL::Cell *cell) const;

	void parse_verilog(const std::vector<VerilogFmtArg> &args, bool sformat_like, int default_base, RTLIL::IdString task_name, RTLIL::IdString module_name);
	std::vector<VerilogFmtArg> emit_verilog() const;

	void emit_cxxrtl(std::ostream &f, std::function<void(const RTLIL::SigSpec &)> emit_sig) const;

	std::string render() const;

private:
	void apply_verilog_automatic_sizing_and_add(FmtPart &part);
};

YOSYS_NAMESPACE_END

#endif
