/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Remy Goldschmidt <taktoa@gmail.com>
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
 *  Support for Verilog user-defined primitives (UDPs), IEEE 1364-2005
 *  clause 8.  The Verilog parser collects a UDP definition into a
 *  UdpParseData structure; make_udp_module() then lowers it into an
 *  ordinary behavioural AST module that the rest of Yosys synthesises
 *  using the existing FF/latch inference passes.
 *
 */

#ifndef VERILOG_UDP_H
#define VERILOG_UDP_H

#include "kernel/yosys.h"
#include "frontends/ast/ast.h"

YOSYS_NAMESPACE_BEGIN

namespace VERILOG_FRONTEND
{
	// A single row of the UDP state table.  The input symbols are stored in
	// port-list order (i.e. matching the order of the input ports in the UDP
	// header, not the order of the input declarations).
	struct UdpTableRow {
		std::vector<std::string> inputs; // one raw symbol per input port
		std::string current;             // current-state symbol ("" if combinational)
		std::string output;              // output / next-state symbol
		AST::AstSrcLocType loc;
	};

	// Everything the parser collects while reading a `primitive ... endprimitive`
	// block.  Consumed by make_udp_module().
	struct UdpParseData {
		AST::AstSrcLocType loc;
		std::string name;                       // UDP name (escaped, e.g. "\\foo")

		std::vector<std::string> port_order;    // port names in header order; [0] is the output
		std::string output_name;                // name of the (single) output port
		pool<std::string> input_names;          // names declared as inputs
		bool output_declared = false;
		bool is_sequential = false;             // true once a reg declaration is seen

		std::unique_ptr<AST::AstNode> initial_val; // optional initial value expression (or null)

		std::unique_ptr<dict<RTLIL::IdString, std::unique_ptr<AST::AstNode>>> attributes;

		std::vector<UdpTableRow> rows;
		bool table_is_sequential = false;       // table rows carry a current-state field

		// scratch used while accumulating the input fields of the row currently
		// being parsed
		std::vector<std::string> scratch_inputs;
	};

	// Lower a parsed UDP into a behavioural AST_MODULE.  Reports user errors via
	// log_file_error().  Never returns null.
	std::unique_ptr<AST::AstNode> make_udp_module(UdpParseData &udp);
}

YOSYS_NAMESPACE_END

#endif
