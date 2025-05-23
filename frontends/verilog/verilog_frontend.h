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
 *  ---
 *
 *  The Verilog frontend.
 *
 *  This frontend is using the AST frontend library (see frontends/ast/).
 *  Thus this frontend does not generate RTLIL code directly but creates an
 *  AST directly from the Verilog parse tree and then passes this AST to
 *  the AST frontend library.
 *
 */

#ifndef VERILOG_FRONTEND_H
#define VERILOG_FRONTEND_H

#include "kernel/yosys.h"
#include "frontends/ast/ast.h"

#if ! defined(yyFlexLexerOnce)
#define yyFlexLexer frontend_verilog_yyFlexLexer
#include <FlexLexer.h>
#endif

#include <stdio.h>
#include <stdint.h>
#include <list>

YOSYS_NAMESPACE_BEGIN

namespace VERILOG_FRONTEND
{
	// this function converts a Verilog constant to an AST_CONSTANT node
	std::unique_ptr<AST::AstNode> const2ast(std::string code, char case_type = 0, bool warn_z = false);
	extern void frontend_verilog_yyerror(char const *fmt, ...);
};

YOSYS_NAMESPACE_END

#endif
