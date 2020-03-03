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
 */

#ifndef VERILOG_FRONTEND_H
#define VERILOG_FRONTEND_H

#include "kernel/yosys.h"
#include "frontends/ast/ast.h"
#include <stdio.h>
#include <stdint.h>
#include <list>

YOSYS_NAMESPACE_BEGIN

namespace VERILOG_FRONTEND
{
	// this variable is set to a new AST_DESIGN node and then filled with the AST by the bison parser
	extern struct AST::AstNode *current_ast;

	// this function converts a Verilog constant to an AST_CONSTANT node
	AST::AstNode *const2ast(std::string code, char case_type = 0, bool warn_z = false);

	// state of `default_nettype
	extern bool default_nettype_wire;

	// running in SystemVerilog mode
	extern bool sv_mode;

	// running in -formal mode
	extern bool formal_mode;

	// running in -noassert mode
	extern bool noassert_mode;

	// running in -noassume mode
	extern bool noassume_mode;

	// running in -norestrict mode
	extern bool norestrict_mode;

	// running in -assume-asserts mode
	extern bool assume_asserts_mode;

	// running in -assert-assumes mode
	extern bool assert_assumes_mode;

	// running in -lib mode
	extern bool lib_mode;

	// running in -specify mode
	extern bool specify_mode;

	// lexer input stream
	extern std::istream *lexin;
}

// the pre-processor
std::string frontend_verilog_preproc(std::istream &f, std::string filename, const std::map<std::string, std::string> &pre_defines_map,
		dict<std::string, std::pair<std::string, bool>> &global_defines_cache, const std::list<std::string> &include_dirs);

YOSYS_NAMESPACE_END

// the usual bison/flex stuff
extern int frontend_verilog_yydebug;
void frontend_verilog_yyerror(char const *fmt, ...);
void frontend_verilog_yyrestart(FILE *f);
int frontend_verilog_yyparse(void);
int frontend_verilog_yylex_destroy(void);
int frontend_verilog_yyget_lineno(void);
void frontend_verilog_yyset_lineno (int);

#endif
