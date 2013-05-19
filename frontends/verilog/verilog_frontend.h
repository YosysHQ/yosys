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

#include "kernel/rtlil.h"
#include "frontends/ast/ast.h"
#include <stdio.h>
#include <stdint.h>

namespace VERILOG_FRONTEND
{
	// this variable is set to a new AST_DESIGN node and then filled with the AST by the bison parser
	extern struct AST::AstNode *current_ast;

	// this function converts a Verilog constant to an AST_CONSTANT node
	AST::AstNode *const2ast(std::string code, char case_type = 0);

	// lexer state variables
	extern bool lexer_feature_defattr;
}

// the pre-processor
std::string frontend_verilog_preproc(FILE *f, std::string filename, const std::map<std::string, std::string> pre_defines_map);

// the usual bison/flex stuff
extern int frontend_verilog_yydebug;
int frontend_verilog_yylex(void);
void frontend_verilog_yyerror(char const *fmt, ...);
void frontend_verilog_yyrestart(FILE *f);
int frontend_verilog_yyparse(void);
int frontend_verilog_yylex_destroy(void);
int frontend_verilog_yyget_lineno(void);
void frontend_verilog_yyset_lineno (int);

#endif
