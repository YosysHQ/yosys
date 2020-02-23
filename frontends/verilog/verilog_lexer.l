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
 *  ---
 *
 *  A simple lexer for Verilog code. Non-preprocessor compiler directives are
 *  handled here. The preprocessor stuff is handled in preproc.cc. Everything
 *  else is left to the bison parser (see verilog_parser.y).
 *
 */

%{

#ifdef __clang__
// bison generates code using the 'register' storage class specifier
#pragma clang diagnostic ignored "-Wdeprecated-register"
#endif

#include "kernel/log.h"
#include "frontends/verilog/verilog_frontend.h"
#include "frontends/ast/ast.h"
#include "verilog_parser.tab.hh"

USING_YOSYS_NAMESPACE
using namespace AST;
using namespace VERILOG_FRONTEND;

YOSYS_NAMESPACE_BEGIN
namespace VERILOG_FRONTEND {
	std::vector<std::string> fn_stack;
	std::vector<int> ln_stack;
}
YOSYS_NAMESPACE_END

#define YYSTYPE FRONTEND_VERILOG_YYSTYPE
#define YYLTYPE FRONTEND_VERILOG_YYLTYPE

#define SV_KEYWORD(_tok) \
	if (sv_mode) return _tok; \
	log("Lexer warning: The SystemVerilog keyword `%s' (at %s:%d) is not "\
			"recognized unless read_verilog is called with -sv!\n", yytext, \
			AST::current_filename.c_str(), frontend_verilog_yyget_lineno()); \
	yylval->string = new std::string(std::string("\\") + yytext); \
	return TOK_ID;

#define NON_KEYWORD() \
	yylval->string = new std::string(std::string("\\") + yytext); \
	return TOK_ID;

#define YY_INPUT(buf,result,max_size) \
	result = readsome(*VERILOG_FRONTEND::lexin, buf, max_size)

YYLTYPE real_location;
YYLTYPE old_location;

#define YY_USER_ACTION \
       old_location = real_location; \
       real_location.first_line = real_location.last_line; \
       real_location.first_column = real_location.last_column; \
       for(int i = 0; yytext[i] != '\0'; ++i){ \
               if(yytext[i] == '\n') { \
                       real_location.last_line++; \
                       real_location.last_column = 1; \
               } \
               else { \
                       real_location.last_column++; \
               } \
       } \
    (*yylloc) = real_location;

#define YY_BREAK \
    (*yylloc) = old_location; \
    break;

#undef YY_BUF_SIZE
#define YY_BUF_SIZE 65536

extern int frontend_verilog_yylex(YYSTYPE *yylval_param, YYLTYPE *yyloc_param);
%}

%option yylineno
%option noyywrap
%option nounput
%option bison-locations
%option bison-bridge
%option prefix="frontend_verilog_yy"

%x COMMENT
%x STRING
%x SYNOPSYS_TRANSLATE_OFF
%x SYNOPSYS_FLAGS
%x IMPORT_DPI

%%

<INITIAL,SYNOPSYS_TRANSLATE_OFF>"`file_push "[^\n]* {
	fn_stack.push_back(current_filename);
	ln_stack.push_back(frontend_verilog_yyget_lineno());
	current_filename = yytext+11;
	if (!current_filename.empty() && current_filename.front() == '"')
		current_filename = current_filename.substr(1);
	if (!current_filename.empty() && current_filename.back() == '"')
		current_filename = current_filename.substr(0, current_filename.size()-1);
	frontend_verilog_yyset_lineno(0);
	yylloc->first_line = yylloc->last_line = 0;
	real_location.first_line = real_location.last_line = 0;
}

<INITIAL,SYNOPSYS_TRANSLATE_OFF>"`file_pop"[^\n]*\n {
	current_filename = fn_stack.back();
	fn_stack.pop_back();
	frontend_verilog_yyset_lineno(ln_stack.back());
	yylloc->first_line = yylloc->last_line = ln_stack.back();
	real_location.first_line = real_location.last_line = ln_stack.back();
	ln_stack.pop_back();
}

<INITIAL,SYNOPSYS_TRANSLATE_OFF>"`line"[ \t]+[^ \t\r\n]+[ \t]+\"[^ \r\n]+\"[^\r\n]*\n {
	char *p = yytext + 5;
	while (*p == ' ' || *p == '\t') p++;
	frontend_verilog_yyset_lineno(atoi(p));
	yylloc->first_line = yylloc->last_line = atoi(p);
	real_location.first_line = real_location.last_line = atoi(p);
	while (*p && *p != ' ' && *p != '\t') p++;
	while (*p == ' ' || *p == '\t') p++;
	char *q = *p ? p + 1 : p;
	while (*q && *q != '"') q++;
	current_filename = std::string(p).substr(1, q-p-1);
}

"`file_notfound "[^\n]* {
	log_error("Can't open include file `%s'!\n", yytext + 15);
}

"`timescale"[ \t]+[^ \t\r\n/]+[ \t]*"/"[ \t]*[^ \t\r\n]* /* ignore timescale directive */

"`celldefine"[^\n]* /* ignore `celldefine */
"`endcelldefine"[^\n]* /* ignore `endcelldefine */

"`default_nettype"[ \t]+[^ \t\r\n/]+ {
	char *p = yytext;
	while (*p != 0 && *p != ' ' && *p != '\t') p++;
	while (*p == ' ' || *p == '\t') p++;
	if (!strcmp(p, "none"))
		VERILOG_FRONTEND::default_nettype_wire = false;
	else if (!strcmp(p, "wire"))
		VERILOG_FRONTEND::default_nettype_wire = true;
	else
		frontend_verilog_yyerror("Unsupported default nettype: %s", p);
}

"`protect"[^\n]* /* ignore `protect*/
"`endprotect"[^\n]* /* ignore `endprotect*/

"`"[a-zA-Z_$][a-zA-Z0-9_$]* {
	frontend_verilog_yyerror("Unimplemented compiler directive or undefined macro %s.", yytext);
}

"module"       { return TOK_MODULE; }
"endmodule"    { return TOK_ENDMODULE; }
"function"     { return TOK_FUNCTION; }
"endfunction"  { return TOK_ENDFUNCTION; }
"task"         { return TOK_TASK; }
"endtask"      { return TOK_ENDTASK; }
"specify"      { return specify_mode ? TOK_SPECIFY : TOK_IGNORED_SPECIFY; }
"endspecify"   { return TOK_ENDSPECIFY; }
"specparam"    { return TOK_SPECPARAM; }
"package"      { SV_KEYWORD(TOK_PACKAGE); }
"endpackage"   { SV_KEYWORD(TOK_ENDPACKAGE); }
"interface"    { SV_KEYWORD(TOK_INTERFACE); }
"endinterface" { SV_KEYWORD(TOK_ENDINTERFACE); }
"modport"      { SV_KEYWORD(TOK_MODPORT); }
"parameter"    { return TOK_PARAMETER; }
"localparam"   { return TOK_LOCALPARAM; }
"defparam"     { return TOK_DEFPARAM; }
"assign"       { return TOK_ASSIGN; }
"always"       { return TOK_ALWAYS; }
"initial"      { return TOK_INITIAL; }
"begin"	       { return TOK_BEGIN; }
"end"          { return TOK_END; }
"if"           { return TOK_IF; }
"else"         { return TOK_ELSE; }
"for"          { return TOK_FOR; }
"posedge"      { return TOK_POSEDGE; }
"negedge"      { return TOK_NEGEDGE; }
"or"           { return TOK_OR; }
"case"         { return TOK_CASE; }
"casex"        { return TOK_CASEX; }
"casez"        { return TOK_CASEZ; }
"endcase"      { return TOK_ENDCASE; }
"default"      { return TOK_DEFAULT; }
"generate"     { return TOK_GENERATE; }
"endgenerate"  { return TOK_ENDGENERATE; }
"while"        { return TOK_WHILE; }
"repeat"       { return TOK_REPEAT; }
"automatic"    { return TOK_AUTOMATIC; }

"unique"       { SV_KEYWORD(TOK_UNIQUE); }
"unique0"      { SV_KEYWORD(TOK_UNIQUE); }
"priority"     { SV_KEYWORD(TOK_PRIORITY); }

"always_comb"  { SV_KEYWORD(TOK_ALWAYS_COMB); }
"always_ff"    { SV_KEYWORD(TOK_ALWAYS_FF); }
"always_latch" { SV_KEYWORD(TOK_ALWAYS_LATCH); }

 /* use special token for labels on assert, assume, cover, and restrict because it's insanley complex
    to fix parsing of cells otherwise. (the current cell parser forces a reduce very early to update some
    global state.. its a mess) */
[a-zA-Z_$][a-zA-Z0-9_$]*/[ \t\r\n]*:[ \t\r\n]*(assert|assume|cover|restrict)[^a-zA-Z0-9_$\.] {
	if (!strcmp(yytext, "default"))
		return TOK_DEFAULT;
	yylval->string = new std::string(std::string("\\") + yytext);
	return TOK_SVA_LABEL;
}

"assert"     { if (formal_mode) return TOK_ASSERT; SV_KEYWORD(TOK_ASSERT); }
"assume"     { if (formal_mode) return TOK_ASSUME; SV_KEYWORD(TOK_ASSUME); }
"cover"      { if (formal_mode) return TOK_COVER; SV_KEYWORD(TOK_COVER); }
"restrict"   { if (formal_mode) return TOK_RESTRICT; SV_KEYWORD(TOK_RESTRICT); }
"property"   { if (formal_mode) return TOK_PROPERTY; SV_KEYWORD(TOK_PROPERTY); }
"rand"       { if (formal_mode) return TOK_RAND; SV_KEYWORD(TOK_RAND); }
"const"      { if (formal_mode) return TOK_CONST; SV_KEYWORD(TOK_CONST); }
"checker"    { if (formal_mode) return TOK_CHECKER; SV_KEYWORD(TOK_CHECKER); }
"endchecker" { if (formal_mode) return TOK_ENDCHECKER; SV_KEYWORD(TOK_ENDCHECKER); }
"final"      { SV_KEYWORD(TOK_FINAL); }
"logic"      { SV_KEYWORD(TOK_LOGIC); }
"var"        { SV_KEYWORD(TOK_VAR); }
"bit"        { SV_KEYWORD(TOK_REG); }

"eventually"   { if (formal_mode) return TOK_EVENTUALLY; SV_KEYWORD(TOK_EVENTUALLY); }
"s_eventually" { if (formal_mode) return TOK_EVENTUALLY; SV_KEYWORD(TOK_EVENTUALLY); }

"input"   { return TOK_INPUT; }
"output"  { return TOK_OUTPUT; }
"inout"   { return TOK_INOUT; }
"wire"    { return TOK_WIRE; }
"wor"     { return TOK_WOR; }
"wand"    { return TOK_WAND; }
"reg"     { return TOK_REG; }
"integer" { return TOK_INTEGER; }
"signed"  { return TOK_SIGNED; }
"genvar"  { return TOK_GENVAR; }
"real"    { return TOK_REAL; }

"enum"    { SV_KEYWORD(TOK_ENUM); }
"typedef" { SV_KEYWORD(TOK_TYPEDEF); }

[0-9][0-9_]* {
	yylval->string = new std::string(yytext);
	return TOK_CONSTVAL;
}

[0-9]*[ \t]*\'[sS]?[bodhBODH]?[ \t\r\n]*[0-9a-fA-FzxZX?_]+ {
	yylval->string = new std::string(yytext);
	return TOK_CONSTVAL;
}

[0-9][0-9_]*\.[0-9][0-9_]*([eE][-+]?[0-9_]+)? {
	yylval->string = new std::string(yytext);
	return TOK_REALVAL;
}

[0-9][0-9_]*[eE][-+]?[0-9_]+ {
	yylval->string = new std::string(yytext);
	return TOK_REALVAL;
}

\"		{ BEGIN(STRING); }
<STRING>\\.	{ yymore(); real_location = old_location; }
<STRING>\"	{
	BEGIN(0);
	char *yystr = strdup(yytext);
	yystr[strlen(yytext) - 1] = 0;
	int i = 0, j = 0;
	while (yystr[i]) {
		if (yystr[i] == '\\' && yystr[i + 1]) {
			i++;
			if (yystr[i] == 'a')
				yystr[i] = '\a';
			else if (yystr[i] == 'f')
				yystr[i] = '\f';
			else if (yystr[i] == 'n')
				yystr[i] = '\n';
			else if (yystr[i] == 'r')
				yystr[i] = '\r';
			else if (yystr[i] == 't')
				yystr[i] = '\t';
			else if (yystr[i] == 'v')
				yystr[i] = '\v';
			else if ('0' <= yystr[i] && yystr[i] <= '7') {
				yystr[i] = yystr[i] - '0';
				if ('0' <= yystr[i + 1] && yystr[i + 1] <= '7') {
					yystr[i + 1] = yystr[i] * 8 + yystr[i + 1] - '0';
					i++;
				}
				if ('0' <= yystr[i + 1] && yystr[i + 1] <= '7') {
					yystr[i + 1] = yystr[i] * 8 + yystr[i + 1] - '0';
					i++;
				}
			}
		}
		yystr[j++] = yystr[i++];
	}
	yystr[j] = 0;
	yylval->string = new std::string(yystr, j);
	free(yystr);
	return TOK_STRING;
}
<STRING>.	{ yymore(); real_location = old_location; }

and|nand|or|nor|xor|xnor|not|buf|bufif0|bufif1|notif0|notif1 {
	yylval->string = new std::string(yytext);
	return TOK_PRIMITIVE;
}

supply0 { return TOK_SUPPLY0; }
supply1 { return TOK_SUPPLY1; }

"$"(display|write|strobe|monitor|time|stop|finish|dumpfile|dumpvars|dumpon|dumpoff|dumpall) {
	yylval->string = new std::string(yytext);
	return TOK_ID;
}

"$"(setup|hold|setuphold|removal|recovery|recrem|skew|timeskew|fullskew|nochange) {
	if (!specify_mode) REJECT;
	yylval->string = new std::string(yytext);
	return TOK_ID;
}

"$"(info|warning|error|fatal) {
	yylval->string = new std::string(yytext);
	return TOK_MSG_TASKS;
}

"$signed"   { return TOK_TO_SIGNED; }
"$unsigned" { return TOK_TO_UNSIGNED; }

[a-zA-Z_$][a-zA-Z0-9_$]* {
	yylval->string = new std::string(std::string("\\") + yytext);
	return TOK_ID;
}

[a-zA-Z_$][a-zA-Z0-9_$\.]* {
	yylval->string = new std::string(std::string("\\") + yytext);
	return TOK_ID;
}

"/*"[ \t]*(synopsys|synthesis)[ \t]*translate_off[ \t]*"*/" {
	static bool printed_warning = false;
	if (!printed_warning) {
		log_warning("Found one of those horrible `(synopsys|synthesis) translate_off' comments.\n"
				"Yosys does support them but it is recommended to use `ifdef constructs instead!\n");
		printed_warning = true;
	}
	BEGIN(SYNOPSYS_TRANSLATE_OFF);
}
<SYNOPSYS_TRANSLATE_OFF>.    /* ignore synopsys translate_off body */
<SYNOPSYS_TRANSLATE_OFF>\n   /* ignore synopsys translate_off body */
<SYNOPSYS_TRANSLATE_OFF>"/*"[ \t]*(synopsys|synthesis)[ \t]*"translate_on"[ \t]*"*/" { BEGIN(0); }

"/*"[ \t]*(synopsys|synthesis)[ \t]+ {
	BEGIN(SYNOPSYS_FLAGS);
}
<SYNOPSYS_FLAGS>full_case {
	static bool printed_warning = false;
	if (!printed_warning) {
		log_warning("Found one of those horrible `(synopsys|synthesis) full_case' comments.\n"
				"Yosys does support them but it is recommended to use Verilog `full_case' attributes instead!\n");
		printed_warning = true;
	}
	return TOK_SYNOPSYS_FULL_CASE;
}
<SYNOPSYS_FLAGS>parallel_case {
	static bool printed_warning = false;
	if (!printed_warning) {
		log_warning("Found one of those horrible `(synopsys|synthesis) parallel_case' comments.\n"
				"Yosys does support them but it is recommended to use Verilog `parallel_case' attributes instead!\n");
		printed_warning = true;
	}
	return TOK_SYNOPSYS_PARALLEL_CASE;
}
<SYNOPSYS_FLAGS>. /* ignore everything else */
<SYNOPSYS_FLAGS>"*/" { BEGIN(0); }

import[ \t\r\n]+\"(DPI|DPI-C)\"[ \t\r\n]+function[ \t\r\n]+ {
	BEGIN(IMPORT_DPI);
	return TOK_DPI_FUNCTION;
}

<IMPORT_DPI>[a-zA-Z_$][a-zA-Z0-9_$]* {
	yylval->string = new std::string(std::string("\\") + yytext);
	return TOK_ID;
}

<IMPORT_DPI>[ \t\r\n] /* ignore whitespaces */

<IMPORT_DPI>";" {
	BEGIN(0);
	return *yytext;
}

<IMPORT_DPI>. {
	return *yytext;
}

"\\"[^ \t\r\n]+ {
	yylval->string = new std::string(yytext);
	return TOK_ID;
}

"(*" { return ATTR_BEGIN; }
"*)" { return ATTR_END; }

"{*"  { return DEFATTR_BEGIN; }
"*}"  { return DEFATTR_END; }

"**" { return OP_POW; }
"||" { return OP_LOR; }
"&&" { return OP_LAND; }
"==" { return OP_EQ; }
"!=" { return OP_NE; }
"<=" { return OP_LE; }
">=" { return OP_GE; }

"===" { return OP_EQX; }
"!==" { return OP_NEX; }

"~&" { return OP_NAND; }
"~|" { return OP_NOR;  }
"~^" { return OP_XNOR; }
"^~" { return OP_XNOR; }

"<<"  { return OP_SHL; }
">>"  { return OP_SHR; }
"<<<" { return OP_SSHL; }
">>>" { return OP_SSHR; }

"::"  { return TOK_PACKAGESEP; }
"++"  { return TOK_INCREMENT; }
"--"  { return TOK_DECREMENT; }

"+:" { return TOK_POS_INDEXED; }
"-:" { return TOK_NEG_INDEXED; }

".*" { return TOK_WILDCARD_CONNECT; }

[-+]?[=*]> {
	if (!specify_mode) REJECT;
	yylval->string = new std::string(yytext);
	return TOK_SPECIFY_OPER;
}

"&&&" {
	if (!specify_mode) return TOK_IGNORED_SPECIFY_AND;
	return TOK_SPECIFY_AND;
}

"/*" { BEGIN(COMMENT); }
<COMMENT>.    /* ignore comment body */
<COMMENT>\n   /* ignore comment body */
<COMMENT>"*/" { BEGIN(0); }

[ \t\r\n]		/* ignore whitespaces */
\\[\r\n]		/* ignore continuation sequence */
"//"[^\r\n]*		/* ignore one-line comments */

. { return *yytext; }

%%

// this is a hack to avoid the 'yyinput defined but not used' error msgs
void *frontend_verilog_avoid_input_warnings() {
	return (void*)&yyinput;
}

