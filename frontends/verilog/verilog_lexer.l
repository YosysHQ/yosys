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
 *  ---
 *
 *  A simple lexer for Verilog code. Non-preprocessor compiler directives are
 *  handled here. The preprocessor stuff is handled in preproc.cc. Everything
 *  else is left to the bison parser (see verilog_parser.y).
 *
 */

%option c++
%option yyclass="VerilogLexer"
%option noyywrap
%option nounput
%option yylineno
%option prefix="frontend_verilog_yy"

%{

#ifdef __clang__
// bison generates code using the 'register' storage class specifier
#pragma clang diagnostic ignored "-Wdeprecated-register"
// flex generates weirdly-indented code
#pragma clang diagnostic ignored "-Wmisleading-indentation"
#endif

#include "frontends/verilog/verilog_lexer.h"
#include "frontends/ast/ast.h"
#include "frontends/verilog/verilog_location.h"
#include "kernel/log.h"
#include <vector>
#include <memory>

USING_YOSYS_NAMESPACE
using namespace AST;
using namespace VERILOG_FRONTEND;
using parser = frontend_verilog_yy::parser;

YOSYS_NAMESPACE_BEGIN
#undef YY_DECL
#define YY_DECL parser::symbol_type VerilogLexer::nextToken()

#undef yyterminate
#define yyterminate() return terminate()

YOSYS_NAMESPACE_END

#define SV_KEYWORD(_tok) \
	if (mode->sv) return _tok; \
	log("Lexer warning: The SystemVerilog keyword `%s' (at %s:%d) is not "\
			"recognized unless read_verilog is called with -sv!\n", YYText(), \
			current_filename->c_str(), yylineno); \
	string_t val = std::make_unique<std::string>(std::string("\\") + YYText()); \
	return parser::make_TOK_ID(std::move(val), out_loc);

#define NON_KEYWORD() \
	string_t val = std::make_unique<std::string>(std::string("\\") + YYText()); \
	return parser::make_TOK_ID(std::move(val), out_loc);


#define YY_USER_ACTION \
	out_loc.step(); \
	for(int i = 0; YYText()[i] != '\0'; ++i){ \
		if(YYText()[i] == '\n') { \
			out_loc.lines(); \
		} \
		else { \
			out_loc.columns(); \
		} \
	} \
	out_loc.begin.filename = current_filename; \
	out_loc.end.filename = current_filename;

#define YY_BREAK \
    break;

#undef YY_BUF_SIZE
#define YY_BUF_SIZE 65536

static bool isUserType(ParseState* extra, std::string &s)
{
	// check current scope then outer scopes for a name
	for (auto it = extra->user_type_stack.rbegin(); it != extra->user_type_stack.rend(); ++it) {
		if (it->count(s) > 0) {
				return true;
		}
	}
	return false;
}

parser::symbol_type char_tok(char c, parser::location_type loc) {
	switch (c) {
		case '!': return parser::make_TOK_EXCL(loc);
		case '#': return parser::make_TOK_HASH(loc);
		case '%': return parser::make_TOK_PERC(loc);
		case '&': return parser::make_TOK_AMP(loc);
		case '(': return parser::make_TOK_LPAREN(loc);
		case ')': return parser::make_TOK_RPAREN(loc);
		case '*': return parser::make_TOK_ASTER(loc);
		case '+': return parser::make_TOK_PLUS(loc);
		case ',': return parser::make_TOK_COMMA(loc);
		case '-': return parser::make_TOK_MINUS(loc);
		case '.': return parser::make_TOK_DOT(loc);
		case '/': return parser::make_TOK_SLASH(loc);
		case ':': return parser::make_TOK_COL(loc);
		case ';': return parser::make_TOK_SEMICOL(loc);
		case '<': return parser::make_TOK_LT(loc);
		case '=': return parser::make_TOK_EQ(loc);
		case '>': return parser::make_TOK_GT(loc);
		case '?': return parser::make_TOK_QUE(loc);
		case '@': return parser::make_TOK_AT(loc);
		case '[': return parser::make_TOK_LBRA(loc);
		case ']': return parser::make_TOK_RBRA(loc);
		case '^': return parser::make_TOK_CARET(loc);
		case '_': return parser::make_TOK_UNDER(loc);
		case '{': return parser::make_TOK_LCURL(loc);
		case '|': return parser::make_TOK_PIPE(loc);
		case '}': return parser::make_TOK_RCURL(loc);
		case '~': return parser::make_TOK_TILDE(loc);
		case 'n': return parser::make_TOK_n(loc);
		case 'p': return parser::make_TOK_p(loc);
		case 'x': return parser::make_TOK_x(loc);
		case 'z': return parser::make_TOK_z(loc);
		case 0: return parser::make_FRONTEND_VERILOG_YYEOF(loc);
		default:
			return parser::make_ch_t(c, loc);
	}
}
static bool is_hex_dig(char c, int *val, parser::location_type loc)
{
	if ('0' <= c && c <= '9') {
		*val = c - '0';
		return true;
	} else if ('a' <= c && c <= 'f') {
		*val = c - 'a' + 0xA;
		return true;
	} else if ('A' <= c && c <= 'F') {
		*val = c - 'A' + 0xA;
		return true;
	} else if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') {
		log_file_warning(*loc.begin.filename, loc.begin.line, "'%c' not a valid digit in hex escape sequence.\n", c);
		*val = 0; // not semantically valid in hex escape...
		return true; // ...but still processed as part of hex token
	}

	return false;
}

static bool is_oct_dig(char c, int *val, parser::location_type loc)
{
	if ('0' <= c && c <= '7') {
		*val = c - '0';
		return true;
	} else if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') {
		log_file_warning(*loc.begin.filename, loc.begin.line, "'%c' not a valid digit in octal escape sequence.\n", c);
		*val = 0; // not semantically valid in octal escape...
		return true; // ...but still processed as part of octal token
	}

	return false;
}

static parser::symbol_type process_str(char *str, int len, bool triple, parser::location_type loc)
{
	char *in, *out; // Overwrite input buffer: flex manual states "Actions
		// are free to modify 'yytext' except for lengthening it".

	for (in = str, out = str; in < str + len; in++)
		switch (*in) {
		case '\n':
		case '\r':
			if (in + 1 < str + len && (in[1] ^ *in) == ('\n' ^ '\r'))
				in++;
			if (!triple)
				log_file_warning(*loc.begin.filename, loc.begin.line, "Multi-line string literals should be triple-quoted or escaped.\n");
			*out++ = '\n';
			break;
		case '\\':
			in++;
			log_assert(in < str + len);
			switch (*in) {
			case 'a':
				*out++ = '\a';
				break;
			case 'f':
				*out++ = '\f';
				break;
			case 'n':
				*out++ = '\n';
				break;
			case 'r': /* not part of IEEE-1800 2023, but seems
				     like a good idea to support it anyway */
				*out++ = '\r';
				break;
			case 't':
				*out++ = '\t';
				break;
			case 'v':
				*out++ = '\v';
				break;
			case 'x':
				int val;
				if (in + 1 < str + len && is_hex_dig(in[1], &val, loc)) {
					*out = val;
					in++;
					if (in + 1 < str + len && is_hex_dig(in[1], &val, loc)) {
						*out = *out * 0x10 + val;
						in++;
					}
					out++;
				} else
					log_file_warning(*loc.begin.filename, loc.begin.line, "ignoring invalid hex escape.\n");
				break;
			case '\\':
				*out++ = '\\';
				break;
			case '"':
				*out++ = '"';
				break;
			case '\n':
			case '\r':
				if (in + 1 < str + len && (in[1] ^ *in) == ('\n' ^ '\r'))
					in++;
				break;
			default:
				if ('0' <= *in && *in <= '7') {
					int val;

					*out = *in - '0';
					if (in + 1 < str + len && is_oct_dig(in[1], &val, loc)) {
						*out = *out * 010 + val;
						in++;
						if (in + 1 < str + len && is_oct_dig(in[1], &val, loc)) {
							if (*out >= 040)
								log_file_warning(*loc.begin.filename, loc.begin.line, "octal escape exceeds \\377\n");
							*out = *out * 010 + val;
							in++;
						}
					}
					out++;
				} else
					*out++ = *in;
			}
			break;
		default:
			*out++ = *in;
		}

	return parser::make_TOK_STRING(std::make_unique<std::string>(str, out - str), loc);
}

%}

%x COMMENT
%x SYNOPSYS_TRANSLATE_OFF
%x SYNOPSYS_FLAGS
%x IMPORT_DPI
%x BASED_CONST

UNSIGNED_NUMBER [0-9][0-9_]*
FIXED_POINT_NUMBER_DEC [0-9][0-9_]*\.[0-9][0-9_]*([eE][-+]?[0-9_]+)?
FIXED_POINT_NUMBER_NO_DEC [0-9][0-9_]*[eE][-+]?[0-9_]+
TIME_SCALE_SUFFIX [munpf]?s

%%

	// Initialise comment_caller to something to avoid a "maybe undefined"
	// warning from GCC.
	int comment_caller = INITIAL;

<INITIAL,SYNOPSYS_TRANSLATE_OFF>"`file_push "[^\n]* {
	fn_stack.push_back(current_filename);
	ln_stack.push_back(yylineno);
	std::string filename = YYText()+11;
	if (!filename.empty() && filename.front() == '"')
		filename = filename.substr(1);
	if (!filename.empty() && filename.back() == '"')
		filename = filename.substr(0, filename.size()-1);
	current_filename = std::make_shared<std::string>(filename);
	yylineno = (0);
	out_loc.begin.line = out_loc.end.line = 0;
}

<INITIAL,SYNOPSYS_TRANSLATE_OFF>"`file_pop"[^\n]*\n {
	current_filename = fn_stack.back();
	fn_stack.pop_back();
	yylineno = (ln_stack.back());
	out_loc.begin.line = out_loc.end.line = ln_stack.back();
	ln_stack.pop_back();
}

<INITIAL,SYNOPSYS_TRANSLATE_OFF>"`line"[ \t]+[^ \t\r\n]+[ \t]+\"[^ \r\n]+\"[^\r\n]*\n {
	const char *p = YYText() + 5;
	while (*p == ' ' || *p == '\t') p++;
	yylineno = (atoi(p));
	out_loc.begin.line = out_loc.end.line = atoi(p);
	while (*p && *p != ' ' && *p != '\t') p++;
	while (*p == ' ' || *p == '\t') p++;
	const char *q = *p ? p + 1 : p;
	while (*q && *q != '"') q++;
	current_filename = std::make_shared<std::string>(std::string(p).substr(1, q-p-1));
}

"`file_notfound "[^\n]* {
	log_error("Can't open include file `%s'!\n", YYText() + 15);
}

"`timescale"[ \t]+[^ \t\r\n/]+[ \t]*"/"[ \t]*[^ \t\r\n]* /* ignore timescale directive */

"`celldefine"[^\n]* /* ignore `celldefine */
"`endcelldefine"[^\n]* /* ignore `endcelldefine */

"`default_nettype"[ \t]+[^ \t\r\n/]+ {
	const char *p = YYText();
	while (*p != 0 && *p != ' ' && *p != '\t') p++;
	while (*p == ' ' || *p == '\t') p++;
	if (!strcmp(p, "none"))
		extra->default_nettype_wire = false;
	else if (!strcmp(p, "wire"))
		extra->default_nettype_wire = true;
	else
		err_at_loc(out_loc, "Unsupported default nettype: %s", p);
}

"`protect"[^\n]* /* ignore `protect*/
"`endprotect"[^\n]* /* ignore `endprotect*/

"`"[a-zA-Z_$][a-zA-Z0-9_$]* {
	err_at_loc(out_loc, "Unimplemented compiler directive or undefined macro %s.", YYText());
}

"module"       { return parser::make_TOK_MODULE(out_loc); }
"endmodule"    { return parser::make_TOK_ENDMODULE(out_loc); }
"function"     { return parser::make_TOK_FUNCTION(out_loc); }
"endfunction"  { return parser::make_TOK_ENDFUNCTION(out_loc); }
"task"         { return parser::make_TOK_TASK(out_loc); }
"endtask"      { return parser::make_TOK_ENDTASK(out_loc); }
"specify"      { return mode->specify ? parser::make_TOK_SPECIFY(out_loc) : parser::make_TOK_IGNORED_SPECIFY(out_loc); }
"endspecify"   { return parser::make_TOK_ENDSPECIFY(out_loc); }
"specparam"    { return parser::make_TOK_SPECPARAM(out_loc); }
"package"      { SV_KEYWORD(parser::make_TOK_PACKAGE(out_loc)); }
"endpackage"   { SV_KEYWORD(parser::make_TOK_ENDPACKAGE(out_loc)); }
"import"       { SV_KEYWORD(parser::make_TOK_IMPORT(out_loc)); }
"interface"    { SV_KEYWORD(parser::make_TOK_INTERFACE(out_loc)); }
"endinterface" { SV_KEYWORD(parser::make_TOK_ENDINTERFACE(out_loc)); }
"modport"      { SV_KEYWORD(parser::make_TOK_MODPORT(out_loc)); }
"parameter"    { return parser::make_TOK_PARAMETER(out_loc); }
"localparam"   { return parser::make_TOK_LOCALPARAM(out_loc); }
"defparam"     { return parser::make_TOK_DEFPARAM(out_loc); }
"assign"       { return parser::make_TOK_ASSIGN(out_loc); }
"always"       { return parser::make_TOK_ALWAYS(out_loc); }
"initial"      { return parser::make_TOK_INITIAL(out_loc); }
"begin"	       { return parser::make_TOK_BEGIN(out_loc); }
"end"          { return parser::make_TOK_END(out_loc); }
"if"           { return parser::make_TOK_IF(out_loc); }
"ifnone"       { return parser::make_TOK_IFNONE(out_loc); }
"else"         { return parser::make_TOK_ELSE(out_loc); }
"for"          { return parser::make_TOK_FOR(out_loc); }
"posedge"      { return parser::make_TOK_POSEDGE(out_loc); }
"negedge"      { return parser::make_TOK_NEGEDGE(out_loc); }
"or"           { return parser::make_TOK_OR(out_loc); }
"case"         { return parser::make_TOK_CASE(out_loc); }
"casex"        { return parser::make_TOK_CASEX(out_loc); }
"casez"        { return parser::make_TOK_CASEZ(out_loc); }
"endcase"      { return parser::make_TOK_ENDCASE(out_loc); }
"default"      { return parser::make_TOK_DEFAULT(out_loc); }
"generate"     { return parser::make_TOK_GENERATE(out_loc); }
"endgenerate"  { return parser::make_TOK_ENDGENERATE(out_loc); }
"while"        { return parser::make_TOK_WHILE(out_loc); }
"repeat"       { return parser::make_TOK_REPEAT(out_loc); }
"automatic"    { return parser::make_TOK_AUTOMATIC(out_loc); }

"unique"       { SV_KEYWORD(parser::make_TOK_UNIQUE(out_loc)); }
"unique0"      { SV_KEYWORD(parser::make_TOK_UNIQUE0(out_loc)); }
"priority"     { SV_KEYWORD(parser::make_TOK_PRIORITY(out_loc)); }

"always_comb"  { SV_KEYWORD(parser::make_TOK_ALWAYS_COMB(out_loc)); }
"always_ff"    { SV_KEYWORD(parser::make_TOK_ALWAYS_FF(out_loc)); }
"always_latch" { SV_KEYWORD(parser::make_TOK_ALWAYS_LATCH(out_loc)); }

 /* use special token for labels on assert, assume, cover, and restrict because it's insanley complex
    to fix parsing of cells otherwise. (the current cell parser forces a reduce very early to update some
    global state.. its a mess) */
[a-zA-Z_$][a-zA-Z0-9_$]*/[ \t\r\n]*:[ \t\r\n]*(assert|assume|cover|restrict)[^a-zA-Z0-9_$\.] {
	if (!strcmp(YYText(), "default"))
		return parser::make_TOK_DEFAULT(out_loc);
	string_t val = std::make_unique<std::string>(std::string("\\") + YYText());
	return parser::make_TOK_SVA_LABEL(std::move(val), out_loc);
}

"assert"     { if (mode->formal) return parser::make_TOK_ASSERT(out_loc); SV_KEYWORD(parser::make_TOK_ASSERT(out_loc)); }
"assume"     { if (mode->formal) return parser::make_TOK_ASSUME(out_loc); SV_KEYWORD(parser::make_TOK_ASSUME(out_loc)); }
"cover"      { if (mode->formal) return parser::make_TOK_COVER(out_loc); SV_KEYWORD(parser::make_TOK_COVER(out_loc)); }
"restrict"   { if (mode->formal) return parser::make_TOK_RESTRICT(out_loc); SV_KEYWORD(parser::make_TOK_RESTRICT(out_loc)); }
"property"   { if (mode->formal) return parser::make_TOK_PROPERTY(out_loc); SV_KEYWORD(parser::make_TOK_PROPERTY(out_loc)); }
"rand"       { if (mode->formal) return parser::make_TOK_RAND(out_loc); SV_KEYWORD(parser::make_TOK_RAND(out_loc)); }
"const"      { if (mode->formal) return parser::make_TOK_CONST(out_loc); SV_KEYWORD(parser::make_TOK_CONST(out_loc)); }
"checker"    { if (mode->formal) return parser::make_TOK_CHECKER(out_loc); SV_KEYWORD(parser::make_TOK_CHECKER(out_loc)); }
"endchecker" { if (mode->formal) return parser::make_TOK_ENDCHECKER(out_loc); SV_KEYWORD(parser::make_TOK_ENDCHECKER(out_loc)); }
"bind"       { if (mode->formal) return parser::make_TOK_BIND(out_loc); SV_KEYWORD(parser::make_TOK_BIND(out_loc)); }
"final"      { SV_KEYWORD(parser::make_TOK_FINAL(out_loc)); }
"logic"      { SV_KEYWORD(parser::make_TOK_LOGIC(out_loc)); }
"var"        { SV_KEYWORD(parser::make_TOK_VAR(out_loc)); }
"bit"        { SV_KEYWORD(parser::make_TOK_LOGIC(out_loc)); }
"int"        { SV_KEYWORD(parser::make_TOK_INT(out_loc)); }
"byte"       { SV_KEYWORD(parser::make_TOK_BYTE(out_loc)); }
"shortint"   { SV_KEYWORD(parser::make_TOK_SHORTINT(out_loc)); }
"longint"    { SV_KEYWORD(parser::make_TOK_LONGINT(out_loc)); }
"void"       { SV_KEYWORD(parser::make_TOK_VOID(out_loc)); }

"eventually"   { if (mode->formal) return parser::make_TOK_EVENTUALLY(out_loc); SV_KEYWORD(parser::make_TOK_EVENTUALLY(out_loc)); }
"s_eventually" { if (mode->formal) return parser::make_TOK_EVENTUALLY(out_loc); SV_KEYWORD(parser::make_TOK_EVENTUALLY(out_loc)); }

"input"   { return parser::make_TOK_INPUT(out_loc); }
"output"  { return parser::make_TOK_OUTPUT(out_loc); }
"inout"   { return parser::make_TOK_INOUT(out_loc); }
"wire"    { return parser::make_TOK_WIRE(out_loc); }
"tri"     { return parser::make_TOK_WIRE(out_loc); }
"wor"     { return parser::make_TOK_WOR(out_loc); }
"trior"   { return parser::make_TOK_WOR(out_loc); }
"wand"    { return parser::make_TOK_WAND(out_loc); }
"triand"  { return parser::make_TOK_WAND(out_loc); }
"reg"     { return parser::make_TOK_REG(out_loc); }
"integer" { return parser::make_TOK_INTEGER(out_loc); }
"signed"  { return parser::make_TOK_SIGNED(out_loc); }
"unsigned" { SV_KEYWORD(parser::make_TOK_UNSIGNED(out_loc)); }
"genvar"  { return parser::make_TOK_GENVAR(out_loc); }
"real"    { return parser::make_TOK_REAL(out_loc); }

"enum"    { SV_KEYWORD(parser::make_TOK_ENUM(out_loc)); }
"typedef" { SV_KEYWORD(parser::make_TOK_TYPEDEF(out_loc)); }
"struct"  { SV_KEYWORD(parser::make_TOK_STRUCT(out_loc)); }
"union"   { SV_KEYWORD(parser::make_TOK_UNION(out_loc)); }
"packed"  { SV_KEYWORD(parser::make_TOK_PACKED(out_loc)); }

{UNSIGNED_NUMBER} {
	string_t val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_CONSTVAL(std::move(val), out_loc);
}

\'[01zxZX] {
	string_t val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_UNBASED_UNSIZED_CONSTVAL(std::move(val), out_loc);
}

\'[sS]?[bodhBODH] {
	BEGIN(BASED_CONST);
	string_t val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_BASE(std::move(val), out_loc);
}

<BASED_CONST>[0-9a-fA-FzxZX?][0-9a-fA-FzxZX?_]* {
	BEGIN(0);
	string_t val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_BASED_CONSTVAL(std::move(val), out_loc);
}

{FIXED_POINT_NUMBER_DEC} {
	string_t val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_REALVAL(std::move(val), out_loc);
}

{FIXED_POINT_NUMBER_NO_DEC} {
	string_t val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_REALVAL(std::move(val), out_loc);
}

\"([^\\"]|\\.|\\\n)*\"			{ return process_str(yytext + 1, yyleng - 2, false, out_loc); }

\"{3}(\"{0,2}([^\\"]|\\.|\\\n))*\"{3}	{ return process_str(yytext + 3, yyleng - 6, true, out_loc); }

and|nand|or|nor|xor|xnor|not|buf|bufif0|bufif1|notif0|notif1|tran {
	auto val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_PRIMITIVE(std::move(val), out_loc);
}

supply0 { return parser::make_TOK_SUPPLY0(out_loc); }
supply1 { return parser::make_TOK_SUPPLY1(out_loc); }

"$"(display[bho]?|write[bho]?|strobe|monitor|time|realtime|stop|finish|dumpfile|dumpvars|dumpon|dumpoff|dumpall) {
	auto val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_ID(std::move(val), out_loc);
}

"$"(setup|hold|setuphold|removal|recovery|recrem|skew|timeskew|fullskew|nochange) {
	if (!mode->specify) REJECT;
	auto val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_ID(std::move(val), out_loc);
}

"$"(info|warning|error|fatal) {
	auto val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_MSG_TASKS(std::move(val), out_loc);
}

"$signed"   { return parser::make_TOK_TO_SIGNED(out_loc); }
"$unsigned" { return parser::make_TOK_TO_UNSIGNED(out_loc); }

[a-zA-Z_][a-zA-Z0-9_]*::[a-zA-Z_$][a-zA-Z0-9_$]* {
	// package qualifier
	auto s = std::string("\\") + YYText();
	if (extra->pkg_user_types.count(s) > 0) {
		// package qualified typedefed name
		auto val = std::make_unique<std::string>(s);
		return parser::make_TOK_PKG_USER_TYPE(std::move(val), out_loc);
	}
	else {
		// backup before :: just return first part
		size_t len = strchr(YYText(), ':') - YYText();
		yyless(len);
		auto val = std::make_unique<std::string>(std::string("\\") + YYText());
		return parser::make_TOK_ID(std::move(val), out_loc);
	}
}

[a-zA-Z_$][a-zA-Z0-9_$]* {
	auto s = std::string("\\") + YYText();
	if (isUserType(extra, s)) {
		// previously typedefed name
		auto val = std::make_unique<std::string>(s);
		return parser::make_TOK_USER_TYPE(std::move(val), out_loc);
	}
	else {
		auto val = std::make_unique<std::string>(std::string("\\") + YYText());
		return parser::make_TOK_ID(std::move(val), out_loc);
	}
}

[a-zA-Z_$][a-zA-Z0-9_$\.]* {
	auto val = std::make_unique<std::string>(std::string("\\") + YYText());
	return parser::make_TOK_ID(std::move(val), out_loc);
}

"/*"[ \t]*(synopsys|synthesis)[ \t]*translate_off[ \t]*"*/" {
	static bool printed_warning = false;
	if (!printed_warning) {
		log_warning(
			"Encountered `translate_off' comment! Such legacy hot "
			"comments are supported by Yosys, but are not part of "
			"any formal language specification. Using a portable "
			"and standards-compliant construct such as `ifdef is "
			"recommended!\n"
		);
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
		log_warning(
			"Encountered `full_case' comment! Such legacy hot "
			"comments are supported by Yosys, but are not part of "
			"any formal language specification. Using the Verilog "
			"`full_case' attribute or the SystemVerilog `unique' "
			"or `unique0' keywords is recommended!\n"
		);
		printed_warning = true;
	}
	return parser::make_TOK_SYNOPSYS_FULL_CASE(out_loc);
}
<SYNOPSYS_FLAGS>parallel_case {
	static bool printed_warning = false;
	if (!printed_warning) {
		log_warning(
			"Encountered `parallel_case' comment! Such legacy hot "
			"comments are supported by Yosys, but are not part of "
			"any formal language specification. Using the Verilog "
			"`parallel_case' attribute or the SystemVerilog "
			"`unique' or `priority' keywords is recommended!\n"
		);
		printed_warning = true;
	}
	return parser::make_TOK_SYNOPSYS_PARALLEL_CASE(out_loc);
}
<SYNOPSYS_FLAGS>. /* ignore everything else */
<SYNOPSYS_FLAGS>"*/" { BEGIN(0); }

import[ \t\r\n]+\"(DPI|DPI-C)\"[ \t\r\n]+function[ \t\r\n]+ {
	BEGIN(IMPORT_DPI);
	return parser::make_TOK_DPI_FUNCTION(out_loc);
}

<IMPORT_DPI>[a-zA-Z_$][a-zA-Z0-9_$]* {
	auto val = std::make_unique<std::string>(std::string("\\") + YYText());
	return parser::make_TOK_ID(std::move(val), out_loc);
}

<IMPORT_DPI>[ \t\r\n] /* ignore whitespaces */

<IMPORT_DPI>";" {
	BEGIN(0);
	return char_tok(*YYText(), out_loc);
}

<IMPORT_DPI>. {
	return char_tok(*YYText(), out_loc);
}

"\\"[^ \t\r\n]+ {
	auto val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_ID(std::move(val), out_loc);
}

"(*" { return parser::make_ATTR_BEGIN(out_loc); }
"*)" { return parser::make_ATTR_END(out_loc); }

"{*"  { return parser::make_DEFATTR_BEGIN(out_loc); }
"*}"  { return parser::make_DEFATTR_END(out_loc); }

"**" { return parser::make_OP_POW(out_loc); }
"||" { return parser::make_OP_LOR(out_loc); }
"&&" { return parser::make_OP_LAND(out_loc); }
"==" { return parser::make_OP_EQ(out_loc); }
"!=" { return parser::make_OP_NE(out_loc); }
"<=" { return parser::make_OP_LE(out_loc); }
">=" { return parser::make_OP_GE(out_loc); }

"===" { return parser::make_OP_EQX(out_loc); }
"!==" { return parser::make_OP_NEX(out_loc); }

"~&" { return parser::make_OP_NAND(out_loc); }
"~|" { return parser::make_OP_NOR(out_loc);  }
"~^" { return parser::make_OP_XNOR(out_loc); }
"^~" { return parser::make_OP_XNOR(out_loc); }

"<<"  { return parser::make_OP_SHL(out_loc); }
">>"  { return parser::make_OP_SHR(out_loc); }
"<<<" { return parser::make_OP_SSHL(out_loc); }
">>>" { return parser::make_OP_SSHR(out_loc); }

"'" { return parser::make_OP_CAST(out_loc); }

"::"  { return parser::make_TOK_PACKAGESEP(out_loc); }
"++"  { return parser::make_TOK_INCREMENT(out_loc); }
"--"  { return parser::make_TOK_DECREMENT(out_loc); }

"+:" { return parser::make_TOK_POS_INDEXED(out_loc); }
"-:" { return parser::make_TOK_NEG_INDEXED(out_loc); }

".*" { return parser::make_TOK_WILDCARD_CONNECT(out_loc); }

"|=" { SV_KEYWORD(parser::make_TOK_BIT_OR_ASSIGN(out_loc)); }
"&=" { SV_KEYWORD(parser::make_TOK_BIT_AND_ASSIGN(out_loc)); }
"+=" { SV_KEYWORD(parser::make_TOK_ADD_ASSIGN(out_loc)); }
"-=" { SV_KEYWORD(parser::make_TOK_SUB_ASSIGN(out_loc)); }
"^=" { SV_KEYWORD(parser::make_TOK_BIT_XOR_ASSIGN(out_loc)); }
"/=" { SV_KEYWORD(parser::make_TOK_DIV_ASSIGN(out_loc)); }
"%=" { SV_KEYWORD(parser::make_TOK_MOD_ASSIGN(out_loc)); }
"*=" { SV_KEYWORD(parser::make_TOK_MUL_ASSIGN(out_loc)); }
"<<=" { SV_KEYWORD(parser::make_TOK_SHL_ASSIGN(out_loc)); }
">>=" { SV_KEYWORD(parser::make_TOK_SHR_ASSIGN(out_loc)); }
"<<<=" { SV_KEYWORD(parser::make_TOK_SSHL_ASSIGN(out_loc)); }
">>>=" { SV_KEYWORD(parser::make_TOK_SSHR_ASSIGN(out_loc)); }

[-+]?[=*]> {
	if (!mode->specify) REJECT;
	auto val = std::make_unique<std::string>(YYText());
	return parser::make_TOK_SPECIFY_OPER(std::move(val), out_loc);
}

"&&&" {
	if (!mode->specify) return parser::make_TOK_IGNORED_SPECIFY_AND(out_loc);
	return parser::make_TOK_SPECIFY_AND(out_loc);
}

{UNSIGNED_NUMBER}{TIME_SCALE_SUFFIX} { return parser::make_TOK_TIME_SCALE(out_loc); }
{FIXED_POINT_NUMBER_DEC}{TIME_SCALE_SUFFIX} { return parser::make_TOK_TIME_SCALE(out_loc); }
{FIXED_POINT_NUMBER_NO_DEC}{TIME_SCALE_SUFFIX} { return parser::make_TOK_TIME_SCALE(out_loc); }

<INITIAL,BASED_CONST>"/*" { comment_caller=YY_START; BEGIN(COMMENT); }
<COMMENT>.    /* ignore comment body */
<COMMENT>\n   /* ignore comment body */
<COMMENT>"*/" { BEGIN(comment_caller); }


<INITIAL,BASED_CONST>[ \t\r\n]		/* ignore whitespaces */
<INITIAL,BASED_CONST>\\[\r\n]		/* ignore continuation sequence */
<INITIAL,BASED_CONST>"//"[^\r\n]*	/* ignore one-line comments */

<INITIAL>. { return char_tok(*YYText(), out_loc); }
<*>. { BEGIN(0); return char_tok(*YYText(), out_loc); }

%%

