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
 *  A very simple and straightforward frontend for the RTLIL text
 *  representation.
 *
 */

#ifndef RTLIL_FRONTEND_H
#define RTLIL_FRONTEND_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace RTLIL_FRONTEND {
	extern std::istream *lexin;
	extern RTLIL::Design *current_design;
	extern bool flag_nooverwrite;
	extern bool flag_overwrite;
	extern bool flag_lib;
}

YOSYS_NAMESPACE_END

extern int rtlil_frontend_yydebug;
int rtlil_frontend_yylex(void);
void rtlil_frontend_yyerror(char const *s);
void rtlil_frontend_yyrestart(FILE *f);
int rtlil_frontend_yyparse(void);
int rtlil_frontend_yylex_destroy(void);
int rtlil_frontend_yyget_lineno(void);

#endif

