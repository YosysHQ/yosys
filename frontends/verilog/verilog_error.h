#ifndef VERILOG_ERROR_H
#define VERILOG_ERROR_H

#include "kernel/yosys_common.h"
#include "frontends/ast/ast.h"
#include "frontends/verilog/verilog_location.h"

#if ! defined(yyFlexLexerOnce)
#define yyFlexLexer frontend_verilog_yyFlexLexer
#include <FlexLexer.h>
#endif

YOSYS_NAMESPACE_BEGIN

namespace VERILOG_FRONTEND
{
    [[noreturn]]
    void err_at_ast(AST::AstSrcLocType loc, char const *fmt, ...);
    [[noreturn]]
    void err_at_loc(location loc, char const *fmt, ...);
};

YOSYS_NAMESPACE_END

#endif
