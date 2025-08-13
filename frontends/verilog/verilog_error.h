#ifndef VERILOG_ERROR_H
#define VERILOG_ERROR_H

#include "kernel/yosys_common.h"
#include "frontends/ast/ast.h"
#include "frontends/verilog/verilog_location.h"

YOSYS_NAMESPACE_BEGIN

namespace VERILOG_FRONTEND
{
    [[noreturn]]
    void err_at_loc(Location loc, char const *fmt, ...);
    void warn_at_loc(Location loc, char const *fmt, ...);
};

YOSYS_NAMESPACE_END

#endif
