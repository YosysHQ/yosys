#ifndef VERILOG_ERROR_H
#define VERILOG_ERROR_H

#include "kernel/yosys_common.h"
#include "frontends/ast/ast.h"
#include "frontends/verilog/verilog_location.h"

YOSYS_NAMESPACE_BEGIN

namespace VERILOG_FRONTEND
{
    [[noreturn]]
    void formatted_err_at_loc(Location loc, std::string str);
    template <typename... Args>
    [[noreturn]]
    void err_at_loc(Location loc, FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
    {
        formatted_err_at_loc(std::move(loc), fmt.format(args...));
    }

    void formatted_warn_at_loc(Location loc, std::string str);
    template <typename... Args>
    void warn_at_loc(Location loc, FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
    {
        formatted_warn_at_loc(std::move(loc), fmt.format(args...));
    }
};

YOSYS_NAMESPACE_END

#endif
