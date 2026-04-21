/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018  Ruben Undheim <ruben.undheim@gmail.com>
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
 */

#ifndef HIERARCHY_VERILOG_H
#define HIERARCHY_VERILOG_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace Hierarchy {
    void resolve_verilog(Design* design, bool nodefaults, bool keep_positionals, bool keep_portwidths, bool top_is_from_verific);
    void resolve_wildcards(Cell* cell, std::set<Module*>& blackbox_derivatives, bool nodefaults, dict<IdString, dict<IdString, Const>>& defaults_db);
    void resolve_wand_wor(Module* module, std::set<Module*>& blackbox_derivatives, bool keep_portwidths, bool top_is_from_verific);
    void check_supported_formal(Design* design);
};

YOSYS_NAMESPACE_END

#endif /* HIERARCHY_VERILOG_H */
