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
 */

#ifndef COST_H
#define COST_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

int get_cell_cost(RTLIL::Cell *cell, dict<RTLIL::IdString, int> *mod_cost_cache = nullptr);

int get_cell_cost(RTLIL::IdString type, const dict<RTLIL::IdString, RTLIL::Const> &parameters = dict<RTLIL::IdString, RTLIL::Const>(),
		RTLIL::Design *design = nullptr, dict<RTLIL::IdString, int> *mod_cost_cache = nullptr);

inline int get_cell_cost(RTLIL::Cell *cell, dict<RTLIL::IdString, int> *mod_cost_cache)
{
	return get_cell_cost(cell->type, cell->parameters, cell->module->design, mod_cost_cache);
}

YOSYS_NAMESPACE_END

#endif
