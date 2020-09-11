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

struct CellCosts
{
	static const dict<RTLIL::IdString, int>& default_gate_cost() {
		static const dict<RTLIL::IdString, int> db = {
			{ ID($_BUF_),    1 },
			{ ID($_NOT_),    2 },
			{ ID($_AND_),    4 },
			{ ID($_NAND_),   4 },
			{ ID($_OR_),     4 },
			{ ID($_NOR_),    4 },
			{ ID($_ANDNOT_), 4 },
			{ ID($_ORNOT_),  4 },
			{ ID($_XOR_),    5 },
			{ ID($_XNOR_),   5 },
			{ ID($_AOI3_),   6 },
			{ ID($_OAI3_),   6 },
			{ ID($_AOI4_),   7 },
			{ ID($_OAI4_),   7 },
			{ ID($_MUX_),    4 },
			{ ID($_NMUX_),   4 }
		};
		return db;
	}

	static const dict<RTLIL::IdString, int>& cmos_gate_cost() {
		static const dict<RTLIL::IdString, int> db = {
			{ ID($_BUF_),     1 },
			{ ID($_NOT_),     2 },
			{ ID($_AND_),     6 },
			{ ID($_NAND_),    4 },
			{ ID($_OR_),      6 },
			{ ID($_NOR_),     4 },
			{ ID($_ANDNOT_),  6 },
			{ ID($_ORNOT_),   6 },
			{ ID($_XOR_),    12 },
			{ ID($_XNOR_),   12 },
			{ ID($_AOI3_),    6 },
			{ ID($_OAI3_),    6 },
			{ ID($_AOI4_),    8 },
			{ ID($_OAI4_),    8 },
			{ ID($_MUX_),    12 },
			{ ID($_NMUX_),   10 }
		};
		return db;
	}

	dict<RTLIL::IdString, int> mod_cost_cache;
	const dict<RTLIL::IdString, int> *gate_cost = nullptr;
	Design *design = nullptr;

	int get(RTLIL::IdString type) const
	{
		if (gate_cost && gate_cost->count(type))
			return gate_cost->at(type);

		log_warning("Can't determine cost of %s cell.\n", log_id(type));
		return 1;
	}

	int get(RTLIL::Cell *cell)
	{
		if (gate_cost && gate_cost->count(cell->type))
			return gate_cost->at(cell->type);

		if (design && design->module(cell->type) && cell->parameters.empty())
		{
			RTLIL::Module *mod = design->module(cell->type);

			if (mod->attributes.count(ID(cost)))
				return mod->attributes.at(ID(cost)).as_int();

			if (mod_cost_cache.count(mod->name))
				return mod_cost_cache.at(mod->name);

			int module_cost = 1;
			for (auto c : mod->cells())
				module_cost += get(c);

			mod_cost_cache[mod->name] = module_cost;
			return module_cost;
		}

		log_warning("Can't determine cost of %s cell (%d parameters).\n", log_id(cell->type), GetSize(cell->parameters));
		return 1;
	}
};

YOSYS_NAMESPACE_END

#endif
