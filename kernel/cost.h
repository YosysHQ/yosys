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

#include <kernel/yosys.h>

YOSYS_NAMESPACE_BEGIN

int get_cell_cost(RTLIL::Cell *cell, dict<RTLIL::IdString, int> *mod_cost_cache = nullptr);

int get_cell_cost(RTLIL::IdString type, const dict<RTLIL::IdString, RTLIL::Const> &parameters = dict<RTLIL::IdString, RTLIL::Const>(),
		RTLIL::Design *design = nullptr, dict<RTLIL::IdString, int> *mod_cost_cache = nullptr)
{
	static dict<RTLIL::IdString, int> gate_cost = {
		{ "$_BUF_",   1 },
		{ "$_NOT_",   2 },
		{ "$_AND_",   4 },
		{ "$_NAND_",  4 },
		{ "$_OR_",    4 },
		{ "$_NOR_",   4 },
		{ "$_XOR_",   8 },
		{ "$_XNOR_",  8 },
		{ "$_AOI3_",  6 },
		{ "$_OAI3_",  6 },
		{ "$_AOI4_",  8 },
		{ "$_OAI4_",  8 },
		{ "$_MUX_",   4 }
	};

	if (gate_cost.count(type))
		return gate_cost.at(type);

	if (parameters.empty() && design && design->module(type))
	{
		RTLIL::Module *mod = design->module(type);

		if (mod->attributes.count("\\cost"))
			return mod->attributes.at("\\cost").as_int();

		dict<RTLIL::IdString, int> local_mod_cost_cache;
		if (mod_cost_cache == nullptr)
			mod_cost_cache = &local_mod_cost_cache;

		if (mod_cost_cache->count(mod->name))
			return mod_cost_cache->at(mod->name);

		int module_cost = 1;
		for (auto c : mod->cells())
			module_cost += get_cell_cost(c, mod_cost_cache);

		(*mod_cost_cache)[mod->name] = module_cost;
		return module_cost;
	}

	log_warning("Can't determine cost of %s cell (%d parameters).\n", log_id(type), GetSize(parameters));
	return 1;
}

int get_cell_cost(RTLIL::Cell *cell, dict<RTLIL::IdString, int> *mod_cost_cache)
{
	return get_cell_cost(cell->type, cell->parameters, cell->module->design, mod_cost_cache);
}

YOSYS_NAMESPACE_END

#endif
