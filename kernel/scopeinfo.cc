/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#include "kernel/scopeinfo.h"

YOSYS_NAMESPACE_BEGIN

template <typename I, typename Filter> void ModuleHdlnameIndex::index_items(I begin, I end, Filter filter)
{
	for (; begin != end; ++begin) {
		auto const &item = *begin;

		if (!filter(item))
			continue;
		std::vector<IdString> path = parse_hdlname(item);
		if (!path.empty())
			lookup.emplace(item, tree.insert(path, item));
	}
}

void ModuleHdlnameIndex::index()
{
	index_wires();
	index_cells();
}

void ModuleHdlnameIndex::index_wires()
{
	auto wires = module->wires();
	index_items(wires.begin(), wires.end(), [](Wire *) { return true; });
}

void ModuleHdlnameIndex::index_cells()
{
	auto cells = module->cells();
	index_items(cells.begin(), cells.end(), [](Cell *) { return true; });
}

void ModuleHdlnameIndex::index_scopeinfo_cells()
{
	auto cells = module->cells();
	index_items(cells.begin(), cells.end(), [](Cell *cell) { return cell->type == ID($scopeinfo); });
}

std::vector<std::string> ModuleHdlnameIndex::scope_sources(Cursor cursor)
{
	std::vector<std::string> result;

	for (; !cursor.is_root(); cursor = cursor.parent()) {
		if (!cursor.has_entry()) {
			result.push_back("");
			result.push_back("");
			continue;
		}
		Cell *cell = cursor.entry().cell();
		if (cell == nullptr || cell->type != ID($scopeinfo)) {
			result.push_back("");
			result.push_back("");
			continue;
		}
		result.push_back(scopeinfo_get_attribute(cell, ScopeinfoAttrs::Module, ID::src).decode_string());
		result.push_back(scopeinfo_get_attribute(cell, ScopeinfoAttrs::Cell, ID::src).decode_string());
	}

	result.push_back(module->get_src_attribute());

	std::reverse(result.begin(), result.end());

	return result;
}

static const char *attr_prefix(ScopeinfoAttrs attrs)
{
	switch (attrs) {
	case ScopeinfoAttrs::Cell:
		return "\\cell_";
	case ScopeinfoAttrs::Module:
		return "\\module_";
	default:
		log_abort();
	}
}

bool scopeinfo_has_attribute(const RTLIL::Cell *scopeinfo, ScopeinfoAttrs attrs, const RTLIL::IdString &id)
{
	log_assert(scopeinfo->type == ID($scopeinfo));
	return scopeinfo->has_attribute(attr_prefix(attrs) + RTLIL::unescape_id(id));
}

RTLIL::Const scopeinfo_get_attribute(const RTLIL::Cell *scopeinfo, ScopeinfoAttrs attrs, const RTLIL::IdString &id)
{
	log_assert(scopeinfo->type == ID($scopeinfo));
	auto found = scopeinfo->attributes.find(attr_prefix(attrs) + RTLIL::unescape_id(id));
	if (found == scopeinfo->attributes.end())
		return RTLIL::Const();
	return found->second;
}

dict<RTLIL::IdString, RTLIL::Const> scopeinfo_attributes(const RTLIL::Cell *scopeinfo, ScopeinfoAttrs attrs)
{
	dict<RTLIL::IdString, RTLIL::Const> attributes;

	const char *prefix = attr_prefix(attrs);
	int prefix_len = strlen(prefix);

	for (auto const &entry : scopeinfo->attributes)
		if (entry.first.begins_with(prefix))
			attributes.emplace(RTLIL::escape_id(entry.first.c_str() + prefix_len), entry.second);

	return attributes;
}

YOSYS_NAMESPACE_END
