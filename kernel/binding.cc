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
 */

#include "binding.h"

YOSYS_NAMESPACE_BEGIN

RTLIL::Binding::Binding(RTLIL::IdString target_type,
                        RTLIL::IdString target_name)
	: target_type(target_type), target_name(target_name)
{
	// A counter of the number of bindings that have been created so far.
	static int binding_counter;
	attr_name = stringf("\\bound%d", binding_counter++);
}

// Return true if mod is either called name or is derived from an abstract
// module that was called name.
static bool
module_original_type_matches(const RTLIL::Module &mod, RTLIL::IdString name)
{
	if (mod.name == name) return true;

	// A module derived from 'foo' will have a name starting with $paramod
	// and an 'hdlname' attribute equal to '\foo'.
	if (!mod.name.begins_with("$paramod"))
		return false;

	RTLIL::IdString hdlname = mod.get_string_attribute(ID::hdlname);
	log_assert(!hdlname.empty());
	return (hdlname == name);
}

// Search through the design for modules called name, or that are derived from
// one called name.
static std::vector<RTLIL::Module *>
find_concrete_modules(RTLIL::Design &design, RTLIL::IdString name)
{
	std::vector<RTLIL::Module *> mods;

	for (const auto &pr : design.modules_) {
		if (module_original_type_matches(*pr.second, name))
			mods.push_back(pr.second);
	}

	return mods;
}

// Try to find a cell below mod whose (dot-separated) name is given by path.
// Modify so_far in place and return true on success.
static bool
find_cell_in(RTLIL::Binding::Path *so_far,
             RTLIL::Design &design, RTLIL::Module &mod, const char *path)
{
	const char *dot = strchr(path, '.');
	std::string cell_name =
		dot ? std::string(path, dot - path) : std::string(path);

	RTLIL::Cell *cell = mod.cell('\\' + cell_name);
	if (!cell)
		return false;

	so_far->push_back(RTLIL::Binding::Item(&mod, cell));
	if (!dot)
		return true;

	// We found a child cell, but there's more searching to do. Recurse to
	// search the cell's module.
	return find_cell_in(so_far, design, *cell->module, dot + 1);
}

RTLIL::Binding::Path
RTLIL::Binding::find_rel_cell(RTLIL::Design &design, RTLIL::Module &start) const
{
	Path ret;
	bool found = find_cell_in(&ret, design, start, target_name.c_str() + 1);
	if (!found)
		return Path();

	log_assert(ret.size());
	check_cell_type(design, *ret.back().second);
	return ret;
}

std::vector<RTLIL::Binding::Path>
RTLIL::Binding::find_tl_cells(RTLIL::Design &design) const
{
	std::vector<Path> paths;

	std::string tgt_name = target_name.str();
	size_t tgt_off = 0;

	// The target name should always start with a backslash
	log_assert(tgt_name[0] == '\\');

	// Is the name absolute (starts with $root)? If so, just skip past that:
	// we're at the top already.
	if (tgt_name.compare(0, 7, "\\$root.") == 0)
		tgt_off = 7;
	else
		tgt_off = 1;

	// This function can only find cells (as opposed to modules at the top
	// level). If there's no '.' after tgt_off, give up.
	size_t dot_off = tgt_name.find('.', tgt_off);
	if (dot_off == std::string::npos)
		return paths;

	// Otherwise, characters with indices {tgt_off .. dot_off - 1} should
	// name a module and then {dot_off + 1 .. } should name the cell
	// relative to the module.
	//
	// Note that we need to prefix the module name with a backslash (which
	// is separated from the actual module name if the name started with
	// $root) before interning the string.
	std::string mod_name = '\\' + tgt_name.substr(tgt_off, dot_off - tgt_off);
	const char *cell_path = tgt_name.c_str() + dot_off + 1;

	std::vector<RTLIL::Module *> mods = find_concrete_modules(design, mod_name);
	for (RTLIL::Module *mod : mods) {
		Path path;
		bool found = find_cell_in(&path, design, *mod, cell_path);
		if (found) {
			log_assert(path.size());
			check_cell_type(design, *path.back().second);
			paths.push_back(path);
		}
	}

	// If no concrete modules for mod_name have a cell at cell_path, then
	// paths will be an empty vector. If *some* have the cell (possible with
	// a generate if/else or similar), we should probably complain.
	if (paths.size() > 0 && paths.size() != mods.size()) {
		log_error("Some, but not all, specialized modules "
		          "with original name %s have a cell at path %s.",
		          mod_name.c_str(), cell_path);
	}

	return paths;
}

std::vector<RTLIL::Module *>
RTLIL::Binding::find_concrete_module_targets(RTLIL::Design &design) const
{
	// If target_type is nonempty, the bind statement had an instantiation
	// list. In which case, we definitely don't want to interpret this as a
	// module name.
	if(!target_type.empty())
		return std::vector<RTLIL::Module *>();

	return find_concrete_modules(design, target_name);
}

void
RTLIL::Binding::check_cell_type(RTLIL::Design &design,
                                const RTLIL::Cell &cell) const
{
	// If the user specified the module type, check it matches
	if (!target_type.empty()) {
		const RTLIL::Module *cell_mod = design.module(cell.type);
		log_assert(cell_mod);
		if (!module_original_type_matches(*cell_mod, target_type)) {
			log_error("The %s matches a cell, "
				  "but that cell has the wrong type (%s).",
				  describe().c_str(), cell_mod->name.c_str());
		}
	}
}

YOSYS_NAMESPACE_END
