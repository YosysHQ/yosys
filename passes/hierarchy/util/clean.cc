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

#include "kernel/yosys_common.h"
#include "passes/hierarchy/util/misc.h"
#include "passes/hierarchy/util/clean.h"

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {

void clean(RTLIL::Design *design, RTLIL::Module *top, bool purge_lib)
{
	std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> used;
	mark_used(design, used, top, 0);

	std::vector<RTLIL::Module*> del_modules;
	for (auto mod : design->modules())
		if (used.count(mod) == 0)
			del_modules.push_back(mod);
		else {
			// Now all interface ports must have been exploded, and it is hence
			// safe to delete all of the remaining dummy interface ports:
			pool<RTLIL::Wire*> del_wires;
			for(auto wire : mod->wires()) {
				if ((wire->port_input || wire->port_output) && wire->get_bool_attribute(ID::is_interface)) {
					del_wires.insert(wire);
				}
			}
			if (del_wires.size() > 0) {
				mod->remove(del_wires);
				mod->fixup_ports();
			}
		}

	int del_counter = 0;
	for (auto mod : del_modules) {
		if (!purge_lib && mod->get_blackbox_attribute())
			continue;
		log("Removing unused module `%s'.\n", mod->name);
		design->remove(mod);
		del_counter++;
	}

	log("Removed %d unused modules.\n", del_counter);
}

void mark_used(RTLIL::Design *design, std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> &used, RTLIL::Module *mod, int indent)
{
	if (used.count(mod) > 0)
		return;

	if (indent == 0)
		log("Top module:  %s\n", mod->name);
	else if (!mod->get_blackbox_attribute())
		log("Used module: %*s%s\n", indent, "", mod->name);
	used.insert(mod);

	for (auto cell : mod->cells()) {
		std::string celltype = cell->type.str();
		if (auto array_type = try_make_array(celltype))
			celltype = array_type->name;
		if (design->module(celltype))
			mark_used(design, used, design->module(celltype), indent+4);
	}
}

};
YOSYS_NAMESPACE_END