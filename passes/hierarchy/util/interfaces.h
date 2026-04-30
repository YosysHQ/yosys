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

#ifndef HIERARCHY_INTERFACES_H
#define HIERARCHY_INTERFACES_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {

void expand_all_interfaces(Design* design, Module* top_mod, bool flag_check, bool flag_simcheck, bool flag_smtcheck, const std::vector<std::string> &libdirs);
bool expand_module(RTLIL::Design *design, RTLIL::Module *module, bool flag_check, bool flag_simcheck, bool flag_smtcheck, const std::vector<std::string> &libdirs);

// For expanding a module's interface connections
struct IFExpander
{
	IFExpander (RTLIL::Design &design, RTLIL::Module &m);

	RTLIL::Module                          &module;
	dict<RTLIL::IdString, RTLIL::Module*>   interfaces_in_module;

	bool                                    has_interfaces_not_found;
	std::vector<RTLIL::IdString>            connections_to_remove;
	std::vector<RTLIL::IdString>            connections_to_add_name;
	std::vector<RTLIL::SigSpec>             connections_to_add_signal;
	dict<RTLIL::IdString, RTLIL::Module*>   interfaces_to_add_to_submodule;
	dict<RTLIL::IdString, RTLIL::IdString>  modports_used_in_submodule;

	// Reset the per-cell state
	void start_cell();

	// Set has_interfaces_not_found if there are pending interfaces that
	// haven't been found yet (and might be found in the future). Print a
	// warning if we've already gone over all the cells in the module.
	void on_missing_interface(RTLIL::IdString interface_name);

	// Handle an interface connection from the module
	void on_interface(RTLIL::Module        &submodule,
	                  RTLIL::IdString       conn_name,
	                  const RTLIL::SigSpec &conn_signals);

	// Handle a single connection from the module, making a note to expand
	// it if it's an interface connection.
	void on_connection(RTLIL::Module        &submodule,
	                   RTLIL::IdString       conn_name,
	                   const RTLIL::SigSpec &conn_signals);

	// Iterate over the connections in a cell, tracking any interface
	// connections
	void visit_connections(const RTLIL::Cell &cell,
			       RTLIL::Module     &submodule);

	// Add/remove connections to the cell as necessary, replacing any SV
	// interface port connection with the individual signal connections.
	void rewrite_interface_connections(RTLIL::Cell &cell) const;
};

};
YOSYS_NAMESPACE_END

#endif /* HIERARCHY_INTERFACES_H */
