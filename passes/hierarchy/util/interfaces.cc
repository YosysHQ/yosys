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
#include "passes/hierarchy/util/interfaces.h"
#include "passes/hierarchy/util/clean.h"

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {

RTLIL::Module *check_if_top_has_changed(Design *design, Module *top_mod)
{
	if(top_mod != NULL && top_mod->get_bool_attribute(ID::initial_top))
		return top_mod;
	else {
		for (auto mod : design->modules()) {
			if (mod->get_bool_attribute(ID::top)) {
				return mod;
			}
		}
	}
	return NULL;
}

// Check that the connections on the cell match those that are defined
// on the type: each named connection should match the name of a port
// and each positional connection should have an index smaller than
// the number of ports.
//
// Also do the same checks on the specified parameters.
static void check_cell_connections(const RTLIL::Module &module, RTLIL::Cell &cell, RTLIL::Module &mod)
{
	int id;
	for (auto &conn : cell.connections()) {
		if (read_id_num(conn.first, &id)) {
			if (id <= 0 || id > GetSize(mod.ports))
				log_error("Module `%s' referenced in module `%s' in cell `%s' "
						  "has only %d ports, requested port %d.\n",
						  log_id(cell.type), log_id(&module), log_id(&cell),
						  GetSize(mod.ports), id);
			continue;
		}

		const RTLIL::Wire* wire = mod.wire(conn.first);
		if (!wire || wire->port_id == 0) {
			log_error("Module `%s' referenced in module `%s' in cell `%s' "
					  "does not have a port named '%s'.\n",
					  log_id(cell.type), log_id(&module), log_id(&cell),
					  log_id(conn.first));
		}
	}
	for (auto &param : cell.parameters) {
		if (read_id_num(param.first, &id)) {
			if (id <= 0 || id > GetSize(mod.avail_parameters))
				log_error("Module `%s' referenced in module `%s' in cell `%s' "
						  "has only %d parameters, requested parameter %d.\n",
						  log_id(cell.type), log_id(&module), log_id(&cell),
						  GetSize(mod.avail_parameters), id);
			continue;
		}

		if (mod.avail_parameters.count(param.first) == 0 &&
			param.first[0] != '$' &&
			strchr(param.first.c_str(), '.') == NULL) {
			log_error("Module `%s' referenced in module `%s' in cell `%s' "
					  "does not have a parameter named '%s'.\n",
					  log_id(cell.type), log_id(&module), log_id(&cell),
					  log_id(param.first));
		}
	}
}


// Get a module needed by a cell, either by deriving an abstract module or by
// loading one from a directory in libdirs.
//
// If the module can't be found and check is true then exit with an error
// message. Otherwise, return a pointer to the module if we derived or loaded
// something. or null otherwise (the module should be blackbox or we couldn't
// find it and check is not set).
RTLIL::Module *get_module(RTLIL::Design				  &design,
						  RTLIL::Cell					&cell,
						  RTLIL::Module				  &parent,
						  bool							check,
						  const std::vector<std::string> &libdirs)
{
	std::string cell_type = cell.type.str();
	RTLIL::Module *abs_mod = design.module("$abstract" + cell_type);
	if (abs_mod) {
		cell.type = abs_mod->derive(&design, cell.parameters);
		cell.parameters.clear();
		RTLIL::Module *mod = design.module(cell.type);
		log_assert(mod);
		return mod;
	}

	// If the cell type starts with '$' and isn't '$abstract', we should
	// treat it as a black box and skip.
	if (cell_type[0] == '$')
		return nullptr;

	for (auto &dir : libdirs) {
		static const vector<pair<string, string>> extensions_list =
			{
			 {".v", "verilog"},
			 {".sv", "verilog -sv"},
			 {".il", "rtlil"}
			};

		for (auto &ext : extensions_list) {
			std::string filename = dir + "/" + RTLIL::unescape_id(cell.type) + ext.first;
			if (!check_file_exists(filename))
				continue;

			Frontend::frontend_call(&design, NULL, filename, ext.second);
			RTLIL::Module *mod = design.module(cell.type);
			if (!mod)
				log_error("File `%s' from libdir does not declare module `%s'.\n",
						  filename.c_str(), cell_type.c_str());
			return mod;
		}
	}

	// We couldn't find the module anywhere. Complain if check is set.
	if (check)
		log_error("Module `%s' referenced in module `%s' in cell `%s' is not part of the design.\n",
				  cell_type.c_str(), parent.name.c_str(), cell.name.c_str());

	return nullptr;
}


void expand_all_interfaces(Design* design, Module* top_mod, bool flag_check, bool flag_simcheck, bool flag_smtcheck, const std::vector<std::string> &libdirs) {
	bool did_something = true;
	while (did_something)
	{
		did_something = false;

		std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> used_modules;
		if (top_mod != NULL) {
			log_header(design, "Analyzing design hierarchy..\n");
			mark_used(design, used_modules, top_mod, 0);
		} else {
			for (auto mod : design->modules())
				used_modules.insert(mod);
		}

		for (auto module : used_modules) {
			if (expand_module(design, module, flag_check, flag_simcheck, flag_smtcheck, libdirs))
				did_something = true;
		}


		// The top module might have changed if interface instances have been detected in it:
		RTLIL::Module *tmp_top_mod = check_if_top_has_changed(design, top_mod);
		if (tmp_top_mod != NULL) {
			if (tmp_top_mod != top_mod){
				top_mod = tmp_top_mod;
				top_mod->attributes[ID::initial_top] = RTLIL::Const(1);
				did_something = true;
			}
		}

		// Delete modules marked as 'to_delete':
		std::vector<RTLIL::Module *> modules_to_delete;
		for(auto mod : design->modules()) {
			if (mod->get_bool_attribute(ID::to_delete)) {
				modules_to_delete.push_back(mod);
			}
		}
		for(size_t i=0; i<modules_to_delete.size(); i++) {
			design->remove(modules_to_delete[i]);
		}
	}
}

bool expand_module(RTLIL::Design *design, RTLIL::Module *module, bool flag_check, bool flag_simcheck, bool flag_smtcheck, const std::vector<std::string> &libdirs)
{
	bool did_something = false;
	std::map<RTLIL::Cell*, std::pair<int, int>> array_cells;
	std::string filename;

	bool has_interface_ports = false;

	// If any of the ports are actually interface ports, we will always need to
	// reprocess the module:
	if(!module->get_bool_attribute(ID::interfaces_replaced_in_module)) {
		for (auto wire : module->wires()) {
			if ((wire->port_input || wire->port_output) && wire->get_bool_attribute(ID::is_interface))
				has_interface_ports = true;
		}
	}

	IFExpander if_expander(*design, *module);

	for (auto cell : module->cells())
	{
		if_expander.start_cell();

		if (auto a = try_make_array(cell->type.str())) {
			int idx = atoi(cell->type.substr(a->pos_idx + 1, a->pos_num).c_str());
			int num = atoi(cell->type.substr(a->pos_num + 1, a->pos_type).c_str());
			array_cells[cell] = std::pair<int, int>(idx, num);
			cell->type = cell->type.substr(a->pos_type + 1);
		}

		RTLIL::Module *mod = design->module(cell->type);
		if (!mod)
		{
			mod = get_module(*design, *cell, *module, flag_check || flag_simcheck || flag_smtcheck, libdirs);

			// If we still don't have a module, treat the cell as a black box and skip
			// it. Otherwise, we either loaded or derived something so should set the
			// did_something flag before returning (to ensure we come back and expand
			// the thing we just loaded).
			if (mod)
				did_something = true;

			continue;
		}

		log_assert(mod);

		// Go over all connections and check if any of them are SV
		// interfaces.
		if_expander.visit_connections(*cell, *mod);

		if (flag_check || flag_simcheck || flag_smtcheck)
			check_cell_connections(*module, *cell, *mod);

		if (mod->get_blackbox_attribute()) {
			if (flag_simcheck || (flag_smtcheck && !mod->get_bool_attribute(ID::smtlib2_module)))
				log_error("Module `%s' referenced in module `%s' in cell `%s' is a blackbox/whitebox module.\n",
						cell->type.c_str(), module->name.c_str(), cell->name.c_str());
			continue;
		}

		// If interface instances not yet found, skip cell for now, and say we did something, so that we will return back here:
		if(if_expander.has_interfaces_not_found) {
			did_something = true; // waiting for interfaces to be handled
			continue;
		}

		if_expander.rewrite_interface_connections(*cell);

		// If there are no overridden parameters AND not interfaces, then we can use the existing module instance as the type
		// for the cell:
		if (cell->parameters.size() == 0 &&
			(if_expander.interfaces_to_add_to_submodule.size() == 0 ||
			 !(cell->get_bool_attribute(ID::module_not_derived)))) {
			// If the cell being processed is an the interface instance itself, go down to "handle_interface_instance:",
			// so that the signals of the interface are added to the parent module.
			if (mod->get_bool_attribute(ID::is_interface)) {
				goto handle_interface_instance;
			}
			continue;
		}

		cell->type = mod->derive(design,
					 cell->parameters,
					 if_expander.interfaces_to_add_to_submodule,
					 if_expander.modports_used_in_submodule);
		cell->parameters.clear();
		did_something = true;

		handle_interface_instance:

			// We add all the signals of the interface explicitly to the parent module. This is always needed when we encounter
			// an interface instance:
			if (mod->get_bool_attribute(ID::is_interface) && cell->get_bool_attribute(ID::module_not_derived)) {
				cell->set_bool_attribute(ID::is_interface);
				RTLIL::Module *derived_module = design->module(cell->type);
				if_expander.interfaces_in_module[cell->name] = derived_module;
				did_something = true;
			}
		// We clear 'module_not_derived' such that we will not rederive the cell again (needed when there are interfaces connected to the cell)
		cell->attributes.erase(ID::module_not_derived);
	}
	// Clear the attribute 'cells_not_processed' such that it can be known that we
	// have been through all cells at least once, and that we can know whether
	// to flag an error because of interface instances not found:
	module->attributes.erase(ID::cells_not_processed);


	// If any interface instances or interface ports were found in the module, we need to rederive it completely:
	if ((if_expander.interfaces_in_module.size() > 0 || has_interface_ports) && !module->get_bool_attribute(ID::interfaces_replaced_in_module)) {
		module->expand_interfaces(design, if_expander.interfaces_in_module);
		return did_something;
	}

	// Now that modules have been derived, we may want to reprocess this
	// module given the additional available context.
	if (module->reprocess_if_necessary(design))
		return true;

	for (auto &it : array_cells)
	{
		RTLIL::Cell *cell = it.first;
		int idx = it.second.first, num = it.second.second;

		if (design->module(cell->type) == nullptr)
			log_error("Array cell `%s.%s' of unknown type `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));

		RTLIL::Module *mod = design->module(cell->type);

		for (auto &conn : cell->connections_) {
			int conn_size = conn.second.size();
			RTLIL::IdString portname = conn.first;
			if (portname.begins_with("$")) {
				int port_id = atoi(portname.substr(1).c_str());
				for (auto wire : mod->wires())
					if (wire->port_id == port_id) {
						portname = wire->name;
						break;
					}
			}
			if (mod->wire(portname) == nullptr)
				log_error("Array cell `%s.%s' connects to unknown port `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(conn.first));
			int port_size = mod->wire(portname)->width;
			if (conn_size == port_size || conn_size == 0)
				continue;
			if (conn_size != port_size*num)
				log_error("Array cell `%s.%s' has invalid port vs. signal size for port `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(conn.first));
			conn.second = conn.second.extract(port_size*idx, port_size);
		}
	}

	return did_something;
}

IFExpander::IFExpander (RTLIL::Design &design, RTLIL::Module &m)
	: module(m), has_interfaces_not_found(false)
{
	// Keep track of all derived interfaces available in the current
	// module in 'interfaces_in_module':
	for (auto cell : module.cells()) {
		if(!cell->get_bool_attribute(ID::is_interface))
			continue;

		interfaces_in_module[cell->name] = design.module(cell->type);
	}
}

// Reset the per-cell state
void IFExpander::start_cell()
{
	has_interfaces_not_found = false;
	connections_to_remove.clear();
	connections_to_add_name.clear();
	connections_to_add_signal.clear();
	interfaces_to_add_to_submodule.clear();
	modports_used_in_submodule.clear();
}

// Set has_interfaces_not_found if there are pending interfaces that
// haven't been found yet (and might be found in the future). Print a
// warning if we've already gone over all the cells in the module.
void IFExpander::on_missing_interface(RTLIL::IdString interface_name)
{
	// If there are cells that haven't yet been processed, maybe
	// we'll find this interface in the future.
	if (module.get_bool_attribute(ID::cells_not_processed)) {
		has_interfaces_not_found = true;
		return;
	}

	// Otherwise, we have already gone over all cells in this
	// module and the interface has still not been found. Warn
	// about it and don't set has_interfaces_not_found (to avoid a
	// loop).
	log_warning("Could not find interface instance for `%s' in `%s'\n",
			log_id(interface_name), log_id(&module));
}

// Handle an interface connection from the module
void IFExpander::on_interface(RTLIL::Module		&submodule,
					RTLIL::IdString	   conn_name,
					const RTLIL::SigSpec &conn_signals)
{
	// Check if the connected wire is a potential interface in the parent module
	std::string interface_name_str = conn_signals[0].wire->name.str();
	// Strip the prefix '$dummywireforinterface' from the dummy wire to get the name
	interface_name_str.replace(0,23,"");
	interface_name_str = "\\" + interface_name_str;
	RTLIL::IdString interface_name = interface_name_str;

	// If 'interfaces' in the cell have not be been handled yet, we aren't
	// ready to derive the sub-module either
	if (!module.get_bool_attribute(ID::interfaces_replaced_in_module)) {
		on_missing_interface(interface_name);
		return;
	}

	// Check if the interface instance is present in module. Interface
	// instances may either have the plain name or the name appended with
	// '_inst_from_top_dummy'. Check for both of them here
	int nexactmatch = interfaces_in_module.count(interface_name) > 0;
	std::string interface_name_str2 =  interface_name_str + "_inst_from_top_dummy";
	RTLIL::IdString interface_name2 = interface_name_str2;
	int nmatch2 = interfaces_in_module.count(interface_name2) > 0;

	// If we can't find either name, this is a missing interface.
	if (! (nexactmatch || nmatch2)) {
		on_missing_interface(interface_name);
		return;
	}

	if (nexactmatch != 0) // Choose the one with the plain name if it exists
		interface_name2 = interface_name;

	RTLIL::Module *mod_replace_ports = interfaces_in_module.at(interface_name2);

	// Go over all wires in interface, and add replacements to lists.
	for (auto mod_wire : mod_replace_ports->wires()) {
		std::string signal_name1 = conn_name.str() + "." + log_id(mod_wire->name);
		std::string signal_name2 = interface_name.str() + "." + log_id(mod_wire);
		connections_to_add_name.push_back(RTLIL::IdString(signal_name1));
		if(module.wire(signal_name2) == nullptr) {
			log_error("Could not find signal '%s' in '%s'\n",
					signal_name2.c_str(), log_id(module.name));
		}
		else {
			RTLIL::Wire *wire_in_parent = module.wire(signal_name2);
			connections_to_add_signal.push_back(wire_in_parent);
		}
	}
	connections_to_remove.push_back(conn_name);
	interfaces_to_add_to_submodule[conn_name] = interfaces_in_module.at(interface_name2);

	// Find if the sub-module has set a modport for the current interface
	// connection. Add any modports to a dict which will be passed to
	// AstModule::derive
	string modport_name = submodule.wire(conn_name)->get_string_attribute(ID::interface_modport);
	if (!modport_name.empty()) {
		modports_used_in_submodule[conn_name] = "\\" + modport_name;
	}
}

// Handle a single connection from the module, making a note to expand
// it if it's an interface connection.
void IFExpander::on_connection(RTLIL::Module		&submodule,
					RTLIL::IdString	   conn_name,
					const RTLIL::SigSpec &conn_signals)
{
	// Does the connection look like an interface
	if (
		conn_signals.size() != 1 ||
		conn_signals[0].wire == nullptr ||
		conn_signals[0].wire->get_bool_attribute(ID::is_interface) == false ||
		conn_signals[0].wire->name.str().find("$dummywireforinterface") != 0
	)
		return;

	// Check if the connection is present as an interface in the sub-module's port list
	int id;
	if (read_id_num(conn_name, &id)) {
		/* Interface expansion is incompatible with positional arguments
			* during expansion, the port list gets each interface signal
			* inserted after the interface itself which means that the argument
			* positions in the parent module no longer match.
			*
			* Supporting this would require expanding the interfaces in the
			* parent module, renumbering the arguments to match, and then
			* iterating over the ports list to find the matching interface
			* (refactoring on_interface to accept different conn_names on the
			* parent and child).
			*/
		log_error("Unable to connect `%s' to submodule `%s' with positional interface argument `%s'!\n",
			module.name,
			submodule.name,
			conn_signals[0].wire->name.str().substr(23)
		);
	} else {
		// Lookup connection by name
		const RTLIL::Wire *wire = submodule.wire(conn_name);
		if (!wire || !wire->get_bool_attribute(ID::is_interface))
			return;
		}
	// If the connection looks like an interface, handle it.
	on_interface(submodule, conn_name, conn_signals);
}

// Iterate over the connections in a cell, tracking any interface
// connections
void IFExpander::visit_connections(const RTLIL::Cell &cell,
				RTLIL::Module	 &submodule)
{
	for (const auto &conn : cell.connections()) {
		on_connection(submodule, conn.first, conn.second);
	}
}

// Add/remove connections to the cell as necessary, replacing any SV
// interface port connection with the individual signal connections.
void IFExpander::rewrite_interface_connections(RTLIL::Cell &cell) const
{
	for(unsigned int i=0;i<connections_to_add_name.size();i++) {
		cell.connections_[connections_to_add_name[i]] = connections_to_add_signal[i];
	}
	// Remove the connection for the interface itself:
	for(unsigned int i=0;i<connections_to_remove.size();i++) {
		cell.connections_.erase(connections_to_remove[i]);
	}
}

};
YOSYS_NAMESPACE_END
