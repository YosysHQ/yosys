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
#include "passes/hierarchy/util/verilog.h"
#include "passes/hierarchy/util/positionals.h"
#include "passes/hierarchy/util/ports.h"

PRIVATE_NAMESPACE_BEGIN
USING_YOSYS_NAMESPACE
// Find a matching wire for an implicit port connection; traversing generate block scope
RTLIL::Wire *find_implicit_port_wire(Module *module, Cell *cell, const std::string& port)
{
	const std::string &cellname = cell->name.str();
	size_t idx = cellname.size();
	while ((idx = cellname.find_last_of('.', idx-1)) != std::string::npos) {
		Wire *found = module->wire(cellname.substr(0, idx+1) + port.substr(1));
		if (found != nullptr)
			return found;
	}
	return module->wire(port);
}

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {

	void resolve_verilog(Design* design, bool nodefaults, bool keep_positionals, bool keep_portwidths, bool top_is_from_verific) {
		if (!keep_positionals)
			resolve_positionals(design);

		// Determine default values
		dict<IdString, dict<IdString, Const>> defaults_db;
		if (!nodefaults)
		{
			for (auto module : design->modules())
				for (auto wire : module->wires())
					if (wire->port_input && wire->attributes.count(ID::defaultvalue))
						defaults_db[module->name][wire->name] = wire->attributes.at(ID::defaultvalue);
		}

		// Process SV implicit wildcard port connections
		std::set<Module*> blackbox_derivatives;
		std::vector<Module*> design_modules = design->modules();

		for (auto module : design_modules)
			for (auto cell : module->cells())
				resolve_wildcards(cell, blackbox_derivatives, nodefaults, defaults_db);

		if (!nodefaults)
		{
			for (auto module : design->modules())
				for (auto cell : module->cells())
				{
					if (defaults_db.count(cell->type) == 0)
						continue;

					if (keep_positionals) {
						bool found_positionals = false;
						for (const auto& [port, sig] : cell->connections())
							if (port[0] == '$' && '0' <= port[1] && port[1] <= '9')
								found_positionals = true;
						if (found_positionals)
							continue;
					}

					for (auto &it : defaults_db.at(cell->type))
						if (!cell->hasPort(it.first))
							cell->setPort(it.first, it.second);
				}
		}

		for (auto module : design_modules)
			resolve_wand_wor(module);

		for (auto module : design_modules)
			check_and_adjust_ports(module, blackbox_derivatives, keep_portwidths, top_is_from_verific);

		for (auto module : blackbox_derivatives)
			design->remove(module);
	}
	void resolve_wildcards(Cell* cell, std::set<Module*>& blackbox_derivatives, bool nodefaults, dict<IdString, dict<IdString, Const>>& defaults_db) {
		if (!cell->get_bool_attribute(ID::wildcard_port_conns))
			return;
		Module* module = cell->module;
		Design* design = module->design;
		Module* submod = design->module(cell->type);

		if (submod == nullptr)
			log_error("Cell %s.%s (%s) has implicit port connections but the module it instantiates is unknown.\n",
					RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));

		// Need accurate port widths for error checking; so must derive blackboxes with dynamic port widths
		auto [derived_submod, boxed_params] = derive_blackbox_dynports(submod, cell, design, blackbox_derivatives);
		if (derived_submod == nullptr)
			return;
		submod = derived_submod;

		auto old_connections = cell->connections();
		for (auto wire : submod->wires()) {
			// Find ports of the module that aren't explicitly connected
			if (!wire->port_input && !wire->port_output)
				continue;
			if (old_connections.count(wire->name))
				continue;
			// Make sure a wire of correct name exists in the parent
			Wire* parent_wire = find_implicit_port_wire(module, cell, wire->name.str());

			// Missing wires are OK when a default value is set
			if (!nodefaults && parent_wire == nullptr && defaults_db.count(cell->type) && defaults_db.at(cell->type).count(wire->name))
				continue;

			if (parent_wire == nullptr)
				log_error("No matching wire for implicit port connection `%s' of cell %s.%s (%s).\n",
						RTLIL::id2cstr(wire->name), RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
			if (parent_wire->width != wire->width)
				log_error("Width mismatch between wire (%d bits) and port (%d bits) for implicit port connection `%s' of cell %s.%s (%s).\n",
						parent_wire->width, wire->width,
						RTLIL::id2cstr(wire->name), RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
			cell->setPort(wire->name, parent_wire);
		}
		cell->attributes.erase(ID::wildcard_port_conns);
	}

	void resolve_wand_wor(Module* module) {
		pool<Wire*> wand_wor_index;
		dict<Wire*, SigSpec> wand_map, wor_map;
		vector<SigSig> new_connections;

		for (auto wire : module->wires())
		{
			if (wire->get_bool_attribute(ID::wand)) {
				wand_map[wire] = SigSpec();
				wand_wor_index.insert(wire);
			}
			if (wire->get_bool_attribute(ID::wor)) {
				wor_map[wire] = SigSpec();
				wand_wor_index.insert(wire);
			}
		}

		for (auto &conn : module->connections())
		{
			SigSig new_conn;
			int cursor = 0;

			for (auto c : conn.first.chunks())
			{
				Wire *w = c.wire;
				SigSpec rhs = conn.second.extract(cursor, GetSize(c));

				if (wand_wor_index.count(w) == 0) {
					new_conn.first.append(c);
					new_conn.second.append(rhs);
				} else {
					if (wand_map.count(w)) {
						SigSpec sig = SigSpec(State::S1, GetSize(w));
						sig.replace(c.offset, rhs);
						wand_map.at(w).append(sig);
					} else {
						SigSpec sig = SigSpec(State::S0, GetSize(w));
						sig.replace(c.offset, rhs);
						wor_map.at(w).append(sig);
					}
				}
				cursor += GetSize(c);
			}
			new_connections.push_back(new_conn);
		}
		module->new_connections(new_connections);

		for (auto cell : module->cells())
		{
			if (!cell->known())
				continue;

			for (const auto& [port, sig] : cell->connections())
			{
				if (!cell->output(port))
					continue;

				SigSpec new_sig;
				bool update_port = false;

				for (auto c : sig.chunks())
				{
					Wire *w = c.wire;

					if (wand_wor_index.count(w) == 0) {
						new_sig.append(c);
						continue;
					}

					Wire *t = module->addWire(NEW_ID, GetSize(c));
					new_sig.append(t);
					update_port = true;

					if (wand_map.count(w)) {
						SigSpec mapped_sig = SigSpec(State::S1, GetSize(w));
						mapped_sig.replace(c.offset, t);
						wand_map.at(w).append(mapped_sig);
					} else {
						SigSpec mapped_sig = SigSpec(State::S0, GetSize(w));
						mapped_sig.replace(c.offset, t);
						wor_map.at(w).append(mapped_sig);
					}
				}

				if (update_port)
					cell->setPort(port, new_sig);
			}
		}

		for (auto w : wand_wor_index)
		{
			bool wand = wand_map.count(w);
			SigSpec sigs = wand ? wand_map.at(w) : wor_map.at(w);

			if (GetSize(sigs) == 0)
				continue;

			if (GetSize(w) == 1) {
				if (wand)
					module->addReduceAnd(NEW_ID, sigs, w);
				else
					module->addReduceOr(NEW_ID, sigs, w);
				continue;
			}

			SigSpec s = sigs.extract(0, GetSize(w));
			for (int i = GetSize(w); i < GetSize(sigs); i += GetSize(w)) {
				if (wand)
					s = module->And(NEW_ID, s, sigs.extract(i, GetSize(w)));
				else
					s = module->Or(NEW_ID, s, sigs.extract(i, GetSize(w)));
			}
			module->connect(w, s);
		}

	}
	void check_supported_formal(Design* design) {
		for (auto mod : design->modules()) {
			for (auto cell : mod->cells()) {
				if (!cell->type.in(ID($check), ID($assert), ID($assume), ID($live), ID($fair), ID($cover)))
					continue;
				if (!cell->has_attribute(ID(unsupported_sva)))
					continue;

				auto src = cell->get_src_attribute();

				if (!src.empty())
					src += ": ";

				log_error("%sProperty `%s' in module `%s' uses unsupported SVA constructs. See frontend warnings for details, run `chformal -remove a:unsupported_sva' to ignore.\n",
					src, log_id(cell->name), log_id(mod->name));
			}
		}
	}
};
YOSYS_NAMESPACE_END
