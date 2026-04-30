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
#include "passes/hierarchy/util/positionals.h"
#include "passes/hierarchy/util/misc.h"

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {

	void resolve_positionals(RTLIL::Design* design) {
		std::set<RTLIL::Module*> pos_mods;
		std::map<std::pair<RTLIL::Module*,int>, RTLIL::IdString> pos_map;
		std::vector<std::pair<RTLIL::Module*,RTLIL::Cell*>> pos_work;

		for (auto mod : design->modules())
		for (auto cell : mod->cells()) {
			RTLIL::Module *cell_mod = design->module(cell->type);
			if (cell_mod == nullptr)
				continue;
			for (auto &conn : cell->connections())
				if (conn.first[0] == '$' && '0' <= conn.first[1] && conn.first[1] <= '9') {
					pos_mods.insert(design->module(cell->type));
					pos_work.push_back(std::pair<RTLIL::Module*,RTLIL::Cell*>(mod, cell));
					break;
				}

			pool<std::pair<IdString, IdString>> params_rename;
			for (const auto &p : cell->parameters) {
				int id;
				if (read_id_num(p.first, &id)) {
					if (id <= 0 || id > GetSize(cell_mod->avail_parameters)) {
						log("  Failed to map positional parameter %d of cell %s.%s (%s).\n",
								id, RTLIL::id2cstr(mod->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
					} else {
						params_rename.insert(std::make_pair(p.first, cell_mod->avail_parameters[id - 1]));
					}
				}
			}
			for (const auto &p : params_rename) {
				cell->setParam(p.second, cell->getParam(p.first));
				cell->unsetParam(p.first);
			}
		}

		for (auto module : pos_mods)
		for (auto wire : module->wires()) {
			if (wire->port_id > 0)
				pos_map[std::pair<RTLIL::Module*,int>(module, wire->port_id)] = wire->name;
		}

		for (auto &work : pos_work) {
			RTLIL::Module *module = work.first;
			RTLIL::Cell *cell = work.second;
			log("Mapping positional arguments of cell %s.%s (%s).\n",
					RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
			dict<RTLIL::IdString, RTLIL::SigSpec> new_connections;
			for (auto &conn : cell->connections()) {
				int id;
				if (read_id_num(conn.first, &id)) {
					std::pair<RTLIL::Module*,int> key(design->module(cell->type), id);
					if (pos_map.count(key) == 0) {
						log("  Failed to map positional argument %d of cell %s.%s (%s).\n",
								id, RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
						new_connections[conn.first] = conn.second;
					} else
						new_connections[pos_map.at(key)] = conn.second;
				} else
					new_connections[conn.first] = conn.second;
			}
			cell->connections_ = new_connections;
		}
	}

};
YOSYS_NAMESPACE_END
