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

#include "kernel/compatibility.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>

#include "passes/techmap/stdcells.inc"

// see simplemap.cc
extern void simplemap_get_mappers(std::map<std::string, void(*)(RTLIL::Module*, RTLIL::Cell*)> &mappers);

static void apply_prefix(std::string prefix, std::string &id)
{
	if (id[0] == '\\')
		id = prefix + "." + id.substr(1);
	else
		id = "$techmap" + prefix + "." + id;
}

static void apply_prefix(std::string prefix, RTLIL::SigSpec &sig, RTLIL::Module *module)
{
	for (size_t i = 0; i < sig.chunks.size(); i++) {
		if (sig.chunks[i].wire == NULL)
			continue;
		std::string wire_name = sig.chunks[i].wire->name;
		apply_prefix(prefix, wire_name);
		assert(module->wires.count(wire_name) > 0);
		sig.chunks[i].wire = module->wires[wire_name];
	}
}

struct TechmapWorker
{
	std::map<std::string, void(*)(RTLIL::Module*, RTLIL::Cell*)> simplemap_mappers;
	std::map<std::pair<RTLIL::IdString, std::map<RTLIL::IdString, RTLIL::Const>>, RTLIL::Module*> techmap_cache;
	std::map<RTLIL::Module*, bool> techmap_do_cache;

	struct TechmapWireData {
		RTLIL::Wire *wire;
		RTLIL::SigSpec value;
	};

	typedef std::map<std::string, std::vector<TechmapWireData>> TechmapWires;

	TechmapWires techmap_find_special_wires(RTLIL::Module *module)
	{
		TechmapWires result;

		if (module == NULL)
			return result;

		for (auto &it : module->wires) {
			const char *p = it.first.c_str();
			if (*p == '$')
				continue;

			const char *q = strrchr(p+1, '.');
			p = q ? q : p+1;

			if (!strncmp(p, "_TECHMAP_", 9)) {
				TechmapWireData record;
				record.wire = it.second;
				record.value = it.second;
				result[p].push_back(record);
				it.second->attributes["\\keep"] = RTLIL::Const(1);
				it.second->attributes["\\_techmap_special_"] = RTLIL::Const(1);
			}
		}

		if (!result.empty()) {
			SigMap sigmap(module);
			for (auto &it1 : result)
			for (auto &it2 : it1.second)
				sigmap.apply(it2.value);
		}

		return result;
	}

	void techmap_module_worker(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Cell *cell, RTLIL::Module *tpl, bool flatten_mode)
	{
		log("Mapping `%s.%s' using `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(tpl->name));

		if (tpl->memories.size() != 0)
			log_error("Technology map yielded memories -> this is not supported.\n");

		if (tpl->processes.size() != 0) {
			log("Technology map yielded processes:\n");
			for (auto &it : tpl->processes)
				log("  %s",RTLIL::id2cstr(it.first));
			log_error("Technology map yielded processes -> this is not supported.\n");
		}

		// erase from namespace first for _TECHMAP_REPLACE_ to work
		module->cells.erase(cell->name);
		std::string orig_cell_name;

		if (!flatten_mode)
			for (auto &it : tpl->cells)
				if (it.first == "\\_TECHMAP_REPLACE_") {
					orig_cell_name = cell->name;
					cell->name = stringf("$techmap%d", RTLIL::autoidx++) + cell->name;
					break;
				}

		std::map<RTLIL::IdString, RTLIL::IdString> positional_ports;

		for (auto &it : tpl->wires) {
			if (it.second->port_id > 0)
				positional_ports[stringf("$%d", it.second->port_id)] = it.first;
			RTLIL::Wire *w = new RTLIL::Wire(*it.second);
			apply_prefix(cell->name, w->name);
			w->port_input = false;
			w->port_output = false;
			w->port_id = 0;
			if (it.second->get_bool_attribute("\\_techmap_special_"))
				w->attributes.clear();
			module->add(w);
			design->select(module, w);
		}

		SigMap port_signal_map;

		for (auto &it : cell->connections) {
			RTLIL::IdString portname = it.first;
			if (positional_ports.count(portname) > 0)
				portname = positional_ports.at(portname);
			if (tpl->wires.count(portname) == 0 || tpl->wires.at(portname)->port_id == 0) {
				if (portname.substr(0, 1) == "$")
					log_error("Can't map port `%s' of cell `%s' to template `%s'!\n", portname.c_str(), cell->name.c_str(), tpl->name.c_str());
				continue;
			}
			RTLIL::Wire *w = tpl->wires.at(portname);
			RTLIL::SigSig c;
			if (w->port_output) {
				c.first = it.second;
				c.second = RTLIL::SigSpec(w);
				apply_prefix(cell->name, c.second, module);
			} else {
				c.first = RTLIL::SigSpec(w);
				c.second = it.second;
				apply_prefix(cell->name, c.first, module);
			}
			if (c.second.width > c.first.width)
				c.second.remove(c.first.width, c.second.width - c.first.width);
			if (c.second.width < c.first.width)
				c.second.append(RTLIL::SigSpec(RTLIL::State::S0, c.first.width - c.second.width));
			assert(c.first.width == c.second.width);
			if (flatten_mode) {
				// more conservative approach:
				// connect internal and external wires
				module->connections.push_back(c);
			} else {
				// approach that yields nicer outputs:
				// replace internal wires that are connected to external wires
				if (w->port_output)
					port_signal_map.add(c.second, c.first);
				else
					port_signal_map.add(c.first, c.second);
			}
		}

		for (auto &it : tpl->cells) {
			RTLIL::Cell *c = new RTLIL::Cell(*it.second);
			if (!flatten_mode && c->type.substr(0, 2) == "\\$")
				c->type = c->type.substr(1);
			if (!flatten_mode && c->name == "\\_TECHMAP_REPLACE_")
				c->name = orig_cell_name;
			else
				apply_prefix(cell->name, c->name);
			for (auto &it2 : c->connections) {
				apply_prefix(cell->name, it2.second, module);
				port_signal_map.apply(it2.second);
			}
			module->add(c);
			design->select(module, c);
		}

		for (auto &it : tpl->connections) {
			RTLIL::SigSig c = it;
			apply_prefix(cell->name, c.first, module);
			apply_prefix(cell->name, c.second, module);
			port_signal_map.apply(c.first);
			port_signal_map.apply(c.second);
			module->connections.push_back(c);
		}

		delete cell;
	}

	bool techmap_module(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Design *map, std::set<RTLIL::Cell*> &handled_cells,
			const std::map<RTLIL::IdString, std::set<RTLIL::IdString>> &celltypeMap, bool flatten_mode)
	{
		if (!design->selected(module))
			return false;

		bool log_continue = false;
		bool did_something = false;
		std::vector<std::string> cell_names;

		SigMap sigmap(module);
		for (auto &cell_it : module->cells)
			cell_names.push_back(cell_it.first);

		for (auto &cell_name : cell_names)
		{
			if (module->cells.count(cell_name) == 0)
				continue;

			RTLIL::Cell *cell = module->cells[cell_name];

			if (!design->selected(module, cell) || handled_cells.count(cell) > 0)
				continue;

			if (celltypeMap.count(cell->type) == 0)
				continue;

			for (auto &tpl_name : celltypeMap.at(cell->type))
			{
				std::string derived_name = tpl_name;
				RTLIL::Module *tpl = map->modules[tpl_name];
				std::map<RTLIL::IdString, RTLIL::Const> parameters = cell->parameters;

				if (!flatten_mode)
				{
					if (tpl->get_bool_attribute("\\techmap_simplemap")) {
						log("Mapping %s.%s (%s) with simplemap.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
						if (simplemap_mappers.count(cell->type) == 0)
							log_error("No simplemap mapper for cell type %s found!\n", RTLIL::id2cstr(cell->type));
						simplemap_mappers.at(cell->type)(module, cell);
						module->cells.erase(cell->name);
						delete cell;
						cell = NULL;
						did_something = true;
						break;
					}

					for (auto conn : cell->connections) {
						if (conn.first.substr(0, 1) == "$")
							continue;
						if (tpl->wires.count(conn.first) > 0 && tpl->wires.at(conn.first)->port_id > 0)
							continue;
						if (!conn.second.is_fully_const() || parameters.count(conn.first) > 0 || tpl->avail_parameters.count(conn.first) == 0)
							goto next_tpl;
						parameters[conn.first] = conn.second.as_const();
					}

					if (0) {
			next_tpl:
						continue;
					}

					if (tpl->avail_parameters.count("\\_TECHMAP_CELLTYPE_") != 0)
						parameters["\\_TECHMAP_CELLTYPE_"] = RTLIL::unescape_id(cell->type);

					for (auto conn : cell->connections) {
						if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONSTMSK_%s_", RTLIL::id2cstr(conn.first))) != 0) {
							std::vector<RTLIL::SigBit> v = sigmap(conn.second).to_sigbit_vector();
							for (auto &bit : v)
								bit = RTLIL::SigBit(bit.wire == NULL ? RTLIL::State::S1 : RTLIL::State::S0);
							parameters[stringf("\\_TECHMAP_CONSTMSK_%s_", RTLIL::id2cstr(conn.first))] = RTLIL::SigSpec(v).as_const();
						}
						if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONSTVAL_%s_", RTLIL::id2cstr(conn.first))) != 0) {
							std::vector<RTLIL::SigBit> v = sigmap(conn.second).to_sigbit_vector();
							for (auto &bit : v)
								if (bit.wire != NULL)
									bit = RTLIL::SigBit(RTLIL::State::Sx);
							parameters[stringf("\\_TECHMAP_CONSTVAL_%s_", RTLIL::id2cstr(conn.first))] = RTLIL::SigSpec(v).as_const();
						}
					}

					int unique_bit_id_counter = 0;
					std::map<RTLIL::SigBit, int> unique_bit_id;
					unique_bit_id[RTLIL::State::S0] = unique_bit_id_counter++;
					unique_bit_id[RTLIL::State::S1] = unique_bit_id_counter++;
					unique_bit_id[RTLIL::State::Sx] = unique_bit_id_counter++;
					unique_bit_id[RTLIL::State::Sz] = unique_bit_id_counter++;

					for (auto conn : cell->connections)
						if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONNMAP_%s_", RTLIL::id2cstr(conn.first))) != 0) {
							for (auto &bit : sigmap(conn.second).to_sigbit_vector())
								if (unique_bit_id.count(bit) == 0)
									unique_bit_id[bit] = unique_bit_id_counter++;
						}

					int bits = 0;
					for (int i = 0; i < 32; i++)
						if (((unique_bit_id_counter-1) & (1 << i)) != 0)
							bits = i;
					if (tpl->avail_parameters.count("\\_TECHMAP_BITS_CONNMAP_"))
						parameters["\\_TECHMAP_BITS_CONNMAP_"] = bits;

					for (auto conn : cell->connections)
						if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONNMAP_%s_", RTLIL::id2cstr(conn.first))) != 0) {
							RTLIL::Const value;
							for (auto &bit : sigmap(conn.second).to_sigbit_vector()) {
								RTLIL::Const chunk(unique_bit_id.at(bit), bits);
								value.bits.insert(value.bits.end(), chunk.bits.begin(), chunk.bits.end());
							}
							parameters[stringf("\\_TECHMAP_CONNMAP_%s_", RTLIL::id2cstr(conn.first))] = value;
						}
				}

				std::pair<RTLIL::IdString, std::map<RTLIL::IdString, RTLIL::Const>> key(tpl_name, parameters);
				if (techmap_cache.count(key) > 0) {
					tpl = techmap_cache[key];
				} else {
					if (cell->parameters.size() != 0) {
						derived_name = tpl->derive(map, parameters);
						tpl = map->modules[derived_name];
						log_continue = true;
					}
					techmap_cache[key] = tpl;
				}

				if (flatten_mode)
					techmap_do_cache[tpl] = true;

				if (techmap_do_cache.count(tpl) == 0)
				{
					bool keep_running = true;
					techmap_do_cache[tpl] = true;

					std::set<std::string> techmap_wire_names;

					while (keep_running)
					{
						TechmapWires twd = techmap_find_special_wires(tpl);
						keep_running = false;

						for (auto &it : twd)
							techmap_wire_names.insert(it.first);

						for (auto &it : twd["_TECHMAP_FAIL_"]) {
							RTLIL::SigSpec value = it.value;
							if (value.is_fully_const() && value.as_bool()) {
								log("Not using module `%s' from techmap as it contains a %s marker wire with non-zero value %s.\n",
										derived_name.c_str(), RTLIL::id2cstr(it.wire->name), log_signal(value));
								techmap_do_cache[tpl] = false;
							}
						}

						if (!techmap_do_cache[tpl])
							break;

						for (auto &it : twd)
						{
							if (it.first.substr(0, 12) != "_TECHMAP_DO_" || it.second.empty())
								continue;

							auto &data = it.second.front();

							if (!data.value.is_fully_const())
								log_error("Techmap yielded config wire %s with non-const value %s.\n", RTLIL::id2cstr(data.wire->name), log_signal(data.value));

							techmap_wire_names.erase(it.first);
							tpl->wires.erase(data.wire->name);

							const char *p = data.wire->name.c_str();
							const char *q = strrchr(p+1, '.');
							q = q ? q : p+1;

							assert(!strncmp(q, "_TECHMAP_DO_", 12));
							std::string new_name = data.wire->name.substr(0, q-p) + "_TECHMAP_DONE_" + data.wire->name.substr(q-p+12);
							while (tpl->wires.count(new_name))
								new_name += "_";
							data.wire->name = new_name;
							tpl->add(data.wire);

							std::string cmd_string = data.value.as_const().decode_string();

							RTLIL::Selection tpl_mod_sel(false);
							std::string backup_active_module = map->selected_active_module;
							map->selected_active_module = tpl->name;
							tpl_mod_sel.select(tpl);
							map->selection_stack.push_back(tpl_mod_sel);
							Pass::call(map, cmd_string);
							map->selection_stack.pop_back();
							map->selected_active_module = backup_active_module;

							keep_running = true;
							break;
						}
					}

					TechmapWires twd = techmap_find_special_wires(tpl);
					for (auto &it : twd) {
						if (it.first != "_TECHMAP_FAIL_" && it.first.substr(0, 12) != "_TECHMAP_DO_" && it.first.substr(0, 14) != "_TECHMAP_DONE_")
							log_error("Techmap yielded unknown config wire %s.\n", it.first.c_str());
						if (techmap_do_cache[tpl])
							for (auto &it2 : it.second)
								if (!it2.value.is_fully_const())
									log_error("Techmap yielded config wire %s with non-const value %s.\n", RTLIL::id2cstr(it2.wire->name), log_signal(it2.value));
						techmap_wire_names.erase(it.first);
					}

					for (auto &it : techmap_wire_names)
						log_error("Techmap special wire %s disappeared. This is considered a fatal error.\n", RTLIL::id2cstr(it));
				}

				if (techmap_do_cache.at(tpl) == false)
					continue;

				if (log_continue) {
					log_header("Continuing TECHMAP pass.\n");
					log_continue = false;
				}

				techmap_module_worker(design, module, cell, tpl, flatten_mode);
				did_something = true;
				cell = NULL;
				break;
			}

			handled_cells.insert(cell);
		}

		if (log_continue) {
			log_header("Continuing TECHMAP pass.\n");
			log_continue = false;
		}

		return did_something;
	}
};

struct TechmapPass : public Pass {
	TechmapPass() : Pass("techmap", "generic technology mapper") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    techmap [-map filename] [selection]\n");
		log("\n");
		log("This pass implements a very simple technology mapper that replaces cells in\n");
		log("the design with implementations given in form of a verilog or ilang source\n");
		log("file.\n");
		log("\n");
		log("    -map filename\n");
		log("        the library of cell implementations to be used.\n");
		log("        without this parameter a builtin library is used that\n");
		log("        transforms the internal RTL cells to the internal gate\n");
		log("        library.\n");
		log("\n");
		log("    -share_map filename\n");
		log("        like -map, but look for the file in the share directory (where the\n");
		log("        yosys data files are). this is mainly used internally when techmap\n");
		log("        is called from other commands.\n");
		log("\n");
		log("    -max_iter <number>\n");
		log("        only run the specified number of iterations.\n");
		log("\n");
		log("    -D <define>, -I <incdir>\n");
		log("        this options are passed as-is to the verilog frontend for loading the\n");
		log("        map file. Note that the verilog frontend is also called with the\n");
		log("        '-ignore_redef' option set.\n");
		log("\n");
		log("When a module in the map file has the 'techmap_celltype' attribute set, it will\n");
		log("match cells with a type that match the text value of this attribute. Otherwise\n");
		log("the module name will be used to match the cell.\n");
		log("\n");
		log("When a module in the map file has the 'techmap_simplemap' attribute set, techmap\n");
		log("will use 'simplemap' (see 'help simplemap') to map cells matching the module.\n");
		log("\n");
		log("All wires in the modules from the map file matching the pattern _TECHMAP_*\n");
		log("or *._TECHMAP_* are special wires that are used to pass instructions from\n");
		log("the mapping module to the techmap command. At the moment the following special\n");
		log("wires are supported:\n");
		log("\n");
		log("    _TECHMAP_FAIL_\n");
		log("        When this wire is set to a non-zero constant value, techmap will not\n");
		log("        use this module and instead try the next module with a matching\n");
		log("        'techmap_celltype' attribute.\n");
		log("\n");
		log("        When such a wire exists but does not have a constant value after all\n");
		log("        _TECHMAP_DO_* commands have been executed, an error is generated.\n");
		log("\n");
		log("    _TECHMAP_DO_*\n");
		log("        This wires are evaluated in alphabetical order. The constant text value\n");
		log("        of this wire is a yosys command (or sequence of commands) that is run\n");
		log("        by techmap on the module. A common use case is to run 'proc' on modules\n");
		log("        that are written using always-statements.\n");
		log("\n");
		log("        When such a wire has a non-constant value at the time it is to be\n");
		log("        evaluated, an error is produced. That means it is possible for such a\n");
		log("        wire to start out as non-constant and evaluate to a constant value\n");
		log("        during processing of other _TECHMAP_DO_* commands.\n");
		log("\n");
		log("In addition to this special wires, techmap also supports special parameters in\n");
		log("modules in the map file:\n");
		log("\n");
		log("    _TECHMAP_CELLTYPE_\n");
		log("        When a parameter with this name exists, it will be set to the type name\n");
		log("        of the cell that matches the module.\n");
		log("\n");
		log("    _TECHMAP_CONSTMSK_<port-name>_\n");
		log("    _TECHMAP_CONSTVAL_<port-name>_\n");
		log("        When this pair of parameters is available in a module for a port, then\n");
		log("        former has a 1-bit for each constant input bit and the latter has the\n");
		log("        value for this bit. The unused bits of the latter are set to undef (x).\n");
		log("\n");
		log("    _TECHMAP_BITS_CONNMAP_\n");
		log("    _TECHMAP_CONNMAP_<port-name>_\n");
		log("        For an N-bit port, the _TECHMAP_CONNMAP_<port-name>_ parameter, if it\n");
		log("        exists, will be set to an N*_TECHMAP_BITS_CONNMAP_ bit vector containing\n");
		log("        N words (of _TECHMAP_BITS_CONNMAP_ bits each) that assign each single\n");
		log("        bit driver a unique id. The values 0-3 are reserved for 0, 1, x, and z.\n");
		log("        This can be used to detect shorted inputs.\n");
		log("\n");
		log("When a module in the map file has a parameter where the according cell in the\n");
		log("design has a port, the module from the map file is only used if the port in\n");
		log("the design is connected to a constant value. The parameter is then set to the\n");
		log("constant value.\n");
		log("\n");
		log("A cell with the name _TECHMAP_REPLACE_ in the map file will inherit the name\n");
		log("of the cell that is beeing replaced.\n");
		log("\n");
		log("See 'help extract' for a pass that does the opposite thing.\n");
		log("\n");
		log("See 'help flatten' for a pass that does flatten the design (which is\n");
		log("esentially techmap but using the design itself as map library).\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing TECHMAP pass (map to technology primitives).\n");
		log_push();

		std::vector<std::string> map_files;
		std::string verilog_frontend = "verilog -ignore_redef";
		int max_iter = -1;

		size_t argidx;
		std::string proc_share_path = proc_share_dirname();
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				map_files.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-share_map" && argidx+1 < args.size()) {
				map_files.push_back(proc_share_path + args[++argidx]);
				continue;
			}
			if (args[argidx] == "-max_iter" && argidx+1 < args.size()) {
				max_iter = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-D" && argidx+1 < args.size()) {
				verilog_frontend += " -D " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-I" && argidx+1 < args.size()) {
				verilog_frontend += " -I " + args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		TechmapWorker worker;
		simplemap_get_mappers(worker.simplemap_mappers);

		RTLIL::Design *map = new RTLIL::Design;
		if (map_files.empty()) {
			FILE *f = fmemopen(stdcells_code, strlen(stdcells_code), "rt");
			Frontend::frontend_call(map, f, "<stdcells.v>", verilog_frontend);
			fclose(f);
		} else
			for (auto &fn : map_files) {
				FILE *f = fopen(fn.c_str(), "rt");
				if (f == NULL)
					log_cmd_error("Can't open map file `%s'\n", fn.c_str());
				Frontend::frontend_call(map, f, fn, (fn.size() > 3 && fn.substr(fn.size()-3) == ".il") ? "ilang" : verilog_frontend);
				fclose(f);
			}

		std::map<RTLIL::IdString, RTLIL::Module*> modules_new;
		for (auto &it : map->modules) {
			if (it.first.substr(0, 2) == "\\$")
				it.second->name = it.first.substr(1);
			modules_new[it.second->name] = it.second;
		}
		map->modules.swap(modules_new);

		std::map<RTLIL::IdString, std::set<RTLIL::IdString>> celltypeMap;
		for (auto &it : map->modules) {
			if (it.second->attributes.count("\\techmap_celltype") && !it.second->attributes.at("\\techmap_celltype").bits.empty()) {
				char *p = strdup(it.second->attributes.at("\\techmap_celltype").decode_string().c_str());
				for (char *q = strtok(p, " \t\r\n"); q; q = strtok(NULL, " \t\r\n"))
					celltypeMap[RTLIL::escape_id(q)].insert(it.first);
				free(p);
			} else
				celltypeMap[it.first].insert(it.first);
		}

		bool did_something = true;
		std::set<RTLIL::Cell*> handled_cells;
		while (did_something) {
			did_something = false;
			for (auto &mod_it : design->modules)
				if (worker.techmap_module(design, mod_it.second, map, handled_cells, celltypeMap, false))
					did_something = true;
			if (did_something)
				design->check();
			if (max_iter > 0 && --max_iter == 0)
				break;
		}

		log("No more expansions possible.\n");
		delete map;

		log_pop();
	}
} TechmapPass;
 
struct FlattenPass : public Pass {
	FlattenPass() : Pass("flatten", "flatten design") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    flatten [selection]\n");
		log("\n");
		log("This pass flattens the design by replacing cells by their implementation. This\n");
		log("pass is very simmilar to the 'techmap' pass. The only difference is that this\n");
		log("pass is using the current design as mapping library.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing FLATTEN pass (flatten design).\n");
		log_push();

		extra_args(args, 1, design);

		TechmapWorker worker;

		std::map<RTLIL::IdString, std::set<RTLIL::IdString>> celltypeMap;
		for (auto &it : design->modules)
			celltypeMap[it.first].insert(it.first);

		RTLIL::Module *top_mod = NULL;
		if (design->full_selection())
			for (auto &mod_it : design->modules)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_mod = mod_it.second;

		bool did_something = true;
		std::set<RTLIL::Cell*> handled_cells;
		while (did_something) {
			did_something = false;
			if (top_mod != NULL) {
				if (worker.techmap_module(design, top_mod, design, handled_cells, celltypeMap, true))
					did_something = true;
			} else {
				for (auto &mod_it : design->modules)
					if (worker.techmap_module(design, mod_it.second, design, handled_cells, celltypeMap, true))
						did_something = true;
			}
		}

		log("No more expansions possible.\n");

		if (top_mod != NULL) {
			std::map<RTLIL::IdString, RTLIL::Module*> new_modules;
			for (auto &mod_it : design->modules)
				if (mod_it.second == top_mod) {
					new_modules[mod_it.first] = mod_it.second;
				} else {
					log("Deleting now unused module %s.\n", RTLIL::id2cstr(mod_it.first));
					delete mod_it.second;
				}
			design->modules.swap(new_modules);
		}

		log_pop();
	}
} FlattenPass;

