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

#include "kernel/yosys.h"
#include "kernel/utils.h"
#include "kernel/sigtools.h"
#include "libs/sha1/sha1.h"

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "simplemap.h"
#include "passes/techmap/techmap.inc"

YOSYS_NAMESPACE_BEGIN

// see maccmap.cc
extern void maccmap(RTLIL::Module *module, RTLIL::Cell *cell, bool unmap = false);

YOSYS_NAMESPACE_END

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void apply_prefix(std::string prefix, std::string &id)
{
	if (id[0] == '\\')
		id = prefix + "." + id.substr(1);
	else
		id = "$techmap" + prefix + "." + id;
}

void apply_prefix(std::string prefix, RTLIL::SigSpec &sig, RTLIL::Module *module)
{
	vector<SigChunk> chunks = sig;
	for (auto &chunk : chunks)
		if (chunk.wire != NULL) {
			std::string wire_name = chunk.wire->name.str();
			apply_prefix(prefix, wire_name);
			log_assert(module->wires_.count(wire_name) > 0);
			chunk.wire = module->wires_[wire_name];
		}
	sig = chunks;
}

struct TechmapWorker
{
	std::map<RTLIL::IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> simplemap_mappers;
	std::map<std::pair<RTLIL::IdString, std::map<RTLIL::IdString, RTLIL::Const>>, RTLIL::Module*> techmap_cache;
	std::map<RTLIL::Module*, bool> techmap_do_cache;
	std::set<RTLIL::Module*, RTLIL::IdString::compare_ptr_by_name<RTLIL::Module>> module_queue;
	dict<Module*, SigMap> sigmaps;

	pool<IdString> flatten_do_list;
	pool<IdString> flatten_done_list;
	pool<Cell*> flatten_keep_list;

	struct TechmapWireData {
		RTLIL::Wire *wire;
		RTLIL::SigSpec value;
	};

	typedef std::map<std::string, std::vector<TechmapWireData>> TechmapWires;

	bool extern_mode;
	bool assert_mode;
	bool flatten_mode;
	bool recursive_mode;
	bool autoproc_mode;

	TechmapWorker()
	{
		extern_mode = false;
		assert_mode = false;
		flatten_mode = false;
		recursive_mode = false;
		autoproc_mode = false;
	}

	std::string constmap_tpl_name(SigMap &sigmap, RTLIL::Module *tpl, RTLIL::Cell *cell, bool verbose)
	{
		std::string constmap_info;
		std::map<RTLIL::SigBit, std::pair<RTLIL::IdString, int>> connbits_map;

		for (auto conn : cell->connections())
			for (int i = 0; i < GetSize(conn.second); i++) {
				RTLIL::SigBit bit = sigmap(conn.second[i]);
				if (bit.wire == nullptr) {
					if (verbose)
						log("  Constant input on bit %d of port %s: %s\n", i, log_id(conn.first), log_signal(bit));
					constmap_info += stringf("|%s %d %d", log_id(conn.first), i, bit.data);
				} else if (connbits_map.count(bit)) {
					if (verbose)
						log("  Bit %d of port %s and bit %d of port %s are connected.\n", i, log_id(conn.first),
								connbits_map.at(bit).second, log_id(connbits_map.at(bit).first));
					constmap_info += stringf("|%s %d %s %d", log_id(conn.first), i,
							log_id(connbits_map.at(bit).first), connbits_map.at(bit).second);
				} else {
					connbits_map[bit] = std::pair<RTLIL::IdString, int>(conn.first, i);
					constmap_info += stringf("|%s %d", log_id(conn.first), i);
				}
			}

		return stringf("$paramod$constmap:%s%s", sha1(constmap_info).c_str(), tpl->name.c_str());
	}

	TechmapWires techmap_find_special_wires(RTLIL::Module *module)
	{
		TechmapWires result;

		if (module == NULL)
			return result;

		for (auto &it : module->wires_) {
			const char *p = it.first.c_str();
			if (*p == '$')
				continue;

			const char *q = strrchr(p+1, '.');
			p = q ? q+1 : p+1;

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

	void techmap_module_worker(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Cell *cell, RTLIL::Module *tpl)
	{
		if (tpl->processes.size() != 0) {
			log("Technology map yielded processes:");
			for (auto &it : tpl->processes)
				log(" %s",RTLIL::id2cstr(it.first));
			log("\n");
			if (autoproc_mode) {
				Pass::call_on_module(tpl->design, tpl, "proc");
				log_assert(GetSize(tpl->processes) == 0);
			} else
				log_error("Technology map yielded processes -> this is not supported (use -autoproc to run 'proc' automatically).\n");
		}

		std::string orig_cell_name;
		pool<string> extra_src_attrs;

		if (!flatten_mode)
		{
			for (auto &it : tpl->cells_)
				if (it.first == "\\_TECHMAP_REPLACE_") {
					orig_cell_name = cell->name.str();
					module->rename(cell, stringf("$techmap%d", autoidx++) + cell->name.str());
					break;
				}

			extra_src_attrs = cell->get_strpool_attribute("\\src");
		}

		dict<IdString, IdString> memory_renames;

		for (auto &it : tpl->memories) {
			std::string m_name = it.first.str();
			apply_prefix(cell->name.str(), m_name);
			RTLIL::Memory *m = new RTLIL::Memory;
			m->name = m_name;
			m->width = it.second->width;
			m->start_offset = it.second->start_offset;
			m->size = it.second->size;
			m->attributes = it.second->attributes;
			if (m->attributes.count("\\src"))
				m->add_strpool_attribute("\\src", extra_src_attrs);
			module->memories[m->name] = m;
			memory_renames[it.first] = m->name;
			design->select(module, m);
		}

		std::map<RTLIL::IdString, RTLIL::IdString> positional_ports;

		for (auto &it : tpl->wires_) {
			if (it.second->port_id > 0)
				positional_ports[stringf("$%d", it.second->port_id)] = it.first;
			std::string w_name = it.second->name.str();
			apply_prefix(cell->name.str(), w_name);
			RTLIL::Wire *w = module->addWire(w_name, it.second);
			w->port_input = false;
			w->port_output = false;
			w->port_id = 0;
			if (it.second->get_bool_attribute("\\_techmap_special_"))
				w->attributes.clear();
			if (w->attributes.count("\\src"))
				w->add_strpool_attribute("\\src", extra_src_attrs);
			design->select(module, w);
		}

		SigMap tpl_sigmap(tpl);
		pool<SigBit> tpl_written_bits;

		for (auto &it1 : tpl->cells_)
		for (auto &it2 : it1.second->connections_)
			if (it1.second->output(it2.first))
				for (auto bit : tpl_sigmap(it2.second))
					tpl_written_bits.insert(bit);
		for (auto &it1 : tpl->connections_)
			for (auto bit : tpl_sigmap(it1.first))
				tpl_written_bits.insert(bit);

		SigMap port_signal_map;
		SigSig port_signal_assign;

		for (auto &it : cell->connections())
		{
			RTLIL::IdString portname = it.first;
			if (positional_ports.count(portname) > 0)
				portname = positional_ports.at(portname);
			if (tpl->wires_.count(portname) == 0 || tpl->wires_.at(portname)->port_id == 0) {
				if (portname.substr(0, 1) == "$")
					log_error("Can't map port `%s' of cell `%s' to template `%s'!\n", portname.c_str(), cell->name.c_str(), tpl->name.c_str());
				continue;
			}

			RTLIL::Wire *w = tpl->wires_.at(portname);
			RTLIL::SigSig c, extra_connect;

			if (w->port_output && !w->port_input) {
				c.first = it.second;
				c.second = RTLIL::SigSpec(w);
				apply_prefix(cell->name.str(), c.second, module);
				extra_connect.first = c.second;
				extra_connect.second = c.first;
			} else if (!w->port_output && w->port_input) {
				c.first = RTLIL::SigSpec(w);
				c.second = it.second;
				apply_prefix(cell->name.str(), c.first, module);
				extra_connect.first = c.first;
				extra_connect.second = c.second;
			} else {
				SigSpec sig_tpl = w, sig_tpl_pf = w, sig_mod = it.second;
				apply_prefix(cell->name.str(), sig_tpl_pf, module);
				for (int i = 0; i < GetSize(sig_tpl) && i < GetSize(sig_mod); i++) {
					if (tpl_written_bits.count(tpl_sigmap(sig_tpl[i]))) {
						c.first.append(sig_mod[i]);
						c.second.append(sig_tpl_pf[i]);
					} else {
						c.first.append(sig_tpl_pf[i]);
						c.second.append(sig_mod[i]);
					}
				}
				extra_connect.first = sig_tpl_pf;
				extra_connect.second = sig_mod;
			}

			if (c.second.size() > c.first.size())
				c.second.remove(c.first.size(), c.second.size() - c.first.size());

			if (c.second.size() < c.first.size())
				c.second.append(RTLIL::SigSpec(RTLIL::State::S0, c.first.size() - c.second.size()));

			log_assert(c.first.size() == c.second.size());

			if (flatten_mode)
			{
				// more conservative approach:
				// connect internal and external wires

				if (sigmaps.count(module) == 0)
					sigmaps[module].set(module);

				if (sigmaps.at(module)(c.first).has_const())
					log_error("Mismatch in directionality for cell port %s.%s.%s: %s <= %s\n",
						log_id(module), log_id(cell), log_id(it.first), log_signal(c.first), log_signal(c.second));

				module->connect(c);
			}
			else
			{
				// approach that yields nicer outputs:
				// replace internal wires that are connected to external wires

				if (w->port_output)
					port_signal_map.add(c.second, c.first);
				else
					port_signal_map.add(c.first, c.second);

				for (auto &attr : w->attributes) {
					if (attr.first == "\\src")
						continue;
					module->connect(extra_connect);
					break;
				}
			}
		}

		for (auto &it : tpl->cells_)
		{
			std::string c_name = it.second->name.str();

			if (!flatten_mode && c_name == "\\_TECHMAP_REPLACE_")
				c_name = orig_cell_name;
			else
				apply_prefix(cell->name.str(), c_name);

			RTLIL::Cell *c = module->addCell(c_name, it.second);
			design->select(module, c);

			if (!flatten_mode && c->type.substr(0, 2) == "\\$")
				c->type = c->type.substr(1);

			for (auto &it2 : c->connections_) {
				apply_prefix(cell->name.str(), it2.second, module);
				port_signal_map.apply(it2.second);
			}

			if (c->type == "$memrd" || c->type == "$memwr" || c->type == "$meminit") {
				IdString memid = c->getParam("\\MEMID").decode_string();
				log_assert(memory_renames.count(memid) != 0);
				c->setParam("\\MEMID", Const(memory_renames[memid].str()));
			}

			if (c->type == "$mem") {
				string memid = c->getParam("\\MEMID").decode_string();
				apply_prefix(cell->name.str(), memid);
				c->setParam("\\MEMID", Const(memid));
			}

			if (c->attributes.count("\\src"))
				c->add_strpool_attribute("\\src", extra_src_attrs);
		}

		for (auto &it : tpl->connections()) {
			RTLIL::SigSig c = it;
			apply_prefix(cell->name.str(), c.first, module);
			apply_prefix(cell->name.str(), c.second, module);
			port_signal_map.apply(c.first);
			port_signal_map.apply(c.second);
			module->connect(c);
		}

		module->remove(cell);
	}

	bool techmap_module(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Design *map, std::set<RTLIL::Cell*> &handled_cells,
			const std::map<RTLIL::IdString, std::set<RTLIL::IdString, RTLIL::sort_by_id_str>> &celltypeMap, bool in_recursion)
	{
		std::string mapmsg_prefix = in_recursion ? "Recursively mapping" : "Mapping";

		if (!design->selected(module))
			return false;

		bool log_continue = false;
		bool did_something = false;

		SigMap sigmap(module);

		TopoSort<RTLIL::Cell*, RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell>> cells;
		std::map<RTLIL::Cell*, std::set<RTLIL::SigBit>> cell_to_inbit;
		std::map<RTLIL::SigBit, std::set<RTLIL::Cell*>> outbit_to_cell;

		for (auto cell : module->cells())
		{
			if (!design->selected(module, cell) || handled_cells.count(cell) > 0)
				continue;

			std::string cell_type = cell->type.str();
			if (in_recursion && cell_type.substr(0, 2) == "\\$")
				cell_type = cell_type.substr(1);

			if (celltypeMap.count(cell_type) == 0) {
				if (assert_mode && cell_type.back() != '_')
					log_error("(ASSERT MODE) No matching template cell for type %s found.\n", log_id(cell_type));
				continue;
			}

			if (flatten_mode) {
				bool keepit = cell->get_bool_attribute("\\keep_hierarchy");
				for (auto &tpl_name : celltypeMap.at(cell_type))
					if (map->modules_[tpl_name]->get_bool_attribute("\\keep_hierarchy"))
						keepit = true;
				if (keepit) {
					if (!flatten_keep_list[cell]) {
						log("Keeping %s.%s (found keep_hierarchy property).\n", log_id(module), log_id(cell));
						flatten_keep_list.insert(cell);
					}
					if (!flatten_done_list[cell->type])
						flatten_do_list.insert(cell->type);
					continue;
				}
			}

			for (auto &conn : cell->connections())
			{
				RTLIL::SigSpec sig = sigmap(conn.second);
				sig.remove_const();

				if (GetSize(sig) == 0)
					continue;

				for (auto &tpl_name : celltypeMap.at(cell_type)) {
					RTLIL::Module *tpl = map->modules_[tpl_name];
					RTLIL::Wire *port = tpl->wire(conn.first);
					if (port && port->port_input)
						cell_to_inbit[cell].insert(sig.begin(), sig.end());
					if (port && port->port_output)
						for (auto &bit : sig)
							outbit_to_cell[bit].insert(cell);
				}
			}

			cells.node(cell);
		}

		for (auto &it_right : cell_to_inbit)
		for (auto &it_sigbit : it_right.second)
		for (auto &it_left : outbit_to_cell[it_sigbit])
			cells.edge(it_left, it_right.first);

		cells.sort();

		for (auto cell : cells.sorted)
		{
			log_assert(handled_cells.count(cell) == 0);
			log_assert(cell == module->cell(cell->name));
			bool mapped_cell = false;

			std::string cell_type = cell->type.str();
			if (in_recursion && cell_type.substr(0, 2) == "\\$")
				cell_type = cell_type.substr(1);

			for (auto &tpl_name : celltypeMap.at(cell_type))
			{
				RTLIL::IdString derived_name = tpl_name;
				RTLIL::Module *tpl = map->modules_[tpl_name];
				std::map<RTLIL::IdString, RTLIL::Const> parameters(cell->parameters.begin(), cell->parameters.end());

				if (tpl->get_bool_attribute("\\blackbox"))
					continue;

				if (!flatten_mode)
				{
					std::string extmapper_name;

					if (tpl->get_bool_attribute("\\techmap_simplemap"))
						extmapper_name = "simplemap";

					if (tpl->get_bool_attribute("\\techmap_maccmap"))
						extmapper_name = "maccmap";

					if (tpl->attributes.count("\\techmap_wrap"))
						extmapper_name = "wrap";

					if (!extmapper_name.empty())
					{
						cell->type = cell_type;

						if ((extern_mode && !in_recursion) || extmapper_name == "wrap")
						{
							std::string m_name = stringf("$extern:%s:%s", extmapper_name.c_str(), log_id(cell->type));

							for (auto &c : cell->parameters)
								m_name += stringf(":%s=%s", log_id(c.first), log_signal(c.second));

							if (extmapper_name == "wrap")
								m_name += ":" + sha1(tpl->attributes.at("\\techmap_wrap").decode_string());

							RTLIL::Design *extmapper_design = extern_mode && !in_recursion ? design : tpl->design;
							RTLIL::Module *extmapper_module = extmapper_design->module(m_name);

							if (extmapper_module == nullptr)
							{
								extmapper_module = extmapper_design->addModule(m_name);
								RTLIL::Cell *extmapper_cell = extmapper_module->addCell(cell->type, cell);

								int port_counter = 1;
								for (auto &c : extmapper_cell->connections_) {
									RTLIL::Wire *w = extmapper_module->addWire(c.first, GetSize(c.second));
									if (w->name == "\\Y" || w->name == "\\Q")
										w->port_output = true;
									else
										w->port_input = true;
									w->port_id = port_counter++;
									c.second = w;
								}

								extmapper_module->fixup_ports();
								extmapper_module->check();

								if (extmapper_name == "simplemap") {
									log("Creating %s with simplemap.\n", log_id(extmapper_module));
									if (simplemap_mappers.count(extmapper_cell->type) == 0)
										log_error("No simplemap mapper for cell type %s found!\n", log_id(extmapper_cell->type));
									simplemap_mappers.at(extmapper_cell->type)(extmapper_module, extmapper_cell);
									extmapper_module->remove(extmapper_cell);
								}

								if (extmapper_name == "maccmap") {
									log("Creating %s with maccmap.\n", log_id(extmapper_module));
									if (extmapper_cell->type != "$macc")
										log_error("The maccmap mapper can only map $macc (not %s) cells!\n", log_id(extmapper_cell->type));
									maccmap(extmapper_module, extmapper_cell);
									extmapper_module->remove(extmapper_cell);
								}

								if (extmapper_name == "wrap") {
									std::string cmd_string = tpl->attributes.at("\\techmap_wrap").decode_string();
									log("Running \"%s\" on wrapper %s.\n", cmd_string.c_str(), log_id(extmapper_module));
									Pass::call_on_module(extmapper_design, extmapper_module, cmd_string);
									log_continue = true;
								}
							}

							cell->type = extmapper_module->name;
							cell->parameters.clear();

							if (!extern_mode || in_recursion) {
								tpl = extmapper_module;
								goto use_wrapper_tpl;
							}

							log("%s %s.%s (%s) to %s.\n", mapmsg_prefix.c_str(), log_id(module), log_id(cell), log_id(cell->type), log_id(extmapper_module));
						}
						else
						{
							log("%s %s.%s (%s) with %s.\n", mapmsg_prefix.c_str(), log_id(module), log_id(cell), log_id(cell->type), extmapper_name.c_str());

							if (extmapper_name == "simplemap") {
								if (simplemap_mappers.count(cell->type) == 0)
									log_error("No simplemap mapper for cell type %s found!\n", RTLIL::id2cstr(cell->type));
								simplemap_mappers.at(cell->type)(module, cell);
							}

							if (extmapper_name == "maccmap") {
								if (cell->type != "$macc")
									log_error("The maccmap mapper can only map $macc (not %s) cells!\n", log_id(cell->type));
								maccmap(module, cell);
							}

							module->remove(cell);
							cell = NULL;
						}

						did_something = true;
						mapped_cell = true;
						break;
					}

					for (auto conn : cell->connections()) {
						if (conn.first.substr(0, 1) == "$")
							continue;
						if (tpl->wires_.count(conn.first) > 0 && tpl->wires_.at(conn.first)->port_id > 0)
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

					for (auto conn : cell->connections()) {
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

					for (auto conn : cell->connections())
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

					for (auto conn : cell->connections())
						if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONNMAP_%s_", RTLIL::id2cstr(conn.first))) != 0) {
							RTLIL::Const value;
							for (auto &bit : sigmap(conn.second).to_sigbit_vector()) {
								RTLIL::Const chunk(unique_bit_id.at(bit), bits);
								value.bits.insert(value.bits.end(), chunk.bits.begin(), chunk.bits.end());
							}
							parameters[stringf("\\_TECHMAP_CONNMAP_%s_", RTLIL::id2cstr(conn.first))] = value;
						}
				}

				if (0) {
			use_wrapper_tpl:;
					// do not register techmap_wrap modules with techmap_cache
				} else {
					std::pair<RTLIL::IdString, std::map<RTLIL::IdString, RTLIL::Const>> key(tpl_name, parameters);
					if (techmap_cache.count(key) > 0) {
						tpl = techmap_cache[key];
					} else {
						if (parameters.size() != 0) {
							derived_name = tpl->derive(map, dict<RTLIL::IdString, RTLIL::Const>(parameters.begin(), parameters.end()));
							tpl = map->module(derived_name);
							log_continue = true;
						}
						techmap_cache[key] = tpl;
					}
				}

				if (flatten_mode) {
					techmap_do_cache[tpl] = true;
				} else {
					RTLIL::Module *constmapped_tpl = map->module(constmap_tpl_name(sigmap, tpl, cell, false));
					if (constmapped_tpl != nullptr)
						tpl = constmapped_tpl;
				}

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

							const char *p = data.wire->name.c_str();
							const char *q = strrchr(p+1, '.');
							q = q ? q : p+1;

							std::string cmd_string = data.value.as_const().decode_string();

						restart_eval_cmd_string:
							if (cmd_string.rfind("CONSTMAP; ", 0) == 0)
							{
								cmd_string = cmd_string.substr(strlen("CONSTMAP; "));

								log("Analyzing pattern of constant bits for this cell:\n");
								RTLIL::IdString new_tpl_name = constmap_tpl_name(sigmap, tpl, cell, true);
								log("Creating constmapped module `%s'.\n", log_id(new_tpl_name));
								log_assert(map->module(new_tpl_name) == nullptr);

								RTLIL::Module *new_tpl = map->addModule(new_tpl_name);
								tpl->cloneInto(new_tpl);

								techmap_do_cache.erase(tpl);
								techmap_do_cache[new_tpl] = true;
								tpl = new_tpl;

								std::map<RTLIL::SigBit, RTLIL::SigBit> port_new2old_map;
								std::map<RTLIL::SigBit, RTLIL::SigBit> port_connmap;
								std::map<RTLIL::SigBit, RTLIL::SigBit> cellbits_to_tplbits;

								for (auto wire : tpl->wires().to_vector())
								{
									if (!wire->port_input || wire->port_output)
										continue;

									RTLIL::IdString port_name = wire->name;
									tpl->rename(wire, NEW_ID);

									RTLIL::Wire *new_wire = tpl->addWire(port_name, wire);
									wire->port_input = false;
									wire->port_id = 0;

									for (int i = 0; i < wire->width; i++) {
										port_new2old_map[RTLIL::SigBit(new_wire, i)] = RTLIL::SigBit(wire, i);
										port_connmap[RTLIL::SigBit(wire, i)] = RTLIL::SigBit(new_wire, i);
									}
								}

								for (auto conn : cell->connections())
									for (int i = 0; i < GetSize(conn.second); i++)
									{
										RTLIL::SigBit bit = sigmap(conn.second[i]);
										RTLIL::SigBit tplbit(tpl->wire(conn.first), i);

										if (bit.wire == nullptr)
										{
											RTLIL::SigBit oldbit = port_new2old_map.at(tplbit);
											port_connmap.at(oldbit) = bit;
										}
										else if (cellbits_to_tplbits.count(bit))
										{
											RTLIL::SigBit oldbit = port_new2old_map.at(tplbit);
											port_connmap.at(oldbit) = cellbits_to_tplbits[bit];
										}
										else
											cellbits_to_tplbits[bit] = tplbit;
									}

								RTLIL::SigSig port_conn;
								for (auto &it : port_connmap) {
									port_conn.first.append_bit(it.first);
									port_conn.second.append_bit(it.second);
								}
								tpl->connect(port_conn);

								tpl->check();
								goto restart_eval_cmd_string;
							}

							if (cmd_string.rfind("RECURSION; ", 0) == 0)
							{
								cmd_string = cmd_string.substr(strlen("RECURSION; "));
								while (techmap_module(map, tpl, map, handled_cells, celltypeMap, true)) { }
								goto restart_eval_cmd_string;
							}

							Pass::call_on_module(map, tpl, cmd_string);

							log_assert(!strncmp(q, "_TECHMAP_DO_", 12));
							std::string new_name = data.wire->name.substr(0, q-p) + "_TECHMAP_DONE_" + data.wire->name.substr(q-p+12);
							while (tpl->wires_.count(new_name))
								new_name += "_";
							tpl->rename(data.wire->name, new_name);

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

					if (recursive_mode) {
						if (log_continue) {
							log_header(design, "Continuing TECHMAP pass.\n");
							log_continue = false;
						}
						while (techmap_module(map, tpl, map, handled_cells, celltypeMap, true)) { }
					}
				}

				if (techmap_do_cache.at(tpl) == false)
					continue;

				if (log_continue) {
					log_header(design, "Continuing TECHMAP pass.\n");
					log_continue = false;
				}

				if (extern_mode && !in_recursion)
				{
					std::string m_name = stringf("$extern:%s", log_id(tpl));

					if (!design->module(m_name))
					{
						RTLIL::Module *m = design->addModule(m_name);
						tpl->cloneInto(m);

						for (auto cell : m->cells()) {
							if (cell->type.substr(0, 2) == "\\$")
								cell->type = cell->type.substr(1);
						}

						module_queue.insert(m);
					}

					log("%s %s.%s to imported %s.\n", mapmsg_prefix.c_str(), log_id(module), log_id(cell), log_id(m_name));
					cell->type = m_name;
					cell->parameters.clear();
				}
				else
				{
					log("%s %s.%s using %s.\n", mapmsg_prefix.c_str(), log_id(module), log_id(cell), log_id(tpl));
					techmap_module_worker(design, module, cell, tpl);
					cell = NULL;
				}
				did_something = true;
				mapped_cell = true;
				break;
			}

			if (assert_mode && !mapped_cell)
				log_error("(ASSERT MODE) Failed to map cell %s.%s (%s).\n", log_id(module), log_id(cell), log_id(cell->type));

			handled_cells.insert(cell);
		}

		if (log_continue) {
			log_header(design, "Continuing TECHMAP pass.\n");
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
		log("the design with implementations given in form of a Verilog or ilang source\n");
		log("file.\n");
		log("\n");
		log("    -map filename\n");
		log("        the library of cell implementations to be used.\n");
		log("        without this parameter a builtin library is used that\n");
		log("        transforms the internal RTL cells to the internal gate\n");
		log("        library.\n");
		log("\n");
		log("    -map %%<design-name>\n");
		log("        like -map above, but with an in-memory design instead of a file.\n");
		log("\n");
		log("    -extern\n");
		log("        load the cell implementations as separate modules into the design\n");
		log("        instead of inlining them.\n");
		log("\n");
		log("    -max_iter <number>\n");
		log("        only run the specified number of iterations.\n");
		log("\n");
		log("    -recursive\n");
		log("        instead of the iterative breadth-first algorithm use a recursive\n");
		log("        depth-first algorithm. both methods should yield equivalent results,\n");
		log("        but may differ in performance.\n");
		log("\n");
		log("    -autoproc\n");
		log("        Automatically call \"proc\" on implementations that contain processes.\n");
		log("\n");
		log("    -assert\n");
		log("        this option will cause techmap to exit with an error if it can't map\n");
		log("        a selected cell. only cell types that end on an underscore are accepted\n");
		log("        as final cell types by this mode.\n");
		log("\n");
		log("    -D <define>, -I <incdir>\n");
		log("        this options are passed as-is to the Verilog frontend for loading the\n");
		log("        map file. Note that the Verilog frontend is also called with the\n");
		log("        '-ignore_redef' option set.\n");
		log("\n");
		log("When a module in the map file has the 'techmap_celltype' attribute set, it will\n");
		log("match cells with a type that match the text value of this attribute. Otherwise\n");
		log("the module name will be used to match the cell.\n");
		log("\n");
		log("When a module in the map file has the 'techmap_simplemap' attribute set, techmap\n");
		log("will use 'simplemap' (see 'help simplemap') to map cells matching the module.\n");
		log("\n");
		log("When a module in the map file has the 'techmap_maccmap' attribute set, techmap\n");
		log("will use 'maccmap' (see 'help maccmap') to map cells matching the module.\n");
		log("\n");
		log("When a module in the map file has the 'techmap_wrap' attribute set, techmap\n");
		log("will create a wrapper for the cell and then run the command string that the\n");
		log("attribute is set to on the wrapper module.\n");
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
		log("        A _TECHMAP_DO_* command may start with the special token 'CONSTMAP; '.\n");
		log("        in this case techmap will create a copy for each distinct configuration\n");
		log("        of constant inputs and shorted inputs at this point and import the\n");
		log("        constant and connected bits into the map module. All further commands\n");
		log("        are executed in this copy. This is a very convenient way of creating\n");
		log("        optimized specializations of techmap modules without using the special\n");
		log("        parameters described below.\n");
		log("\n");
		log("        A _TECHMAP_DO_* command may start with the special token 'RECURSION; '.\n");
		log("        then techmap will recursively replace the cells in the module with their\n");
		log("        implementation. This is not affected by the -max_iter option.\n");
		log("\n");
		log("        It is possible to combine both prefixes to 'RECURSION; CONSTMAP; '.\n");
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
		log("of the cell that is being replaced.\n");
		log("\n");
		log("See 'help extract' for a pass that does the opposite thing.\n");
		log("\n");
		log("See 'help flatten' for a pass that does flatten the design (which is\n");
		log("essentially techmap but using the design itself as map library).\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing TECHMAP pass (map to technology primitives).\n");
		log_push();

		TechmapWorker worker;
		simplemap_get_mappers(worker.simplemap_mappers);

		std::vector<std::string> map_files;
		std::string verilog_frontend = "verilog -ignore_redef";
		int max_iter = -1;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				map_files.push_back(args[++argidx]);
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
			if (args[argidx] == "-assert") {
				worker.assert_mode = true;
				continue;
			}
			if (args[argidx] == "-extern") {
				worker.extern_mode = true;
				continue;
			}
			if (args[argidx] == "-recursive") {
				worker.recursive_mode = true;
				continue;
			}
			if (args[argidx] == "-autoproc") {
				worker.autoproc_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Design *map = new RTLIL::Design;
		if (map_files.empty()) {
			std::istringstream f(stdcells_code);
			Frontend::frontend_call(map, &f, "<techmap.v>", verilog_frontend);
		} else
			for (auto &fn : map_files)
				if (fn.substr(0, 1) == "%") {
					if (!saved_designs.count(fn.substr(1))) {
						delete map;
						log_cmd_error("Can't saved design `%s'.\n", fn.c_str()+1);
					}
					for (auto mod : saved_designs.at(fn.substr(1))->modules())
						if (!map->has(mod->name))
							map->add(mod->clone());
				} else {
					std::ifstream f;
					rewrite_filename(fn);
					f.open(fn.c_str());
					if (f.fail())
						log_cmd_error("Can't open map file `%s'\n", fn.c_str());
					Frontend::frontend_call(map, &f, fn, (fn.size() > 3 && fn.substr(fn.size()-3) == ".il") ? "ilang" : verilog_frontend);
				}

		std::map<RTLIL::IdString, std::set<RTLIL::IdString, RTLIL::sort_by_id_str>> celltypeMap;
		for (auto &it : map->modules_) {
			if (it.second->attributes.count("\\techmap_celltype") && !it.second->attributes.at("\\techmap_celltype").bits.empty()) {
				char *p = strdup(it.second->attributes.at("\\techmap_celltype").decode_string().c_str());
				for (char *q = strtok(p, " \t\r\n"); q; q = strtok(NULL, " \t\r\n"))
					celltypeMap[RTLIL::escape_id(q)].insert(it.first);
				free(p);
			} else {
				string module_name = it.first.str();
				if (module_name.substr(0, 2) == "\\$")
					module_name = module_name.substr(1);
				celltypeMap[module_name].insert(it.first);
			}
		}

		for (auto module : design->modules())
			worker.module_queue.insert(module);

		while (!worker.module_queue.empty())
		{
			RTLIL::Module *module = *worker.module_queue.begin();
			worker.module_queue.erase(module);

			bool did_something = true;
			std::set<RTLIL::Cell*> handled_cells;
			while (did_something) {
				did_something = false;
					if (worker.techmap_module(design, module, map, handled_cells, celltypeMap, false))
						did_something = true;
				if (did_something)
					module->check();
				if (max_iter > 0 && --max_iter == 0)
					break;
			}
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
		log("pass is very similar to the 'techmap' pass. The only difference is that this\n");
		log("pass is using the current design as mapping library.\n");
		log("\n");
		log("Cells and/or modules with the 'keep_hierarchy' attribute set will not be\n");
		log("flattened by this command.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing FLATTEN pass (flatten design).\n");
		log_push();

		extra_args(args, 1, design);

		TechmapWorker worker;
		worker.flatten_mode = true;

		std::map<RTLIL::IdString, std::set<RTLIL::IdString, RTLIL::sort_by_id_str>> celltypeMap;
		for (auto module : design->modules())
			celltypeMap[module->name].insert(module->name);

		RTLIL::Module *top_mod = NULL;
		if (design->full_selection())
			for (auto mod : design->modules())
				if (mod->get_bool_attribute("\\top"))
					top_mod = mod;

		std::set<RTLIL::Cell*> handled_cells;
		if (top_mod != NULL) {
			worker.flatten_do_list.insert(top_mod->name);
			while (!worker.flatten_do_list.empty()) {
				auto mod = design->module(*worker.flatten_do_list.begin());
				while (worker.techmap_module(design, mod, design, handled_cells, celltypeMap, false)) { }
				worker.flatten_done_list.insert(mod->name);
				worker.flatten_do_list.erase(mod->name);
			}
		} else {
			for (auto mod : vector<Module*>(design->modules())) {
				while (worker.techmap_module(design, mod, design, handled_cells, celltypeMap, false)) { }
			}
		}

		log("No more expansions possible.\n");

		if (top_mod != NULL)
		{
			pool<RTLIL::IdString> used_modules, new_used_modules;
			new_used_modules.insert(top_mod->name);
			while (!new_used_modules.empty()) {
				pool<RTLIL::IdString> queue;
				queue.swap(new_used_modules);
				for (auto modname : queue)
					used_modules.insert(modname);
				for (auto modname : queue)
					for (auto cell : design->module(modname)->cells())
						if (design->module(cell->type) && !used_modules[cell->type])
							new_used_modules.insert(cell->type);
			}

			dict<RTLIL::IdString, RTLIL::Module*> new_modules;
			for (auto mod : vector<Module*>(design->modules()))
				if (used_modules[mod->name] || mod->get_bool_attribute("\\blackbox")) {
					new_modules[mod->name] = mod;
				} else {
					log("Deleting now unused module %s.\n", log_id(mod));
					delete mod;
				}
			design->modules_.swap(new_modules);
		}

		log_pop();
	}
} FlattenPass;

PRIVATE_NAMESPACE_END
