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

#include "kernel/yosys.h"
#include "kernel/utils.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "libs/sha1/sha1.h"

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "simplemap.h"

YOSYS_NAMESPACE_BEGIN

// see maccmap.cc
extern void maccmap(RTLIL::Module *module, RTLIL::Cell *cell, bool unmap = false);

YOSYS_NAMESPACE_END

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void apply_prefix(IdString prefix, IdString &id)
{
	if (id[0] == '\\')
		id = stringf("%s.%s", prefix.c_str(), id.c_str()+1);
	else
		id = stringf("$techmap%s.%s", prefix.c_str(), id.c_str());
}

void apply_prefix(IdString prefix, RTLIL::SigSpec &sig, RTLIL::Module *module)
{
	vector<SigChunk> chunks = sig;
	for (auto &chunk : chunks)
		if (chunk.wire != nullptr) {
			IdString wire_name = chunk.wire->name;
			apply_prefix(prefix, wire_name);
			log_assert(module->wire(wire_name) != nullptr);
			chunk.wire = module->wire(wire_name);
		}
	sig = chunks;
}

struct TechmapWorker
{
	dict<IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> simplemap_mappers;
	dict<std::pair<IdString, dict<IdString, RTLIL::Const>>, RTLIL::Module*> techmap_cache;
	dict<RTLIL::Module*, bool> techmap_do_cache;
	pool<RTLIL::Module*> module_queue;
	dict<Module*, SigMap> sigmaps;

	pool<string> log_msg_cache;

	struct TechmapWireData {
		RTLIL::Wire *wire;
		RTLIL::SigSpec value;
	};

	typedef dict<IdString, std::vector<TechmapWireData>> TechmapWires;

	bool extern_mode = false;
	bool assert_mode = false;
	bool recursive_mode = false;
	bool autoproc_mode = false;
	bool ignore_wb = false;

	std::string constmap_tpl_name(SigMap &sigmap, RTLIL::Module *tpl, RTLIL::Cell *cell, bool verbose)
	{
		std::string constmap_info;
		dict<RTLIL::SigBit, std::pair<IdString, int>> connbits_map;

		for (auto &conn : cell->connections())
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
					connbits_map.emplace(bit, std::make_pair(conn.first, i));
					constmap_info += stringf("|%s %d", log_id(conn.first), i);
				}
			}

		return stringf("$paramod$constmap:%s%s", sha1(constmap_info).c_str(), tpl->name.c_str());
	}

	TechmapWires techmap_find_special_wires(RTLIL::Module *module)
	{
		TechmapWires result;

		if (module == nullptr)
			return result;

		for (auto w : module->wires()) {
			if (*w->name.c_str() == '$')
				continue;

			if (w->name.contains("_TECHMAP_") && !w->name.contains("_TECHMAP_REPLACE_")) {
				TechmapWireData record;
				record.wire = w;
				record.value = w;
				result[w->name].push_back(record);
				w->set_bool_attribute(ID::keep);
				w->set_bool_attribute(ID::_techmap_special_);
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
				log(" %s",log_id(it.first));
			log("\n");
			if (autoproc_mode) {
				Pass::call_on_module(tpl->design, tpl, "proc");
				log_assert(GetSize(tpl->processes) == 0);
			} else
				log_error("Technology map yielded processes -> this is not supported (use -autoproc to run 'proc' automatically).\n");
		}

		std::string orig_cell_name;
		pool<string> extra_src_attrs = cell->get_strpool_attribute(ID::src);

		orig_cell_name = cell->name.str();
		for (auto tpl_cell : tpl->cells())
			if (tpl_cell->name.ends_with("_TECHMAP_REPLACE_")) {
				module->rename(cell, stringf("$techmap%d", autoidx++) + cell->name.str());
				break;
			}

		dict<IdString, IdString> memory_renames;

		for (auto &it : tpl->memories) {
			IdString m_name = it.first;
			apply_prefix(cell->name, m_name);
			RTLIL::Memory *m = module->addMemory(m_name, it.second);
			if (m->attributes.count(ID::src))
				m->add_strpool_attribute(ID::src, extra_src_attrs);
			memory_renames[it.first] = m->name;
			design->select(module, m);
		}

		dict<IdString, IdString> positional_ports;
		dict<Wire*, IdString> temp_renamed_wires;
		pool<SigBit> autopurge_tpl_bits;

		for (auto tpl_w : tpl->wires())
		{
			if (tpl_w->port_id > 0)
			{
				IdString posportname = stringf("$%d", tpl_w->port_id);
				positional_ports.emplace(posportname, tpl_w->name);

				if (tpl_w->get_bool_attribute(ID::techmap_autopurge) &&
						(!cell->hasPort(tpl_w->name) || !GetSize(cell->getPort(tpl_w->name))) &&
						(!cell->hasPort(posportname) || !GetSize(cell->getPort(posportname))))
				{
					if (sigmaps.count(tpl) == 0)
						sigmaps[tpl].set(tpl);

					for (auto bit : sigmaps.at(tpl)(tpl_w))
						if (bit.wire != nullptr)
							autopurge_tpl_bits.insert(bit);
				}
			}
			IdString w_name = tpl_w->name;
			apply_prefix(cell->name, w_name);
			RTLIL::Wire *w = module->wire(w_name);
			if (w != nullptr) {
				temp_renamed_wires[w] = w->name;
				module->rename(w, NEW_ID);
				w = nullptr;
			}
			if (w == nullptr) {
				w = module->addWire(w_name, tpl_w);
				w->port_input = false;
				w->port_output = false;
				w->port_id = 0;
				w->attributes.erase(ID::techmap_autopurge);
				if (tpl_w->get_bool_attribute(ID::_techmap_special_))
					w->attributes.clear();
				if (w->attributes.count(ID::src))
					w->add_strpool_attribute(ID::src, extra_src_attrs);
			}
			design->select(module, w);

			if (const char *p = strstr(tpl_w->name.c_str(), "_TECHMAP_REPLACE_.")) {
				IdString replace_name = stringf("%s%s", orig_cell_name.c_str(), p + strlen("_TECHMAP_REPLACE_"));
				Wire *replace_w = module->addWire(replace_name, tpl_w);
				module->connect(replace_w, w);
			}
		}

		pool<SigBit> tpl_written_bits;
		for (auto tpl_cell : tpl->cells())
		for (auto &conn : tpl_cell->connections())
			if (tpl_cell->output(conn.first))
				for (auto bit : conn.second)
					tpl_written_bits.insert(bit);
		for (auto &conn : tpl->connections())
			for (auto bit : conn.first)
				tpl_written_bits.insert(bit);

		SigMap port_signal_map;

		for (auto &it : cell->connections())
		{
			IdString portname = it.first;
			if (positional_ports.count(portname) > 0)
				portname = positional_ports.at(portname);
			if (tpl->wire(portname) == nullptr || tpl->wire(portname)->port_id == 0) {
				if (portname.begins_with("$"))
					log_error("Can't map port `%s' of cell `%s' to template `%s'!\n", portname.c_str(), cell->name.c_str(), tpl->name.c_str());
				continue;
			}

			if (GetSize(it.second) == 0)
				continue;

			RTLIL::Wire *w = tpl->wire(portname);
			RTLIL::SigSig c, extra_connect;

			if (w->port_output && !w->port_input) {
				c.first = it.second;
				c.second = RTLIL::SigSpec(w);
				apply_prefix(cell->name, c.second, module);
				extra_connect.first = c.second;
				extra_connect.second = c.first;
			} else if (!w->port_output && w->port_input) {
				c.first = RTLIL::SigSpec(w);
				c.second = it.second;
				apply_prefix(cell->name, c.first, module);
				extra_connect.first = c.first;
				extra_connect.second = c.second;
			} else {
				SigSpec sig_tpl = w, sig_tpl_pf = w, sig_mod = it.second;
				apply_prefix(cell->name, sig_tpl_pf, module);
				for (int i = 0; i < GetSize(sig_tpl) && i < GetSize(sig_mod); i++) {
					if (tpl_written_bits.count(sig_tpl[i])) {
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

			// replace internal wires that are connected to external wires

			if (w->port_output && !w->port_input) {
				port_signal_map.add(c.second, c.first);
			} else
			if (!w->port_output && w->port_input) {
				port_signal_map.add(c.first, c.second);
			} else {
				module->connect(c);
				extra_connect = SigSig();
			}

			for (auto &attr : w->attributes) {
				if (attr.first == ID::src)
					continue;
				auto lhs = GetSize(extra_connect.first);
				auto rhs = GetSize(extra_connect.second);
				if (lhs > rhs)
					extra_connect.first.remove(rhs, lhs-rhs);
				else if (rhs > lhs)
					extra_connect.second.remove(lhs, rhs-lhs);
				module->connect(extra_connect);
				break;
			}
		}

		for (auto tpl_cell : tpl->cells())
		{
			IdString c_name = tpl_cell->name;
			bool techmap_replace_cell = c_name.ends_with("_TECHMAP_REPLACE_");

			if (techmap_replace_cell)
				c_name = orig_cell_name;
			else if (const char *p = strstr(tpl_cell->name.c_str(), "_TECHMAP_REPLACE_."))
				c_name = stringf("%s%s", orig_cell_name.c_str(), p + strlen("_TECHMAP_REPLACE_"));
			else
				apply_prefix(cell->name, c_name);

			RTLIL::Cell *c = module->addCell(c_name, tpl_cell);
			design->select(module, c);

			if (c->type.begins_with("\\$"))
				c->type = c->type.substr(1);
			
			if (c->type == ID::_TECHMAP_PLACEHOLDER_ && tpl_cell->has_attribute(ID::techmap_chtype)) {
				c->type = RTLIL::escape_id(tpl_cell->get_string_attribute(ID::techmap_chtype));
				c->attributes.erase(ID::techmap_chtype);
			}

			vector<IdString> autopurge_ports;

			for (auto &conn : c->connections())
			{
				bool autopurge = false;
				if (!autopurge_tpl_bits.empty()) {
					autopurge = GetSize(conn.second) != 0;
					for (auto &bit : sigmaps.at(tpl)(conn.second))
						if (!autopurge_tpl_bits.count(bit)) {
							autopurge = false;
							break;
						}
				}

				if (autopurge) {
					autopurge_ports.push_back(conn.first);
				} else {
					RTLIL::SigSpec new_conn = conn.second;
					apply_prefix(cell->name, new_conn, module);
					port_signal_map.apply(new_conn);
					c->setPort(conn.first, std::move(new_conn));
				}
			}

			for (auto &it2 : autopurge_ports)
				c->unsetPort(it2);

			if (c->has_memid()) {
				IdString memid = c->getParam(ID::MEMID).decode_string();
				log_assert(memory_renames.count(memid) != 0);
				c->setParam(ID::MEMID, Const(memory_renames[memid].str()));
			} else if (c->is_mem_cell()) {
				IdString memid = c->getParam(ID::MEMID).decode_string();
				apply_prefix(cell->name, memid);
				c->setParam(ID::MEMID, Const(memid.c_str()));
			}

			if (c->attributes.count(ID::src))
				c->add_strpool_attribute(ID::src, extra_src_attrs);

			if (techmap_replace_cell) {
				for (auto attr : cell->attributes)
					if (!c->attributes.count(attr.first))
						c->attributes[attr.first] = attr.second;
				c->attributes.erase(ID::reprocess_after);
			}
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

		for (auto &it : temp_renamed_wires)
		{
			Wire *w = it.first;
			IdString name = it.second;
			IdString altname = module->uniquify(name);
			Wire *other_w = module->wire(name);
			module->rename(other_w, altname);
			module->rename(w, name);
		}
	}

	bool techmap_module(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Design *map, pool<RTLIL::Cell*> &handled_cells,
			const dict<IdString, pool<IdString>> &celltypeMap, bool in_recursion)
	{
		std::string mapmsg_prefix = in_recursion ? "Recursively mapping" : "Mapping";

		if (!design->selected(module) || module->get_blackbox_attribute(ignore_wb))
			return false;

		bool log_continue = false;
		bool did_something = false;
		LogMakeDebugHdl mkdebug;

		SigMap sigmap(module);
		FfInitVals initvals(&sigmap, module);

		TopoSort<RTLIL::Cell*, IdString::compare_ptr_by_name<RTLIL::Cell>> cells;
		dict<RTLIL::Cell*, pool<RTLIL::SigBit>> cell_to_inbit;
		dict<RTLIL::SigBit, pool<RTLIL::Cell*>> outbit_to_cell;

		for (auto cell : module->selected_cells())
		{
			if (handled_cells.count(cell) > 0)
				continue;

			std::string cell_type = cell->type.str();
			if (in_recursion && cell->type.begins_with("\\$"))
				cell_type = cell_type.substr(1);

			if (celltypeMap.count(cell_type) == 0) {
				if (assert_mode && cell_type.back() != '_')
					log_error("(ASSERT MODE) No matching template cell for type %s found.\n", log_id(cell_type));
				continue;
			}

			for (auto &conn : cell->connections())
			{
				RTLIL::SigSpec sig = sigmap(conn.second);
				sig.remove_const();

				if (GetSize(sig) == 0)
					continue;

				for (auto &tpl_name : celltypeMap.at(cell_type)) {
					RTLIL::Module *tpl = map->module(tpl_name);
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

			if (in_recursion && cell->type.begins_with("\\$"))
				cell_type = cell_type.substr(1);

			for (auto &tpl_name : celltypeMap.at(cell_type))
			{
				IdString derived_name = tpl_name;
				RTLIL::Module *tpl = map->module(tpl_name);
				dict<IdString, RTLIL::Const> parameters(cell->parameters);

				if (tpl->get_blackbox_attribute(ignore_wb))
					continue;

				std::string extmapper_name;

				if (tpl->get_bool_attribute(ID::techmap_simplemap))
					extmapper_name = "simplemap";

				if (tpl->get_bool_attribute(ID::techmap_maccmap))
					extmapper_name = "maccmap";

				if (tpl->attributes.count(ID::techmap_wrap))
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
							m_name += ":" + sha1(tpl->attributes.at(ID::techmap_wrap).decode_string());

						RTLIL::Design *extmapper_design = extern_mode && !in_recursion ? design : tpl->design;
						RTLIL::Module *extmapper_module = extmapper_design->module(m_name);

						if (extmapper_module == nullptr)
						{
							extmapper_module = extmapper_design->addModule(m_name);
							RTLIL::Cell *extmapper_cell = extmapper_module->addCell(cell->type, cell);

							extmapper_cell->set_src_attribute(cell->get_src_attribute());

							int port_counter = 1;
							for (auto &c : extmapper_cell->connections_) {
								RTLIL::Wire *w = extmapper_module->addWire(c.first, GetSize(c.second));
								if (w->name.in(ID::Y, ID::Q))
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
								if (extmapper_cell->type != ID($macc))
									log_error("The maccmap mapper can only map $macc (not %s) cells!\n", log_id(extmapper_cell->type));
								maccmap(extmapper_module, extmapper_cell);
								extmapper_module->remove(extmapper_cell);
							}

							if (extmapper_name == "wrap") {
								std::string cmd_string = tpl->attributes.at(ID::techmap_wrap).decode_string();
								log("Running \"%s\" on wrapper %s.\n", cmd_string.c_str(), log_id(extmapper_module));
								mkdebug.on();
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

						auto msg = stringf("Using extmapper %s for cells of type %s.", log_id(extmapper_module), log_id(cell->type));
						if (!log_msg_cache.count(msg)) {
							log_msg_cache.insert(msg);
							log("%s\n", msg.c_str());
						}
						log_debug("%s %s.%s (%s) to %s.\n", mapmsg_prefix.c_str(), log_id(module), log_id(cell), log_id(cell->type), log_id(extmapper_module));
					}
					else
					{
						auto msg = stringf("Using extmapper %s for cells of type %s.", extmapper_name.c_str(), log_id(cell->type));
						if (!log_msg_cache.count(msg)) {
							log_msg_cache.insert(msg);
							log("%s\n", msg.c_str());
						}
						log_debug("%s %s.%s (%s) with %s.\n", mapmsg_prefix.c_str(), log_id(module), log_id(cell), log_id(cell->type), extmapper_name.c_str());

						if (extmapper_name == "simplemap") {
							if (simplemap_mappers.count(cell->type) == 0)
								log_error("No simplemap mapper for cell type %s found!\n", log_id(cell->type));
							simplemap_mappers.at(cell->type)(module, cell);
						}

						if (extmapper_name == "maccmap") {
							if (cell->type != ID($macc))
								log_error("The maccmap mapper can only map $macc (not %s) cells!\n", log_id(cell->type));
							maccmap(module, cell);
						}

						module->remove(cell);
						cell = nullptr;
					}

					did_something = true;
					mapped_cell = true;
					break;
				}

				for (auto &conn : cell->connections()) {
					if (conn.first.begins_with("$"))
						continue;
					if (tpl->wire(conn.first) != nullptr && tpl->wire(conn.first)->port_id > 0)
						continue;
					if (!conn.second.is_fully_const() || parameters.count(conn.first) > 0 || tpl->avail_parameters.count(conn.first) == 0)
						goto next_tpl;
					parameters[conn.first] = conn.second.as_const();
				}

				if (0) {
		next_tpl:
					continue;
				}

				if (tpl->avail_parameters.count(ID::_TECHMAP_CELLTYPE_) != 0)
					parameters.emplace(ID::_TECHMAP_CELLTYPE_, RTLIL::unescape_id(cell->type));
				if (tpl->avail_parameters.count(ID::_TECHMAP_CELLNAME_) != 0)
					parameters.emplace(ID::_TECHMAP_CELLNAME_, RTLIL::unescape_id(cell->name));

				for (auto &conn : cell->connections()) {
					if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONSTMSK_%s_", log_id(conn.first))) != 0) {
						std::vector<RTLIL::SigBit> v = sigmap(conn.second).to_sigbit_vector();
						for (auto &bit : v)
							bit = RTLIL::SigBit(bit.wire == nullptr ? RTLIL::State::S1 : RTLIL::State::S0);
						parameters.emplace(stringf("\\_TECHMAP_CONSTMSK_%s_", log_id(conn.first)), RTLIL::SigSpec(v).as_const());
					}
					if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONSTVAL_%s_", log_id(conn.first))) != 0) {
						std::vector<RTLIL::SigBit> v = sigmap(conn.second).to_sigbit_vector();
						for (auto &bit : v)
							if (bit.wire != nullptr)
								bit = RTLIL::SigBit(RTLIL::State::Sx);
						parameters.emplace(stringf("\\_TECHMAP_CONSTVAL_%s_", log_id(conn.first)), RTLIL::SigSpec(v).as_const());
					}
					if (tpl->avail_parameters.count(stringf("\\_TECHMAP_WIREINIT_%s_", log_id(conn.first))) != 0) {
						parameters.emplace(stringf("\\_TECHMAP_WIREINIT_%s_", log_id(conn.first)), initvals(conn.second));
					}
				}

				{
					int unique_bit_id_counter = 0;
					dict<RTLIL::SigBit, int> unique_bit_id;
					unique_bit_id[RTLIL::State::S0] = unique_bit_id_counter++;
					unique_bit_id[RTLIL::State::S1] = unique_bit_id_counter++;
					unique_bit_id[RTLIL::State::Sx] = unique_bit_id_counter++;
					unique_bit_id[RTLIL::State::Sz] = unique_bit_id_counter++;

					for (auto &conn : cell->connections())
						if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONNMAP_%s_", log_id(conn.first))) != 0) {
							for (auto &bit : sigmap(conn.second))
								if (unique_bit_id.count(bit) == 0)
									unique_bit_id[bit] = unique_bit_id_counter++;
						}

					// Find highest bit set
					int bits = 0;
					for (int i = 0; i < 32; i++)
						if (((unique_bit_id_counter-1) & (1 << i)) != 0)
							bits = i;
					// Increment index by one to get number of bits
					bits++;
					if (tpl->avail_parameters.count(ID::_TECHMAP_BITS_CONNMAP_))
						parameters[ID::_TECHMAP_BITS_CONNMAP_] = bits;

					for (auto &conn : cell->connections())
						if (tpl->avail_parameters.count(stringf("\\_TECHMAP_CONNMAP_%s_", log_id(conn.first))) != 0) {
							RTLIL::Const value;
							for (auto &bit : sigmap(conn.second)) {
								int val = unique_bit_id.at(bit);
								for (int i = 0; i < bits; i++) {
									value.bits().push_back((val & 1) != 0 ? State::S1 : State::S0);
									val = val >> 1;
								}
							}
							parameters.emplace(stringf("\\_TECHMAP_CONNMAP_%s_", log_id(conn.first)), value);
						}
				}

				if (0) {
			use_wrapper_tpl:;
					// do not register techmap_wrap modules with techmap_cache
				} else {
					std::pair<IdString, dict<IdString, RTLIL::Const>> key(tpl_name, parameters);
					auto it = techmap_cache.find(key);
					if (it != techmap_cache.end()) {
						tpl = it->second;
					} else {
						if (parameters.size() != 0) {
							mkdebug.on();
							derived_name = tpl->derive(map, parameters);
							tpl = map->module(derived_name);
							log_continue = true;
						}
						techmap_cache.emplace(std::move(key), tpl);
					}
				}

				RTLIL::Module *constmapped_tpl = map->module(constmap_tpl_name(sigmap, tpl, cell, false));
				if (constmapped_tpl != nullptr)
					tpl = constmapped_tpl;

				if (techmap_do_cache.count(tpl) == 0)
				{
					bool keep_running = true;
					techmap_do_cache[tpl] = true;

					pool<IdString> techmap_wire_names;

					while (keep_running)
					{
						TechmapWires twd = techmap_find_special_wires(tpl);
						keep_running = false;

						for (auto &it : twd)
							techmap_wire_names.insert(it.first);

						for (auto &it : twd) {
							if (!it.first.ends_with("_TECHMAP_FAIL_"))
								continue;
							for (const TechmapWireData &elem : it.second) {
								RTLIL::SigSpec value = elem.value;
								if (value.is_fully_const() && value.as_bool()) {
									log("Not using module `%s' from techmap as it contains a %s marker wire with non-zero value %s.\n",
											derived_name.c_str(), log_id(elem.wire->name), log_signal(value));
									techmap_do_cache[tpl] = false;
								}
							}
						}

						if (!techmap_do_cache[tpl])
							break;

						for (auto &it : twd)
						{
							if (!it.first.contains("_TECHMAP_DO_") || it.second.empty())
								continue;

							auto &data = it.second.front();

							if (!data.value.is_fully_const())
								log_error("Techmap yielded config wire %s with non-const value %s.\n", log_id(data.wire->name), log_signal(data.value));

							techmap_wire_names.erase(it.first);

							const char *p = data.wire->name.c_str();
							const char *q = strrchr(p+1, '.');
							q = q ? q+1 : p+1;

							std::string cmd_string = data.value.as_const().decode_string();

						restart_eval_cmd_string:
							if (cmd_string.rfind("CONSTMAP; ", 0) == 0)
							{
								cmd_string = cmd_string.substr(strlen("CONSTMAP; "));

								log("Analyzing pattern of constant bits for this cell:\n");
								IdString new_tpl_name = constmap_tpl_name(sigmap, tpl, cell, true);
								log("Creating constmapped module `%s'.\n", log_id(new_tpl_name));
								log_assert(map->module(new_tpl_name) == nullptr);

								RTLIL::Module *new_tpl = map->addModule(new_tpl_name);
								tpl->cloneInto(new_tpl);

								techmap_do_cache.erase(tpl);
								techmap_do_cache[new_tpl] = true;
								tpl = new_tpl;

								dict<RTLIL::SigBit, RTLIL::SigBit> port_new2old_map;
								dict<RTLIL::SigBit, RTLIL::SigBit> port_connmap;
								dict<RTLIL::SigBit, RTLIL::SigBit> cellbits_to_tplbits;

								for (auto wire : tpl->wires().to_vector())
								{
									if (!wire->port_input || wire->port_output)
										continue;

									IdString port_name = wire->name;
									tpl->rename(wire, NEW_ID);

									RTLIL::Wire *new_wire = tpl->addWire(port_name, wire);
									wire->port_input = false;
									wire->port_id = 0;

									for (int i = 0; i < wire->width; i++) {
										port_new2old_map.emplace(RTLIL::SigBit(new_wire, i), RTLIL::SigBit(wire, i));
										port_connmap.emplace(RTLIL::SigBit(wire, i), RTLIL::SigBit(new_wire, i));
									}
								}

								// Handle outputs first, as these cannot be remapped.
								for (auto &conn : cell->connections())
								{
									Wire *twire = tpl->wire(conn.first);
									if (!twire->port_output)
										continue;

									for (int i = 0; i < GetSize(conn.second); i++) {
										RTLIL::SigBit bit = sigmap(conn.second[i]);
										RTLIL::SigBit tplbit(twire, i);
										cellbits_to_tplbits[bit] = tplbit;
									}
								}

								// Now handle inputs, remapping as necessary.
								for (auto &conn : cell->connections())
								{
									Wire *twire = tpl->wire(conn.first);
									if (twire->port_output)
										continue;

									for (int i = 0; i < GetSize(conn.second); i++)
									{
										RTLIL::SigBit bit = sigmap(conn.second[i]);
										RTLIL::SigBit tplbit(twire, i);

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
								}

								RTLIL::SigSig port_conn;
								for (auto &it : port_connmap) {
									port_conn.first.append(it.first);
									port_conn.second.append(it.second);
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
							while (tpl->wire(new_name) != nullptr)
								new_name += "_";
							tpl->rename(data.wire->name, new_name);

							keep_running = true;
							break;
						}
					}

					TechmapWires twd = techmap_find_special_wires(tpl);
					for (auto &it : twd) {
						if (!it.first.ends_with("_TECHMAP_FAIL_") && (!it.first.begins_with("\\_TECHMAP_REMOVEINIT_") || !it.first.ends_with("_")) && !it.first.contains("_TECHMAP_DO_") && !it.first.contains("_TECHMAP_DONE_"))
							log_error("Techmap yielded unknown config wire %s.\n", log_id(it.first));
						if (techmap_do_cache[tpl])
							for (auto &it2 : it.second)
								if (!it2.value.is_fully_const())
									log_error("Techmap yielded config wire %s with non-const value %s.\n", log_id(it2.wire->name), log_signal(it2.value));
						techmap_wire_names.erase(it.first);
					}

					for (auto &it : techmap_wire_names)
						log_error("Techmap special wire %s disappeared. This is considered a fatal error.\n", log_id(it));

					if (recursive_mode) {
						if (log_continue) {
							log_header(design, "Continuing TECHMAP pass.\n");
							log_continue = false;
							mkdebug.off();
						}
						while (techmap_module(map, tpl, map, handled_cells, celltypeMap, true)) { }
					}
				}

				if (techmap_do_cache.at(tpl) == false)
					continue;

				if (log_continue) {
					log_header(design, "Continuing TECHMAP pass.\n");
					log_continue = false;
					mkdebug.off();
				}

				TechmapWires twd = techmap_find_special_wires(tpl);
				for (auto &it : twd) {
					if (it.first.begins_with("\\_TECHMAP_REMOVEINIT_")) {
						for (auto &it2 : it.second) {
							auto val = it2.value.as_const();
							auto wirename = RTLIL::escape_id(it.first.substr(21, it.first.size() - 21 - 1));
							auto it = cell->connections().find(wirename);
							if (it != cell->connections().end()) {
								auto sig = sigmap(it->second);
								for (int i = 0; i < sig.size(); i++)
									if (val[i] == State::S1)
										initvals.remove_init(sig[i]);
							}
						}
					}
				}

				if (extern_mode && !in_recursion)
				{
					std::string m_name = stringf("$extern:%s", log_id(tpl));

					if (!design->module(m_name))
					{
						RTLIL::Module *m = design->addModule(m_name);
						tpl->cloneInto(m);

						for (auto cell : m->cells()) {
							if (cell->type.begins_with("\\$"))
								cell->type = cell->type.substr(1);
						}

						module_queue.insert(m);
					}

					log_debug("%s %s.%s to imported %s.\n", mapmsg_prefix.c_str(), log_id(module), log_id(cell), log_id(m_name));
					cell->type = m_name;
					cell->parameters.clear();
				}
				else
				{
					auto msg = stringf("Using template %s for cells of type %s.", log_id(tpl), log_id(cell->type));
					if (!log_msg_cache.count(msg)) {
						log_msg_cache.insert(msg);
						log("%s\n", msg.c_str());
					}
					log_debug("%s %s.%s (%s) using %s.\n", mapmsg_prefix.c_str(), log_id(module), log_id(cell), log_id(cell->type), log_id(tpl));
					techmap_module_worker(design, module, cell, tpl);
					cell = nullptr;
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
			mkdebug.off();
		}

		return did_something;
	}
};

struct TechmapPass : public Pass {
	TechmapPass() : Pass("techmap", "generic technology mapper") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    techmap [-map filename] [selection]\n");
		log("\n");
		log("This pass implements a very simple technology mapper that replaces cells in\n");
		log("the design with implementations given in form of a Verilog or RTLIL source\n");
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
		log("        only run the specified number of iterations on each module.\n");
		log("        default: unlimited\n");
		log("\n");
		log("    -recursive\n");
		log("        instead of the iterative breadth-first algorithm use a recursive\n");
		log("        depth-first algorithm. both methods should yield equivalent results,\n");
		log("        but may differ in performance.\n");
		log("\n");
		log("    -autoproc\n");
		log("        Automatically call \"proc\" on implementations that contain processes.\n");
		log("\n");
		log("    -wb\n");
		log("        Ignore the 'whitebox' attribute on cell implementations.\n");
		log("\n");
		log("    -assert\n");
		log("        this option will cause techmap to exit with an error if it can't map\n");
		log("        a selected cell. only cell types that end on an underscore are accepted\n");
		log("        as final cell types by this mode.\n");
		log("\n");
		log("    -D <define>, -I <incdir>\n");
		log("        this options are passed as-is to the Verilog frontend for loading the\n");
		log("        map file. Note that the Verilog frontend is also called with the\n");
		log("        '-nooverwrite' option set.\n");
		log("\n");
		log("When a module in the map file has the 'techmap_celltype' attribute set, it will\n");
		log("match cells with a type that match the text value of this attribute. Otherwise\n");
		log("the module name will be used to match the cell.  Multiple space-separated cell\n");
		log("types can be listed, and wildcards using [] will be expanded (ie.\n");
		log("\"$_DFF_[PN]_\" is the same as \"$_DFF_P_ $_DFF_N_\").\n");
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
		log("When a port on a module in the map file has the 'techmap_autopurge' attribute\n");
		log("set, and that port is not connected in the instantiation that is mapped, then\n");
		log("a cell port connected only to such wires will be omitted in the mapped version\n");
		log("of the circuit.\n");
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
		log("    _TECHMAP_REMOVEINIT_<port-name>_\n");
		log("        When this wire is set to a constant value, the init attribute of the\n");
		log("        wire(s) connected to this port will be consumed.  This wire must have\n");
		log("        the same width as the given port, and for every bit that is set to 1 in\n");
		log("        the value, the corresponding init attribute bit will be changed to 1'bx.\n");
		log("        If all bits of an init attribute are left as x, it will be removed.\n");
		log("\n");
		log("In addition to this special wires, techmap also supports special parameters in\n");
		log("modules in the map file:\n");
		log("\n");
		log("    _TECHMAP_CELLTYPE_\n");
		log("        When a parameter with this name exists, it will be set to the type name\n");
		log("        of the cell that matches the module.\n");
		log("\n");
		log("    _TECHMAP_CELLNAME_\n");
		log("        When a parameter with this name exists, it will be set to the name\n");
		log("        of the cell that matches the module.\n");
		log("\n");
		log("    _TECHMAP_CONSTMSK_<port-name>_\n");
		log("    _TECHMAP_CONSTVAL_<port-name>_\n");
		log("        When this pair of parameters is available in a module for a port, then\n");
		log("        former has a 1-bit for each constant input bit and the latter has the\n");
		log("        value for this bit. The unused bits of the latter are set to undef (x).\n");
		log("\n");
		log("    _TECHMAP_WIREINIT_<port-name>_\n");
		log("        When a parameter with this name exists, it will be set to the initial\n");
		log("        value of the wire(s) connected to the given port, as specified by the\n");
		log("        init attribute. If the attribute doesn't exist, x will be filled for the\n");
		log("        missing bits.  To remove the init attribute bits used, use the\n");
		log("        _TECHMAP_REMOVEINIT_*_ wires.\n");
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
		log("and attributes of the cell that is being replaced.\n");
		log("A cell with a name of the form `_TECHMAP_REPLACE_.<suffix>` in the map file will\n");
		log("be named thus but with the `_TECHMAP_REPLACE_' prefix substituted with the name\n");
		log("of the cell being replaced.\n");
		log("Similarly, a wire named in the form `_TECHMAP_REPLACE_.<suffix>` will cause a\n");
		log("new wire alias to be created and named as above but with the `_TECHMAP_REPLACE_'\n");
		log("prefix also substituted.\n");
		log("\n");
		log("A cell with the type _TECHMAP_PLACEHOLDER_ in the map file will have its type\n");
		log("changed to the content of the techmap_chtype attribute. This allows for choosing\n");
		log("the cell type dynamically.\n");
		log("\n");
		log("See 'help extract' for a pass that does the opposite thing.\n");
		log("\n");
		log("See 'help flatten' for a pass that does flatten the design (which is\n");
		log("essentially techmap but using the design itself as map library).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing TECHMAP pass (map to technology primitives).\n");
		log_push();

		TechmapWorker worker;
		simplemap_get_mappers(worker.simplemap_mappers);

		std::vector<std::string> map_files;
		std::string verilog_frontend = "verilog -nooverwrite -noblackbox";
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
			if (args[argidx] == "-wb") {
				worker.ignore_wb = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Design *map = new RTLIL::Design;
		if (map_files.empty()) {
			Frontend::frontend_call(map, nullptr, "+/techmap.v", verilog_frontend);
		} else {
			for (auto &fn : map_files)
				if (fn.compare(0, 1, "%") == 0) {
					if (!saved_designs.count(fn.substr(1))) {
						delete map;
						log_cmd_error("Can't open saved design `%s'.\n", fn.c_str()+1);
					}
					for (auto mod : saved_designs.at(fn.substr(1))->modules())
						if (!map->module(mod->name))
							map->add(mod->clone());
				} else {
					Frontend::frontend_call(map, nullptr, fn, (fn.size() > 3 && fn.compare(fn.size()-3, std::string::npos, ".il") == 0 ? "rtlil" : verilog_frontend));
				}
		}

		log_header(design, "Continuing TECHMAP pass.\n");

		dict<IdString, pool<IdString>> celltypeMap;
		for (auto module : map->modules()) {
			if (module->attributes.count(ID::techmap_celltype) && !module->attributes.at(ID::techmap_celltype).empty()) {
				char *p = strdup(module->attributes.at(ID::techmap_celltype).decode_string().c_str());
				for (char *q = strtok(p, " \t\r\n"); q; q = strtok(nullptr, " \t\r\n")) {
					std::vector<std::string> queue;
					queue.push_back(q);
					while (!queue.empty()) {
						std::string name = queue.back();
						queue.pop_back();
						auto pos = name.find('[');
						if (pos == std::string::npos) {
							// No further expansion.
							celltypeMap[RTLIL::escape_id(name)].insert(module->name);
						} else {
							// Expand [] in this name.
							auto epos = name.find(']', pos);
							if (epos == std::string::npos)
								log_error("Malformed techmap_celltype pattern %s\n", q);
							for (size_t i = pos + 1; i < epos; i++) {
								queue.push_back(name.substr(0, pos) + name[i] + name.substr(epos + 1, std::string::npos));
							}
						}
					}
				}
				free(p);
			} else {
				IdString module_name = module->name.begins_with("\\$") ?
						module->name.substr(1) : module->name.str();
				celltypeMap[module_name].insert(module->name);
			}
		}
		log_debug("Cell type mappings to use:\n");
		for (auto &i : celltypeMap) {
			i.second.sort(RTLIL::sort_by_id_str());
			std::string maps = "";
			for (auto &map : i.second)
				maps += stringf(" %s", log_id(map));
			log_debug("    %s:%s\n", log_id(i.first), maps.c_str());
		}
		log_debug("\n");

		for (auto module : design->modules())
			worker.module_queue.insert(module);

		while (!worker.module_queue.empty())
		{
			RTLIL::Module *module = *worker.module_queue.begin();
			worker.module_queue.erase(module);

			int module_max_iter = max_iter;
			bool did_something = true;
			pool<RTLIL::Cell*> handled_cells;
			while (did_something) {
				did_something = false;
				if (worker.techmap_module(design, module, map, handled_cells, celltypeMap, false))
					did_something = true;
				if (did_something)
					module->check();
				if (module_max_iter > 0 && --module_max_iter == 0)
					break;
			}
		}

		log("No more expansions possible.\n");
		delete map;

		log_pop();
	}
} TechmapPass;

PRIVATE_NAMESPACE_END
