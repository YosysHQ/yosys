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
#include "passes/hierarchy/util/generate.h"

PRIVATE_NAMESPACE_BEGIN
USING_YOSYS_NAMESPACE
using namespace Hierarchy;

static void generate_cell(const char* p, std::vector<std::string>& cells) {
	log("Celltype: %s\n", p);
	cells.push_back(RTLIL::unescape_id(string(p)));
}
static void parse_one(const char* p, std::vector<std::string>& cells, std::vector<generate_port_decl_t>& ports) {
	generate_port_decl_t decl;
	if (p[0] == 'i' && p[1] == 'o') {
		decl.input = true;
		decl.output = true;
		p += 2;
	} else if (*p == 'i') {
		decl.input = true;
		decl.output = false;
		p++;
	} else if (*p == 'o') {
		decl.input = false;
		decl.output = true;
		p++;
	} else {
		return generate_cell(p, cells);
	}
	if (*p == '@') {
		char *endptr;
		decl.index = strtol(++p, &endptr, 10);
		if (decl.index < 1)
			return generate_cell(p, cells);
		p = endptr;
	} else
		decl.index = 0;
	if (*(p++) != ':')
		return generate_cell(p, cells);
	if (*p == 0)
		return generate_cell(p, cells);
	decl.portname = p;
	log("Port declaration: %s", decl.input ? decl.output ? "inout" : "input" : "output");
	if (decl.index >= 1)
		log(" [at position %d]", decl.index);
	log(" %s\n", decl.portname);
	ports.push_back(decl);
	return;
}

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {
	void Generator::generate(Design* design) {
		std::set<RTLIL::IdString> found_celltypes;

		for (auto mod : design->modules())
		for (auto cell : mod->cells())
		{
			if (design->module(cell->type) != nullptr)
				continue;
			if (cell->type.begins_with("$") && !cell->type.begins_with("$__"))
				continue;
			for (auto &pattern : cells)
				if (patmatch(pattern.c_str(), RTLIL::unescape_id(cell->type).c_str()))
					found_celltypes.insert(cell->type);
		}

		for (auto &celltype : found_celltypes)
		{
			std::set<RTLIL::IdString> portnames;
			std::set<RTLIL::IdString> parameters;
			std::map<RTLIL::IdString, int> portwidths;
			log("Generate module for cell type %s:\n", celltype);

			for (auto mod : design->modules())
			for (auto cell : mod->cells())
				if (cell->type == celltype) {
					for (auto &conn : cell->connections()) {
						if (conn.first[0] != '$')
							portnames.insert(conn.first);
						portwidths[conn.first] = max(portwidths[conn.first], conn.second.size());
					}
					for (auto &para : cell->parameters)
						parameters.insert(para.first);
				}

			for (auto &decl : ports)
				if (decl.index > 0)
					portnames.insert(decl.portname);

			std::set<int> indices;
			for (int i = 0; i < int(portnames.size()); i++)
				indices.insert(i+1);

			for (auto &decl : ports)
				if (decl.index > 0) {
					portwidths[decl.portname] = max(portwidths[decl.portname], 1);
					portwidths[decl.portname] = max(portwidths[decl.portname], portwidths[stringf("$%d", decl.index)]);
					log("  port %d: %s [%d:0] %s\n", decl.index, decl.input ? decl.output ? "inout" : "input" : "output", portwidths[decl.portname]-1, RTLIL::id2cstr(decl.portname));
					if (indices.count(decl.index) > ports.size())
						log_error("Port index (%d) exceeds number of found ports (%d).\n", decl.index, int(ports.size()));
					if (indices.count(decl.index) == 0)
						log_error("Conflict on port index %d.\n", decl.index);
					indices.erase(decl.index);
					portnames.erase(decl.portname);
					ports[decl.index-1] = decl;
				}

			while (portnames.size() > 0) {
				RTLIL::IdString portname = *portnames.begin();
				for (auto &decl : ports)
					if (decl.index == 0 && patmatch(decl.portname.c_str(), RTLIL::unescape_id(portname).c_str())) {
						generate_port_decl_t d = decl;
						d.portname = portname.str();
						d.index = *indices.begin();
						log_assert(!indices.empty());
						indices.erase(d.index);
						ports[d.index-1] = d;
						portwidths[d.portname] = max(portwidths[d.portname], 1);
						log("  port %d: %s [%d:0] %s\n", d.index, d.input ? d.output ? "inout" : "input" : "output", portwidths[d.portname]-1, RTLIL::id2cstr(d.portname));
						goto found_matching_decl;
					}
				log_error("Can't match port %s.\n", RTLIL::id2cstr(portname));
			found_matching_decl:;
				portnames.erase(portname);
			}

			log_assert(indices.empty());

			RTLIL::Module *mod = new RTLIL::Module;
			mod->name = celltype;
			mod->attributes[ID::blackbox] = RTLIL::Const(1);
			design->add(mod);

			for (auto &decl : ports) {
				RTLIL::Wire *wire = mod->addWire(decl.portname, portwidths.at(decl.portname));
				wire->port_id = decl.index;
				wire->port_input = decl.input;
				wire->port_output = decl.output;
			}

			mod->fixup_ports();

			for (auto &para : parameters)
				log("  ignoring parameter %s.\n", RTLIL::id2cstr(para));

			log("  module %s created.\n", RTLIL::id2cstr(mod->name));
		}
	}
	void Generator::parse_arg(const char* p) {
		parse_one(p, cells, ports);
	}

};
YOSYS_NAMESPACE_END