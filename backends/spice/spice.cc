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

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static string spice_id2str(IdString id)
{
	static const char *escape_chars = "$\\[]()<>=";
	string s = RTLIL::unescape_id(id);

	for (auto &ch : s)
		if (strchr(escape_chars, ch) != nullptr) ch = '_';

	return s;
}

static string spice_id2str(IdString id, bool use_inames, idict<IdString, 1> &inums)
{
	if (!use_inames && *id.c_str() == '$')
		return stringf("%d", inums(id));
	return spice_id2str(id);
}

static void print_spice_net(std::ostream &f, RTLIL::SigBit s, std::string &neg, std::string &pos, std::string &ncpf, int &nc_counter, bool use_inames, idict<IdString, 1> &inums)
{
	if (s.wire) {
		if (s.wire->port_id)
			use_inames = true;
		if (s.wire->width > 1)
			f << stringf(" %s.%d", spice_id2str(s.wire->name, use_inames, inums).c_str(), s.offset);
		else
			f << stringf(" %s", spice_id2str(s.wire->name, use_inames, inums).c_str());
	} else {
		if (s == RTLIL::State::S0)
			f << stringf(" %s", neg.c_str());
		else if (s == RTLIL::State::S1)
			f << stringf(" %s", pos.c_str());
		else
			f << stringf(" %s%d", ncpf.c_str(), nc_counter++);
	}
}

static void print_spice_module(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, std::string &neg, std::string &pos, std::string &ncpf, bool big_endian, bool use_inames)
{
	SigMap sigmap(module);
	idict<IdString, 1> inums;
	int cell_counter = 0, conn_counter = 0, nc_counter = 0;

	for (auto &cell_it : module->cells_)
	{
		RTLIL::Cell *cell = cell_it.second;
		f << stringf("X%d", cell_counter++);

		std::vector<RTLIL::SigSpec> port_sigs;

		if (design->modules_.count(cell->type) == 0)
		{
			log_warning("no (blackbox) module for cell type `%s' (%s.%s) found! Guessing order of ports.\n",
					log_id(cell->type), log_id(module), log_id(cell));
			for (auto &conn : cell->connections()) {
				RTLIL::SigSpec sig = sigmap(conn.second);
				port_sigs.push_back(sig);
			}
		}
		else
		{
			RTLIL::Module *mod = design->modules_.at(cell->type);

			std::vector<RTLIL::Wire*> ports;
			for (auto wire_it : mod->wires_) {
				RTLIL::Wire *wire = wire_it.second;
				if (wire->port_id == 0)
					continue;
				while (int(ports.size()) < wire->port_id)
					ports.push_back(NULL);
				ports.at(wire->port_id-1) = wire;
			}

			for (RTLIL::Wire *wire : ports) {
				log_assert(wire != NULL);
				RTLIL::SigSpec sig(RTLIL::State::Sz, wire->width);
				if (cell->hasPort(wire->name)) {
					sig = sigmap(cell->getPort(wire->name));
					sig.extend_u0(wire->width, false);
				}
				port_sigs.push_back(sig);
			}
		}

		for (auto &sig : port_sigs) {
			for (int i = 0; i < sig.size(); i++) {
				RTLIL::SigSpec s = sig.extract(big_endian ? sig.size() - 1 - i : i, 1);
				print_spice_net(f, s, neg, pos, ncpf, nc_counter, use_inames, inums);
			}
		}

		f << stringf(" %s\n", spice_id2str(cell->type).c_str());
	}

	for (auto &conn : module->connections())
	for (int i = 0; i < conn.first.size(); i++) {
		f << stringf("V%d", conn_counter++);
		print_spice_net(f, conn.first.extract(i, 1), neg, pos, ncpf, nc_counter, use_inames, inums);
		print_spice_net(f, conn.second.extract(i, 1), neg, pos, ncpf, nc_counter, use_inames, inums);
		f << stringf(" DC 0\n");
	}
}

struct SpiceBackend : public Backend {
	SpiceBackend() : Backend("spice", "write design to SPICE netlist file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_spice [options] [filename]\n");
		log("\n");
		log("Write the current design to an SPICE netlist file.\n");
		log("\n");
		log("    -big_endian\n");
		log("        generate multi-bit ports in MSB first order\n");
		log("        (default is LSB first)\n");
		log("\n");
		log("    -neg net_name\n");
		log("        set the net name for constant 0 (default: Vss)\n");
		log("\n");
		log("    -pos net_name\n");
		log("        set the net name for constant 1 (default: Vdd)\n");
		log("\n");
		log("    -nc_prefix\n");
		log("        prefix for not-connected nets (default: _NC)\n");
		log("\n");
		log("    -inames\n");
		log("        include names of internal ($-prefixed) nets in outputs\n");
		log("        (default is to use net numbers instead)\n");
		log("\n");
		log("    -top top_module\n");
		log("        set the specified module as design top module\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string top_module_name;
		RTLIL::Module *top_module = NULL;
		bool big_endian = false, use_inames = false;
		std::string neg = "Vss", pos = "Vdd", ncpf = "_NC";

		log_header(design, "Executing SPICE backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-big_endian") {
				big_endian = true;
				continue;
			}
			if (args[argidx] == "-inames") {
				use_inames = true;
				continue;
			}
			if (args[argidx] == "-neg" && argidx+1 < args.size()) {
				neg = args[++argidx];
				continue;
			}
			if (args[argidx] == "-pos" && argidx+1 < args.size()) {
				pos = args[++argidx];
				continue;
			}
			if (args[argidx] == "-nc_prefix" && argidx+1 < args.size()) {
				ncpf = args[++argidx];
				continue;
			}
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module_name = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		if (top_module_name.empty())
			for (auto & mod_it:design->modules_)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_module_name = mod_it.first.str();

		*f << stringf("* SPICE netlist generated by %s\n", yosys_version_str);
		*f << stringf("\n");

		for (auto module_it : design->modules_)
		{
			RTLIL::Module *module = module_it.second;
			if (module->get_blackbox_attribute())
				continue;

			if (module->processes.size() != 0)
				log_error("Found unmapped processes in module %s: unmapped processes are not supported in SPICE backend!\n", log_id(module));
			if (module->memories.size() != 0)
				log_error("Found unmapped memories in module %s: unmapped memories are not supported in SPICE backend!\n", log_id(module));

			if (module->name == RTLIL::escape_id(top_module_name)) {
				top_module = module;
				continue;
			}

			std::vector<RTLIL::Wire*> ports;
			for (auto wire_it : module->wires_) {
				RTLIL::Wire *wire = wire_it.second;
				if (wire->port_id == 0)
					continue;
				while (int(ports.size()) < wire->port_id)
					ports.push_back(NULL);
				ports.at(wire->port_id-1) = wire;
			}

			*f << stringf(".SUBCKT %s", spice_id2str(module->name).c_str());
			for (RTLIL::Wire *wire : ports) {
				log_assert(wire != NULL);
				if (wire->width > 1) {
					for (int i = 0; i < wire->width; i++)
						*f << stringf(" %s.%d", spice_id2str(wire->name).c_str(), big_endian ? wire->width - 1 - i : i);
				} else
					*f << stringf(" %s", spice_id2str(wire->name).c_str());
			}
			*f << stringf("\n");
			print_spice_module(*f, module, design, neg, pos, ncpf, big_endian, use_inames);
			*f << stringf(".ENDS %s\n\n", spice_id2str(module->name).c_str());
		}

		if (!top_module_name.empty()) {
			if (top_module == NULL)
				log_error("Can't find top module `%s'!\n", top_module_name.c_str());
			print_spice_module(*f, top_module, design, neg, pos, ncpf, big_endian, use_inames);
			*f << stringf("\n");
		}

		*f << stringf("************************\n");
		*f << stringf("* end of SPICE netlist *\n");
		*f << stringf("************************\n");
		*f << stringf("\n");
	}
} SpiceBackend;

PRIVATE_NAMESPACE_END
