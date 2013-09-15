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

// [[CITE]] Berkeley Logic Interchange Format (BLIF)
// University of California. Berkeley. July 28, 1992
// http://www.ece.cmu.edu/~ee760/760docs/blif.pdf

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>
#include <assert.h>

struct BlifDumper
{
	FILE *f;
	RTLIL::Module *module;
	RTLIL::Design *design;
	CellTypes ct;

	BlifDumper(FILE *f, RTLIL::Module *module, RTLIL::Design *design) : f(f), module(module), design(design), ct(design)
	{
	}

	std::vector<std::string> cstr_buf;

	const char *cstr(RTLIL::IdString id)
	{
		std::string str = RTLIL::unescape_id(id);
		for (size_t i = 0; i < str.size(); i++)
			if (str[i] == '#' || str[i] == '=')
				str[i] = '?';
		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	const char *cstr(RTLIL::SigSpec sig)
	{
		sig.optimize();
		log_assert(sig.width == 1);

		if (sig.chunks.at(0).wire == NULL)
			return sig.chunks.at(0).data.bits.at(0) == RTLIL::State::S1 ?  "$true" : "$false";

		std::string str = RTLIL::unescape_id(sig.chunks.at(0).wire->name);
		for (size_t i = 0; i < str.size(); i++)
			if (str[i] == '#' || str[i] == '=')
				str[i] = '?';

		if (sig.chunks.at(0).wire->width != 1)
			str += stringf("[%d]", sig.chunks.at(0).offset);

		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	void dump()
	{
		fprintf(f, "\n");
		fprintf(f, ".model %s\n", cstr(module->name));

		std::map<int, RTLIL::Wire*> inputs, outputs;

		for (auto &wire_it : module->wires) {
			RTLIL::Wire *wire = wire_it.second;
			if (wire->port_input)
				inputs[wire->port_id] = wire;
			if (wire->port_output)
				outputs[wire->port_id] = wire;
		}

		fprintf(f, ".inputs");
		for (auto &it : inputs) {
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				fprintf(f, " %s", cstr(RTLIL::SigSpec(wire, 1, i)));
		}
		fprintf(f, "\n");

		fprintf(f, ".outputs");
		for (auto &it : outputs) {
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				fprintf(f, " %s", cstr(RTLIL::SigSpec(wire, 1, i)));
		}
		fprintf(f, "\n");

		fprintf(f, ".names $false\n");
		fprintf(f, ".names $true\n1\n");

		for (auto &cell_it : module->cells)
		{
			RTLIL::Cell *cell = cell_it.second;

			if (cell->type == "$_INV_") {
				fprintf(f, ".names %s %s\n0 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (cell->type == "$_AND_") {
				fprintf(f, ".names %s %s %s\n11 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\B")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (cell->type == "$_OR_") {
				fprintf(f, ".names %s %s %s\n1- 1\n-1 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\B")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (cell->type == "$_XOR_") {
				fprintf(f, ".names %s %s %s\n10 1\n01 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\B")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (cell->type == "$_MUX_") {
				fprintf(f, ".names %s %s %s %s\n1-0 1\n-11 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\B")),
						cstr(cell->connections.at("\\S")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (cell->type == "$_DFF_N_") {
				fprintf(f, ".latch %s %s fe %s\n",
						cstr(cell->connections.at("\\D")), cstr(cell->connections.at("\\Q")), cstr(cell->connections.at("\\C")));
				continue;
			}

			if (cell->type == "$_DFF_P_") {
				fprintf(f, ".latch %s %s re %s\n",
						cstr(cell->connections.at("\\D")), cstr(cell->connections.at("\\Q")), cstr(cell->connections.at("\\C")));
				continue;
			}

			fprintf(f, ".subckt %s", cstr(cell->type));
			for (auto &conn : cell->connections)
			for (int i = 0; i < conn.second.width; i++) {
				if (conn.second.width == 1)
					fprintf(f, " %s", cstr(conn.first));
				else
					fprintf(f, " %s[%d]", cstr(conn.first), i);
				fprintf(f, "=%s", cstr(conn.second.extract(i, 1)));
			}
			fprintf(f, "\n");
		}

		for (auto &conn : module->connections)
		for (int i = 0; i < conn.first.width; i++)
			fprintf(f, ".names %s %s\n1 1\n", cstr(conn.second.extract(i, 1)), cstr(conn.first.extract(i, 1)));

		fprintf(f, ".end\n");
	}

	static void dump(FILE *f, RTLIL::Module *module, RTLIL::Design *design)
	{
		BlifDumper dumper(f, module, design);
		dumper.dump();
	}
};

struct BlifBackend : public Backend {
	BlifBackend() : Backend("blif", "write design to BLIF file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_blif [options] [filename]\n");
		log("\n");
		log("Write the current design to an BLIF file.\n");
		log("\n");
		log("    -top top_module\n");
		log("        set the specified module as design top module\n");
		log("\n");
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_module_name;

		log_header("Executing BLIF backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module_name = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		std::vector<RTLIL::Module*> mod_list;

		for (auto module_it : design->modules)
		{
			RTLIL::Module *module = module_it.second;
			if ((module->attributes.count("\\placeholder") > 0) > 0)
				continue;

			if (module->processes.size() != 0)
				log_error("Found unmapped processes in module %s: unmapped processes are not supported in BLIF backend!\n", RTLIL::id2cstr(module->name));
			if (module->memories.size() != 0)
				log_error("Found munmapped emories in module %s: unmapped memories are not supported in BLIF backend!\n", RTLIL::id2cstr(module->name));

			if (module->name == RTLIL::escape_id(top_module_name)) {
				BlifDumper::dump(f, module, design);
				top_module_name.clear();
				continue;
			}

			mod_list.push_back(module);
		}

		if (!top_module_name.empty())
			log_error("Can't find top module `%s'!\n", top_module_name.c_str());

		for (auto module : mod_list)
			BlifDumper::dump(f, module, design);
	}
} BlifBackend;

