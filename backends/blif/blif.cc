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

struct BlifDumperConfig
{
	bool icells_mode;
	bool conn_mode;
	bool impltf_mode;
	bool gates_mode;
	bool param_mode;

	std::string buf_type, buf_in, buf_out;
	std::string true_type, true_out, false_type, false_out;

	BlifDumperConfig() : icells_mode(false), conn_mode(false), impltf_mode(false), gates_mode(false), param_mode(false) { }
};

struct BlifDumper
{
	FILE *f;
	RTLIL::Module *module;
	RTLIL::Design *design;
	BlifDumperConfig *config;
	CellTypes ct;

	BlifDumper(FILE *f, RTLIL::Module *module, RTLIL::Design *design, BlifDumperConfig *config) :
			f(f), module(module), design(design), config(config), ct(design)
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
		log_assert(sig.size() == 1);

		if (sig.chunks().at(0).wire == NULL)
			return sig.chunks().at(0).data.bits.at(0) == RTLIL::State::S1 ?  "$true" : "$false";

		std::string str = RTLIL::unescape_id(sig.chunks().at(0).wire->name);
		for (size_t i = 0; i < str.size(); i++)
			if (str[i] == '#' || str[i] == '=')
				str[i] = '?';

		if (sig.chunks().at(0).wire->width != 1)
			str += stringf("[%d]", sig.chunks().at(0).offset);

		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	const char *subckt_or_gate(std::string cell_type)
	{
		if (!config->gates_mode)
			return "subckt";
		if (!design->modules.count(RTLIL::escape_id(cell_type)))
			return "gate";
		if (design->modules.at(RTLIL::escape_id(cell_type))->get_bool_attribute("\\blackbox"))
			return "gate";
		return "subckt";
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
				fprintf(f, " %s", cstr(RTLIL::SigSpec::grml(wire, i)));
		}
		fprintf(f, "\n");

		fprintf(f, ".outputs");
		for (auto &it : outputs) {
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				fprintf(f, " %s", cstr(RTLIL::SigSpec::grml(wire, i)));
		}
		fprintf(f, "\n");

		if (!config->impltf_mode) {
			if (!config->false_type.empty())
				fprintf(f, ".%s %s %s=$false\n", subckt_or_gate(config->false_type),
						config->false_type.c_str(), config->false_out.c_str());
			else
				fprintf(f, ".names $false\n");
			if (!config->true_type.empty())
				fprintf(f, ".%s %s %s=$true\n", subckt_or_gate(config->true_type),
						config->true_type.c_str(), config->true_out.c_str());
			else
				fprintf(f, ".names $true\n1\n");
		}

		for (auto &cell_it : module->cells)
		{
			RTLIL::Cell *cell = cell_it.second;

			if (!config->icells_mode && cell->type == "$_INV_") {
				fprintf(f, ".names %s %s\n0 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_AND_") {
				fprintf(f, ".names %s %s %s\n11 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\B")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_OR_") {
				fprintf(f, ".names %s %s %s\n1- 1\n-1 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\B")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_XOR_") {
				fprintf(f, ".names %s %s %s\n10 1\n01 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\B")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_MUX_") {
				fprintf(f, ".names %s %s %s %s\n1-0 1\n-11 1\n",
						cstr(cell->connections.at("\\A")), cstr(cell->connections.at("\\B")),
						cstr(cell->connections.at("\\S")), cstr(cell->connections.at("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_DFF_N_") {
				fprintf(f, ".latch %s %s fe %s\n",
						cstr(cell->connections.at("\\D")), cstr(cell->connections.at("\\Q")), cstr(cell->connections.at("\\C")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_DFF_P_") {
				fprintf(f, ".latch %s %s re %s\n",
						cstr(cell->connections.at("\\D")), cstr(cell->connections.at("\\Q")), cstr(cell->connections.at("\\C")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$lut") {
				fprintf(f, ".names");
				auto &inputs = cell->connections.at("\\I");
				auto width = cell->parameters.at("\\WIDTH").as_int();
				log_assert(inputs.size() == width);
				for (int i = 0; i < inputs.size(); i++) {
					fprintf(f, " %s", cstr(inputs.extract(i, 1)));
				}
				auto &output = cell->connections.at("\\O");
				log_assert(output.size() == 1);
				fprintf(f, " %s", cstr(output));
				fprintf(f, "\n");
				auto mask = cell->parameters.at("\\LUT").as_string();
				for (int i = 0; i < (1 << width); i++) {
					if (mask[i] == '0') continue;
					for (int j = width-1; j >= 0; j--) {
						fputc((i>>j)&1 ? '1' : '0', f);
					}
					fprintf(f, " %c\n", mask[i]);
				}
				continue;
			}

			fprintf(f, ".%s %s", subckt_or_gate(cell->type), cstr(cell->type));
			for (auto &conn : cell->connections)
			for (int i = 0; i < conn.second.size(); i++) {
				if (conn.second.size() == 1)
					fprintf(f, " %s", cstr(conn.first));
				else
					fprintf(f, " %s[%d]", cstr(conn.first), i);
				fprintf(f, "=%s", cstr(conn.second.extract(i, 1)));
			}
			fprintf(f, "\n");

			if (config->param_mode)
				for (auto &param : cell->parameters) {
					fprintf(f, ".param %s ", RTLIL::id2cstr(param.first));
					if (param.second.flags & RTLIL::CONST_FLAG_STRING) {
						std::string str = param.second.decode_string();
						fprintf(f, "\"");
						for (char ch : str)
							if (ch == '"' || ch == '\\')
								fprintf(f, "\\%c", ch);
							else if (ch < 32 || ch >= 127)
								fprintf(f, "\\%03o", ch);
							else
								fprintf(f, "%c", ch);
						fprintf(f, "\"\n");
					} else
						fprintf(f, "%s\n", param.second.as_string().c_str());
				}
		}

		for (auto &conn : module->connections)
		for (int i = 0; i < conn.first.size(); i++)
			if (config->conn_mode)
				fprintf(f, ".conn %s %s\n", cstr(conn.second.extract(i, 1)), cstr(conn.first.extract(i, 1)));
			else if (!config->buf_type.empty())
				fprintf(f, ".%s %s %s=%s %s=%s\n", subckt_or_gate(config->buf_type), config->buf_type.c_str(), config->buf_in.c_str(), cstr(conn.second.extract(i, 1)),
						config->buf_out.c_str(), cstr(conn.first.extract(i, 1)));
			else
				fprintf(f, ".names %s %s\n1 1\n", cstr(conn.second.extract(i, 1)), cstr(conn.first.extract(i, 1)));


		fprintf(f, ".end\n");
	}

	static void dump(FILE *f, RTLIL::Module *module, RTLIL::Design *design, BlifDumperConfig &config)
	{
		BlifDumper dumper(f, module, design, &config);
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
		log("    -buf <cell-type> <in-port> <out-port>\n");
		log("        use cells of type <cell-type> with the specified port names for buffers\n");
		log("\n");
		log("    -true <cell-type> <out-port>\n");
		log("    -false <cell-type> <out-port>\n");
		log("        use the specified cell types to drive nets that are constant 1 or 0\n");
		log("\n");
		log("The following options can be usefull when the generated file is not going to be\n");
		log("read by a BLIF parser but a custom tool. It is recommended to not name the output\n");
		log("file *.blif when any of this options is used.\n");
		log("\n");
		log("    -icells\n");
		log("        do not translate Yosys's internal gates to generic BLIF logic\n");
		log("        functions. Instead create .subckt or .gate lines for all cells.\n");
		log("\n");
		log("    -gates\n");
		log("        print .gate instead of .subckt lines for all cells that are not\n");
		log("        instantiations of other modules from this design.\n");
		log("\n");
		log("    -conn\n");
		log("        do not generate buffers for connected wires. instead use the\n");
		log("        non-standard .conn statement.\n");
		log("\n");
		log("    -param\n");
		log("        use the non-standard .param statement to write module parameters\n");
		log("\n");
		log("    -impltf\n");
		log("        do not write definitions for the $true and $false wires.\n");
		log("\n");
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_module_name;
		std::string buf_type, buf_in, buf_out;
		std::string true_type, true_out;
		std::string false_type, false_out;
		BlifDumperConfig config;

		log_header("Executing BLIF backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module_name = args[++argidx];
				continue;
			}
			if (args[argidx] == "-buf" && argidx+3 < args.size()) {
				config.buf_type = args[++argidx];
				config.buf_in = args[++argidx];
				config.buf_out = args[++argidx];
				continue;
			}
			if (args[argidx] == "-true" && argidx+2 < args.size()) {
				config.true_type = args[++argidx];
				config.true_out = args[++argidx];
				continue;
			}
			if (args[argidx] == "-false" && argidx+2 < args.size()) {
				config.false_type = args[++argidx];
				config.false_out = args[++argidx];
				continue;
			}
			if (args[argidx] == "-icells") {
				config.icells_mode = true;
				continue;
			}
			if (args[argidx] == "-gates") {
				config.gates_mode = true;
				continue;
			}
			if (args[argidx] == "-conn") {
				config.conn_mode = true;
				continue;
			}
			if (args[argidx] == "-param") {
				config.param_mode = true;
				continue;
			}
			if (args[argidx] == "-impltf") {
				config.impltf_mode = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		if (top_module_name.empty())
			for (auto & mod_it:design->modules)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_module_name = mod_it.first;

		fprintf(f, "# Generated by %s\n", yosys_version_str);

		std::vector<RTLIL::Module*> mod_list;

		for (auto module_it : design->modules)
		{
			RTLIL::Module *module = module_it.second;
			if (module->get_bool_attribute("\\blackbox"))
				continue;

			if (module->processes.size() != 0)
				log_error("Found unmapped processes in module %s: unmapped processes are not supported in BLIF backend!\n", RTLIL::id2cstr(module->name));
			if (module->memories.size() != 0)
				log_error("Found munmapped emories in module %s: unmapped memories are not supported in BLIF backend!\n", RTLIL::id2cstr(module->name));

			if (module->name == RTLIL::escape_id(top_module_name)) {
				BlifDumper::dump(f, module, design, config);
				top_module_name.clear();
				continue;
			}

			mod_list.push_back(module);
		}

		if (!top_module_name.empty())
			log_error("Can't find top module `%s'!\n", top_module_name.c_str());

		for (auto module : mod_list)
			BlifDumper::dump(f, module, design, config);
	}
} BlifBackend;

