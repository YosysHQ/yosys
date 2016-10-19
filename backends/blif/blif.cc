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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct BlifDumperConfig
{
	bool icells_mode;
	bool conn_mode;
	bool impltf_mode;
	bool gates_mode;
	bool cname_mode;
	bool param_mode;
	bool attr_mode;
	bool blackbox_mode;
	bool noalias_mode;

	std::string buf_type, buf_in, buf_out;
	std::map<RTLIL::IdString, std::pair<RTLIL::IdString, RTLIL::IdString>> unbuf_types;
	std::string true_type, true_out, false_type, false_out, undef_type, undef_out;

	BlifDumperConfig() : icells_mode(false), conn_mode(false), impltf_mode(false), gates_mode(false),
			cname_mode(false), param_mode(false), attr_mode(false), blackbox_mode(false), noalias_mode(false) { }
};

struct BlifDumper
{
	std::ostream &f;
	RTLIL::Module *module;
	RTLIL::Design *design;
	BlifDumperConfig *config;
	CellTypes ct;

	SigMap sigmap;
	dict<SigBit, int> init_bits;

	BlifDumper(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, BlifDumperConfig *config) :
			f(f), module(module), design(design), config(config), ct(design), sigmap(module)
	{
		for (Wire *wire : module->wires())
			if (wire->attributes.count("\\init")) {
				SigSpec initsig = sigmap(wire);
				Const initval = wire->attributes.at("\\init");
				for (int i = 0; i < GetSize(initsig) && i < GetSize(initval); i++)
					switch (initval[i]) {
						case State::S0:
							init_bits[initsig[i]] = 0;
							break;
						case State::S1:
							init_bits[initsig[i]] = 1;
							break;
						default:
							break;
					}
			}
	}

	vector<shared_str> cstr_buf;
	pool<SigBit> cstr_bits_seen;

	const char *cstr(RTLIL::IdString id)
	{
		std::string str = RTLIL::unescape_id(id);
		for (size_t i = 0; i < str.size(); i++)
			if (str[i] == '#' || str[i] == '=' || str[i] == '<' || str[i] == '>')
				str[i] = '?';
		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	const char *cstr(RTLIL::SigBit sig)
	{
		cstr_bits_seen.insert(sig);

		if (sig.wire == NULL) {
			if (sig == RTLIL::State::S0) return config->false_type == "-" || config->false_type == "+" ? config->false_out.c_str() : "$false";
			if (sig == RTLIL::State::S1) return config->true_type == "-" || config->true_type == "+" ? config->true_out.c_str() : "$true";
			return config->undef_type == "-" || config->undef_type == "+" ? config->undef_out.c_str() : "$undef";
		}

		std::string str = RTLIL::unescape_id(sig.wire->name);
		for (size_t i = 0; i < str.size(); i++)
			if (str[i] == '#' || str[i] == '=' || str[i] == '<' || str[i] == '>')
				str[i] = '?';

		if (sig.wire->width != 1)
			str += stringf("[%d]", sig.offset);

		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	const char *cstr_init(RTLIL::SigBit sig)
	{
		sigmap.apply(sig);

		if (init_bits.count(sig) == 0)
			return " 2";

		string str = stringf(" %d", init_bits.at(sig));

		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	const char *subckt_or_gate(std::string cell_type)
	{
		if (!config->gates_mode)
			return "subckt";
		if (!design->modules_.count(RTLIL::escape_id(cell_type)))
			return "gate";
		if (design->modules_.at(RTLIL::escape_id(cell_type))->get_bool_attribute("\\blackbox"))
			return "gate";
		return "subckt";
	}

	void dump_params(const char *command, dict<IdString, Const> &params)
	{
		for (auto &param : params) {
			f << stringf("%s %s ", command, RTLIL::id2cstr(param.first));
			if (param.second.flags & RTLIL::CONST_FLAG_STRING) {
				std::string str = param.second.decode_string();
				f << stringf("\"");
				for (char ch : str)
					if (ch == '"' || ch == '\\')
						f << stringf("\\%c", ch);
					else if (ch < 32 || ch >= 127)
						f << stringf("\\%03o", ch);
					else
						f << stringf("%c", ch);
				f << stringf("\"\n");
			} else
				f << stringf("%s\n", param.second.as_string().c_str());
		}
	}

	void dump()
	{
		f << stringf("\n");
		f << stringf(".model %s\n", cstr(module->name));

		std::map<int, RTLIL::Wire*> inputs, outputs;

		for (auto &wire_it : module->wires_) {
			RTLIL::Wire *wire = wire_it.second;
			if (wire->port_input)
				inputs[wire->port_id] = wire;
			if (wire->port_output)
				outputs[wire->port_id] = wire;
		}

		f << stringf(".inputs");
		for (auto &it : inputs) {
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				f << stringf(" %s", cstr(RTLIL::SigSpec(wire, i)));
		}
		f << stringf("\n");

		f << stringf(".outputs");
		for (auto &it : outputs) {
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				f << stringf(" %s", cstr(RTLIL::SigSpec(wire, i)));
		}
		f << stringf("\n");

		if (module->get_bool_attribute("\\blackbox")) {
			f << stringf(".blackbox\n");
			f << stringf(".end\n");
			return;
		}

		if (!config->impltf_mode) {
			if (!config->false_type.empty()) {
				if (config->false_type == "+")
					f << stringf(".names %s\n", config->false_out.c_str());
				else if (config->false_type != "-")
					f << stringf(".%s %s %s=$false\n", subckt_or_gate(config->false_type),
							config->false_type.c_str(), config->false_out.c_str());
			} else
				f << stringf(".names $false\n");
			if (!config->true_type.empty()) {
				if (config->true_type == "+")
					f << stringf(".names %s\n1\n", config->true_out.c_str());
				else if (config->true_type != "-")
					f << stringf(".%s %s %s=$true\n", subckt_or_gate(config->true_type),
							config->true_type.c_str(), config->true_out.c_str());
			} else
				f << stringf(".names $true\n1\n");
			if (!config->undef_type.empty()) {
				if (config->undef_type == "+")
					f << stringf(".names %s\n", config->undef_out.c_str());
				else if (config->undef_type != "-")
					f << stringf(".%s %s %s=$undef\n", subckt_or_gate(config->undef_type),
							config->undef_type.c_str(), config->undef_out.c_str());
			} else
				f << stringf(".names $undef\n");
		}

		for (auto &cell_it : module->cells_)
		{
			RTLIL::Cell *cell = cell_it.second;

			if (config->unbuf_types.count(cell->type)) {
				auto portnames = config->unbuf_types.at(cell->type);
				f << stringf(".names %s %s\n1 1\n",
						cstr(cell->getPort(portnames.first)), cstr(cell->getPort(portnames.second)));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_NOT_") {
				f << stringf(".names %s %s\n0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_AND_") {
				f << stringf(".names %s %s %s\n11 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_OR_") {
				f << stringf(".names %s %s %s\n1- 1\n-1 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_XOR_") {
				f << stringf(".names %s %s %s\n10 1\n01 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_NAND_") {
				f << stringf(".names %s %s %s\n0- 1\n-0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_NOR_") {
				f << stringf(".names %s %s %s\n00 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_XNOR_") {
				f << stringf(".names %s %s %s\n11 1\n00 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_AOI3_") {
				f << stringf(".names %s %s %s %s\n-00 1\n0-0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\C")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_OAI3_") {
				f << stringf(".names %s %s %s %s\n00- 1\n--0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\C")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_AOI4_") {
				f << stringf(".names %s %s %s %s %s\n-0-0 1\n-00- 1\n0--0 1\n0-0- 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")),
						cstr(cell->getPort("\\C")), cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_OAI4_") {
				f << stringf(".names %s %s %s %s %s\n00-- 1\n--00 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")),
						cstr(cell->getPort("\\C")), cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_MUX_") {
				f << stringf(".names %s %s %s %s\n1-0 1\n-11 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")),
						cstr(cell->getPort("\\S")), cstr(cell->getPort("\\Y")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_FF_") {
				f << stringf(".latch %s %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr_init(cell->getPort("\\Q")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_DFF_N_") {
				f << stringf(".latch %s %s fe %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr(cell->getPort("\\C")), cstr_init(cell->getPort("\\Q")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_DFF_P_") {
				f << stringf(".latch %s %s re %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr(cell->getPort("\\C")), cstr_init(cell->getPort("\\Q")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_DLATCH_N_") {
				f << stringf(".latch %s %s al %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr(cell->getPort("\\E")), cstr_init(cell->getPort("\\Q")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_DLATCH_P_") {
				f << stringf(".latch %s %s ah %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr(cell->getPort("\\E")), cstr_init(cell->getPort("\\Q")));
				continue;
			}

			if (!config->icells_mode && cell->type == "$lut") {
				f << stringf(".names");
				auto &inputs = cell->getPort("\\A");
				auto width = cell->parameters.at("\\WIDTH").as_int();
				log_assert(inputs.size() == width);
				for (int i = width-1; i >= 0; i--)
					f << stringf(" %s", cstr(inputs.extract(i, 1)));
				auto &output = cell->getPort("\\Y");
				log_assert(output.size() == 1);
				f << stringf(" %s", cstr(output));
				f << stringf("\n");
				RTLIL::SigSpec mask = cell->parameters.at("\\LUT");
				for (int i = 0; i < (1 << width); i++)
					if (mask[i] == RTLIL::S1) {
						for (int j = width-1; j >= 0; j--) {
							f << ((i>>j)&1 ? '1' : '0');
						}
						f << " 1\n";
					}
				continue;
			}

			if (!config->icells_mode && cell->type == "$sop") {
				f << stringf(".names");
				auto &inputs = cell->getPort("\\A");
				auto width = cell->parameters.at("\\WIDTH").as_int();
				auto depth = cell->parameters.at("\\DEPTH").as_int();
				vector<State> table = cell->parameters.at("\\TABLE").bits;
				while (GetSize(table) < 2*width*depth)
					table.push_back(State::S0);
				log_assert(inputs.size() == width);
				for (int i = 0; i < width; i++)
					f << stringf(" %s", cstr(inputs.extract(i, 1)));
				auto &output = cell->getPort("\\Y");
				log_assert(output.size() == 1);
				f << stringf(" %s", cstr(output));
				f << stringf("\n");
				for (int i = 0; i < depth; i++) {
					for (int j = 0; j < width; j++) {
						bool pat0 = table.at(2*width*i + 2*j + 0) == State::S1;
						bool pat1 = table.at(2*width*i + 2*j + 1) == State::S1;
						if (pat0 && !pat1) f << "0";
						else if (!pat0 && pat1) f << "1";
						else f << "-";
					}
					f << " 1\n";
				}
				continue;
			}

			f << stringf(".%s %s", subckt_or_gate(cell->type.str()), cstr(cell->type));
			for (auto &conn : cell->connections())
			for (int i = 0; i < conn.second.size(); i++) {
				if (conn.second.size() == 1)
					f << stringf(" %s", cstr(conn.first));
				else
					f << stringf(" %s[%d]", cstr(conn.first), i);
				f << stringf("=%s", cstr(conn.second.extract(i, 1)));
			}
			f << stringf("\n");

			if (config->cname_mode)
				f << stringf(".cname %s\n", cstr(cell->name));
			if (config->attr_mode)
				dump_params(".attr", cell->attributes);
			if (config->param_mode)
				dump_params(".param", cell->parameters);
		}

		for (auto &conn : module->connections())
		for (int i = 0; i < conn.first.size(); i++)
		{
			SigBit lhs_bit = conn.first[i];
			SigBit rhs_bit = conn.second[i];

			if (config->noalias_mode && cstr_bits_seen.count(lhs_bit) == 0)
				continue;

			if (config->conn_mode)
				f << stringf(".conn %s %s\n", cstr(rhs_bit), cstr(lhs_bit));
			else if (!config->buf_type.empty())
				f << stringf(".%s %s %s=%s %s=%s\n", subckt_or_gate(config->buf_type), config->buf_type.c_str(),
						config->buf_in.c_str(), cstr(rhs_bit), config->buf_out.c_str(), cstr(lhs_bit));
			else
				f << stringf(".names %s %s\n1 1\n", cstr(rhs_bit), cstr(lhs_bit));
		}

		f << stringf(".end\n");
	}

	static void dump(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, BlifDumperConfig &config)
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
		log("    -unbuf <cell-type> <in-port> <out-port>\n");
		log("        replace buffer cells with the specified name and port names with\n");
		log("        a .names statement that models a buffer\n");
		log("\n");
		log("    -true <cell-type> <out-port>\n");
		log("    -false <cell-type> <out-port>\n");
		log("    -undef <cell-type> <out-port>\n");
		log("        use the specified cell types to drive nets that are constant 1, 0, or\n");
		log("        undefined. when '-' is used as <cell-type>, then <out-port> specifies\n");
		log("        the wire name to be used for the constant signal and no cell driving\n");
		log("        that wire is generated. when '+' is used as <cell-type>, then <out-port>\n");
		log("        specifies the wire name to be used for the constant signal and a .names\n");
		log("        statement is generated to drive the wire.\n");
		log("\n");
		log("    -noalias\n");
		log("        if a net name is aliasing another net name, then by default a net\n");
		log("        without fanout is created that is driven by the other net. This option\n");
		log("        suppresses the generation of this nets without fanout.\n");
		log("\n");
		log("The following options can be useful when the generated file is not going to be\n");
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
		log("    -attr\n");
		log("        use the non-standard .attr statement to write cell attributes\n");
		log("\n");
		log("    -param\n");
		log("        use the non-standard .param statement to write cell parameters\n");
		log("\n");
		log("    -cname\n");
		log("        use the non-standard .cname statement to write cell names\n");
		log("\n");
		log("    -blackbox\n");
		log("        write blackbox cells with .blackbox statement.\n");
		log("\n");
		log("    -impltf\n");
		log("        do not write definitions for the $true, $false and $undef wires.\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_module_name;
		std::string buf_type, buf_in, buf_out;
		std::string true_type, true_out;
		std::string false_type, false_out;
		BlifDumperConfig config;

		log_header(design, "Executing BLIF backend.\n");

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
			if (args[argidx] == "-unbuf" && argidx+3 < args.size()) {
				RTLIL::IdString unbuf_type = RTLIL::escape_id(args[++argidx]);
				RTLIL::IdString unbuf_in = RTLIL::escape_id(args[++argidx]);
				RTLIL::IdString unbuf_out = RTLIL::escape_id(args[++argidx]);
				config.unbuf_types[unbuf_type] = std::pair<RTLIL::IdString, RTLIL::IdString>(unbuf_in, unbuf_out);
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
			if (args[argidx] == "-undef" && argidx+2 < args.size()) {
				config.undef_type = args[++argidx];
				config.undef_out = args[++argidx];
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
			if (args[argidx] == "-cname") {
				config.cname_mode = true;
				continue;
			}
			if (args[argidx] == "-param") {
				config.param_mode = true;
				continue;
			}
			if (args[argidx] == "-attr") {
				config.attr_mode = true;
				continue;
			}
			if (args[argidx] == "-blackbox") {
				config.blackbox_mode = true;
				continue;
			}
			if (args[argidx] == "-impltf") {
				config.impltf_mode = true;
				continue;
			}
			if (args[argidx] == "-noalias") {
				config.noalias_mode = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		if (top_module_name.empty())
			for (auto & mod_it:design->modules_)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_module_name = mod_it.first.str();

		*f << stringf("# Generated by %s\n", yosys_version_str);

		std::vector<RTLIL::Module*> mod_list;

		design->sort();
		for (auto module_it : design->modules_)
		{
			RTLIL::Module *module = module_it.second;
			if (module->get_bool_attribute("\\blackbox") && !config.blackbox_mode)
				continue;

			if (module->processes.size() != 0)
				log_error("Found unmapped processes in module %s: unmapped processes are not supported in BLIF backend!\n", RTLIL::id2cstr(module->name));
			if (module->memories.size() != 0)
				log_error("Found unmapped memories in module %s: unmapped memories are not supported in BLIF backend!\n", RTLIL::id2cstr(module->name));

			if (module->name == RTLIL::escape_id(top_module_name)) {
				BlifDumper::dump(*f, module, design, config);
				top_module_name.clear();
				continue;
			}

			mod_list.push_back(module);
		}

		if (!top_module_name.empty())
			log_error("Can't find top module `%s'!\n", top_module_name.c_str());

		for (auto module : mod_list)
			BlifDumper::dump(*f, module, design, config);
	}
} BlifBackend;

PRIVATE_NAMESPACE_END
