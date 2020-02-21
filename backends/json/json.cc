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
#include "kernel/cellaigs.h"
#include "kernel/log.h"
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct JsonWriter
{
	std::ostream &f;
	bool use_selection;
	bool aig_mode;
	bool compat_int_mode;

	Design *design;
	Module *module;

	SigMap sigmap;
	int sigidcounter;
	dict<SigBit, string> sigids;
	pool<Aig> aig_models;

	JsonWriter(std::ostream &f, bool use_selection, bool aig_mode, bool compat_int_mode) :
			f(f), use_selection(use_selection), aig_mode(aig_mode),
			compat_int_mode(compat_int_mode) { }

	string get_string(string str)
	{
		string newstr = "\"";
		for (char c : str) {
			if (c == '\\')
				newstr += c;
			newstr += c;
		}
		return newstr + "\"";
	}

	string get_name(IdString name)
	{
		return get_string(RTLIL::unescape_id(name));
	}

	string get_bits(SigSpec sig)
	{
		bool first = true;
		string str = "[";
		for (auto bit : sigmap(sig)) {
			str += first ? " " : ", ";
			first = false;
			if (sigids.count(bit) == 0) {
				string &s = sigids[bit];
				if (bit.wire == nullptr) {
					if (bit == State::S0) s = "\"0\"";
					else if (bit == State::S1) s = "\"1\"";
					else if (bit == State::Sz) s = "\"z\"";
					else s = "\"x\"";
				} else
					s = stringf("%d", sigidcounter++);
			}
			str += sigids[bit];
		}
		return str + " ]";
	}

	void write_parameter_value(const Const &value)
	{
		if ((value.flags & RTLIL::ConstFlags::CONST_FLAG_STRING) != 0) {
			string str = value.decode_string();
			int state = 0;
			for (char c : str) {
				if (state == 0) {
					if (c == '0' || c == '1' || c == 'x' || c == 'z')
						state = 0;
					else if (c == ' ')
						state = 1;
					else
						state = 2;
				} else if (state == 1 && c != ' ')
					state = 2;
			}
			if (state < 2)
				str += " ";
			f << get_string(str);
		} else if (compat_int_mode && GetSize(value) <= 32 && value.is_fully_def()) {
			if ((value.flags & RTLIL::ConstFlags::CONST_FLAG_SIGNED) != 0)
				f << stringf("%d", value.as_int());
			else
				f << stringf("%u", value.as_int());
		} else {
			f << get_string(value.as_string());
		}
	}

	void write_parameters(const dict<IdString, Const> &parameters, bool for_module=false)
	{
		bool first = true;
		for (auto &param : parameters) {
			f << stringf("%s\n", first ? "" : ",");
			f << stringf("        %s%s: ", for_module ? "" : "    ", get_name(param.first).c_str());
			write_parameter_value(param.second);
			first = false;
		}
	}

	void write_module(Module *module_)
	{
		module = module_;
		log_assert(module->design == design);
		sigmap.set(module);
		sigids.clear();

		// reserve 0 and 1 to avoid confusion with "0" and "1"
		sigidcounter = 2;

		f << stringf("    %s: {\n", get_name(module->name).c_str());

		f << stringf("      \"attributes\": {");
		write_parameters(module->attributes, /*for_module=*/true);
		f << stringf("\n      },\n");

		f << stringf("      \"ports\": {");
		bool first = true;
		for (auto n : module->ports) {
			Wire *w = module->wire(n);
			if (use_selection && !module->selected(w))
				continue;
			f << stringf("%s\n", first ? "" : ",");
			f << stringf("        %s: {\n", get_name(n).c_str());
			f << stringf("          \"direction\": \"%s\",\n", w->port_input ? w->port_output ? "inout" : "input" : "output");
			if (w->start_offset)
				f << stringf("          \"offset\": %d,\n", w->start_offset);
			if (w->upto)
				f << stringf("          \"upto\": 1,\n");
			f << stringf("          \"bits\": %s\n", get_bits(w).c_str());
			f << stringf("        }");
			first = false;
		}
		f << stringf("\n      },\n");

		f << stringf("      \"cells\": {");
		first = true;
		for (auto c : module->cells()) {
			if (use_selection && !module->selected(c))
				continue;
			f << stringf("%s\n", first ? "" : ",");
			f << stringf("        %s: {\n", get_name(c->name).c_str());
			f << stringf("          \"hide_name\": %s,\n", c->name[0] == '$' ? "1" : "0");
			f << stringf("          \"type\": %s,\n", get_name(c->type).c_str());
			if (aig_mode) {
				Aig aig(c);
				if (!aig.name.empty()) {
					f << stringf("          \"model\": \"%s\",\n", aig.name.c_str());
					aig_models.insert(aig);
				}
			}
			f << stringf("          \"parameters\": {");
			write_parameters(c->parameters);
			f << stringf("\n          },\n");
			f << stringf("          \"attributes\": {");
			write_parameters(c->attributes);
			f << stringf("\n          },\n");
			if (c->known()) {
				f << stringf("          \"port_directions\": {");
				bool first2 = true;
				for (auto &conn : c->connections()) {
					string direction = "output";
					if (c->input(conn.first))
						direction = c->output(conn.first) ? "inout" : "input";
					f << stringf("%s\n", first2 ? "" : ",");
					f << stringf("            %s: \"%s\"", get_name(conn.first).c_str(), direction.c_str());
					first2 = false;
				}
				f << stringf("\n          },\n");
			}
			f << stringf("          \"connections\": {");
			bool first2 = true;
			for (auto &conn : c->connections()) {
				f << stringf("%s\n", first2 ? "" : ",");
				f << stringf("            %s: %s", get_name(conn.first).c_str(), get_bits(conn.second).c_str());
				first2 = false;
			}
			f << stringf("\n          }\n");
			f << stringf("        }");
			first = false;
		}
		f << stringf("\n      },\n");

		f << stringf("      \"netnames\": {");
		first = true;
		for (auto w : module->wires()) {
			if (use_selection && !module->selected(w))
				continue;
			f << stringf("%s\n", first ? "" : ",");
			f << stringf("        %s: {\n", get_name(w->name).c_str());
			f << stringf("          \"hide_name\": %s,\n", w->name[0] == '$' ? "1" : "0");
			f << stringf("          \"bits\": %s,\n", get_bits(w).c_str());
			if (w->start_offset)
				f << stringf("          \"offset\": %d,\n", w->start_offset);
			if (w->upto)
				f << stringf("          \"upto\": 1,\n");
			f << stringf("          \"attributes\": {");
			write_parameters(w->attributes);
			f << stringf("\n          }\n");
			f << stringf("        }");
			first = false;
		}
		f << stringf("\n      }\n");

		f << stringf("    }");
	}

	void write_design(Design *design_)
	{
		design = design_;
		design->sort();

		f << stringf("{\n");
		f << stringf("  \"creator\": %s,\n", get_string(yosys_version_str).c_str());
		f << stringf("  \"modules\": {\n");
		vector<Module*> modules = use_selection ? design->selected_modules() : design->modules();
		bool first_module = true;
		for (auto mod : modules) {
			if (!first_module)
				f << stringf(",\n");
			write_module(mod);
			first_module = false;
		}
		f << stringf("\n  }");
		if (!aig_models.empty()) {
			f << stringf(",\n  \"models\": {\n");
			bool first_model = true;
			for (auto &aig : aig_models) {
				if (!first_model)
					f << stringf(",\n");
				f << stringf("    \"%s\": [\n", aig.name.c_str());
				int node_idx = 0;
				for (auto &node : aig.nodes) {
					if (node_idx != 0)
						f << stringf(",\n");
					f << stringf("      /* %3d */ [ ", node_idx);
					if (node.portbit >= 0)
						f << stringf("\"%sport\", \"%s\", %d", node.inverter ? "n" : "",
								log_id(node.portname), node.portbit);
					else if (node.left_parent < 0 && node.right_parent < 0)
						f << stringf("\"%s\"", node.inverter ? "true" : "false");
					else
						f << stringf("\"%s\", %d, %d", node.inverter ? "nand" : "and", node.left_parent, node.right_parent);
					for (auto &op : node.outports)
						f << stringf(", \"%s\", %d", log_id(op.first), op.second);
					f << stringf(" ]");
					node_idx++;
				}
				f << stringf("\n    ]");
				first_model = false;
			}
			f << stringf("\n  }");
		}
		f << stringf("\n}\n");
	}
};

struct JsonBackend : public Backend {
	JsonBackend() : Backend("json", "write design to a JSON file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_json [options] [filename]\n");
		log("\n");
		log("Write a JSON netlist of the current design.\n");
		log("\n");
		log("    -aig\n");
		log("        include AIG models for the different gate types\n");
		log("\n");
		log("    -compat-int\n");
		log("        emit 32-bit or smaller fully-defined parameter values directly\n");
		log("        as JSON numbers (for compatibility with old parsers)\n");
		log("\n");
		log("\n");
		log("The general syntax of the JSON output created by this command is as follows:\n");
		log("\n");
		log("    {\n");
		log("      \"modules\": {\n");
		log("        <module_name>: {\n");
		log("          \"ports\": {\n");
		log("            <port_name>: <port_details>,\n");
		log("            ...\n");
		log("          },\n");
		log("          \"cells\": {\n");
		log("            <cell_name>: <cell_details>,\n");
		log("            ...\n");
		log("          },\n");
		log("          \"netnames\": {\n");
		log("            <net_name>: <net_details>,\n");
		log("            ...\n");
		log("          }\n");
		log("        }\n");
		log("      },\n");
		log("      \"models\": {\n");
		log("        ...\n");
		log("      },\n");
		log("    }\n");
		log("\n");
		log("Where <port_details> is:\n");
		log("\n");
		log("    {\n");
		log("      \"direction\": <\"input\" | \"output\" | \"inout\">,\n");
		log("      \"bits\": <bit_vector>\n");
		log("    }\n");
		log("\n");
		log("And <cell_details> is:\n");
		log("\n");
		log("    {\n");
		log("      \"hide_name\": <1 | 0>,\n");
		log("      \"type\": <cell_type>,\n");
		log("      \"parameters\": {\n");
		log("        <parameter_name>: <parameter_value>,\n");
		log("        ...\n");
		log("      },\n");
		log("      \"attributes\": {\n");
		log("        <attribute_name>: <attribute_value>,\n");
		log("        ...\n");
		log("      },\n");
		log("      \"port_directions\": {\n");
		log("        <port_name>: <\"input\" | \"output\" | \"inout\">,\n");
		log("        ...\n");
		log("      },\n");
		log("      \"connections\": {\n");
		log("        <port_name>: <bit_vector>,\n");
		log("        ...\n");
		log("      },\n");
		log("    }\n");
		log("\n");
		log("And <net_details> is:\n");
		log("\n");
		log("    {\n");
		log("      \"hide_name\": <1 | 0>,\n");
		log("      \"bits\": <bit_vector>\n");
		log("    }\n");
		log("\n");
		log("The \"hide_name\" fields are set to 1 when the name of this cell or net is\n");
		log("automatically created and is likely not of interest for a regular user.\n");
		log("\n");
		log("The \"port_directions\" section is only included for cells for which the\n");
		log("interface is known.\n");
		log("\n");
		log("Module and cell ports and nets can be single bit wide or vectors of multiple\n");
		log("bits. Each individual signal bit is assigned a unique integer. The <bit_vector>\n");
		log("values referenced above are vectors of this integers. Signal bits that are\n");
		log("connected to a constant driver are denoted as string \"0\", \"1\", \"x\", or\n");
		log("\"z\" instead of a number.\n");
		log("\n");
		log("Bit vectors (including integers) are written as string holding the binary");
		log("representation of the value. Strings are written as strings, with an appended");
		log("blank in cases of strings of the form /[01xz]* */.\n");
		log("\n");
		log("For example the following Verilog code:\n");
		log("\n");
		log("    module test(input x, y);\n");
		log("      (* keep *) foo #(.P(42), .Q(1337))\n");
		log("          foo_inst (.A({x, y}), .B({y, x}), .C({4'd10, {4{x}}}));\n");
		log("    endmodule\n");
		log("\n");
		log("Translates to the following JSON output:\n");
		log("\n");
		log("    {\n");
		log("      \"modules\": {\n");
		log("        \"test\": {\n");
		log("          \"ports\": {\n");
		log("            \"x\": {\n");
		log("              \"direction\": \"input\",\n");
		log("              \"bits\": [ 2 ]\n");
		log("            },\n");
		log("            \"y\": {\n");
		log("              \"direction\": \"input\",\n");
		log("              \"bits\": [ 3 ]\n");
		log("            }\n");
		log("          },\n");
		log("          \"cells\": {\n");
		log("            \"foo_inst\": {\n");
		log("              \"hide_name\": 0,\n");
		log("              \"type\": \"foo\",\n");
		log("              \"parameters\": {\n");
		log("                \"Q\": 1337,\n");
		log("                \"P\": 42\n");
		log("              },\n");
		log("              \"attributes\": {\n");
		log("                \"keep\": 1,\n");
		log("                \"src\": \"test.v:2\"\n");
		log("              },\n");
		log("              \"connections\": {\n");
		log("                \"C\": [ 2, 2, 2, 2, \"0\", \"1\", \"0\", \"1\" ],\n");
		log("                \"B\": [ 2, 3 ],\n");
		log("                \"A\": [ 3, 2 ]\n");
		log("              }\n");
		log("            }\n");
		log("          },\n");
		log("          \"netnames\": {\n");
		log("            \"y\": {\n");
		log("              \"hide_name\": 0,\n");
		log("              \"bits\": [ 3 ],\n");
		log("              \"attributes\": {\n");
		log("                \"src\": \"test.v:1\"\n");
		log("              }\n");
		log("            },\n");
		log("            \"x\": {\n");
		log("              \"hide_name\": 0,\n");
		log("              \"bits\": [ 2 ],\n");
		log("              \"attributes\": {\n");
		log("                \"src\": \"test.v:1\"\n");
		log("              }\n");
		log("            }\n");
		log("          }\n");
		log("        }\n");
		log("      }\n");
		log("    }\n");
		log("\n");
		log("The models are given as And-Inverter-Graphs (AIGs) in the following form:\n");
		log("\n");
		log("    \"models\": {\n");
		log("      <model_name>: [\n");
		log("        /*   0 */ [ <node-spec> ],\n");
		log("        /*   1 */ [ <node-spec> ],\n");
		log("        /*   2 */ [ <node-spec> ],\n");
		log("        ...\n");
		log("      ],\n");
		log("      ...\n");
		log("    },\n");
		log("\n");
		log("The following node-types may be used:\n");
		log("\n");
		log("    [ \"port\", <portname>, <bitindex>, <out-list> ]\n");
		log("      - the value of the specified input port bit\n");
		log("\n");
		log("    [ \"nport\", <portname>, <bitindex>, <out-list> ]\n");
		log("      - the inverted value of the specified input port bit\n");
		log("\n");
		log("    [ \"and\", <node-index>, <node-index>, <out-list> ]\n");
		log("      - the ANDed value of the specified nodes\n");
		log("\n");
		log("    [ \"nand\", <node-index>, <node-index>, <out-list> ]\n");
		log("      - the inverted ANDed value of the specified nodes\n");
		log("\n");
		log("    [ \"true\", <out-list> ]\n");
		log("      - the constant value 1\n");
		log("\n");
		log("    [ \"false\", <out-list> ]\n");
		log("      - the constant value 0\n");
		log("\n");
		log("All nodes appear in topological order. I.e. only nodes with smaller indices\n");
		log("are referenced by \"and\" and \"nand\" nodes.\n");
		log("\n");
		log("The optional <out-list> at the end of a node specification is a list of\n");
		log("output portname and bitindex pairs, specifying the outputs driven by this node.\n");
		log("\n");
		log("For example, the following is the model for a 3-input 3-output $reduce_and cell\n");
		log("inferred by the following code:\n");
		log("\n");
		log("    module test(input [2:0] in, output [2:0] out);\n");
		log("      assign in = &out;\n");
		log("    endmodule\n");
		log("\n");
		log("    \"$reduce_and:3U:3\": [\n");
		log("      /*   0 */ [ \"port\", \"A\", 0 ],\n");
		log("      /*   1 */ [ \"port\", \"A\", 1 ],\n");
		log("      /*   2 */ [ \"and\", 0, 1 ],\n");
		log("      /*   3 */ [ \"port\", \"A\", 2 ],\n");
		log("      /*   4 */ [ \"and\", 2, 3, \"Y\", 0 ],\n");
		log("      /*   5 */ [ \"false\", \"Y\", 1, \"Y\", 2 ]\n");
		log("    ]\n");
		log("\n");
		log("Future version of Yosys might add support for additional fields in the JSON\n");
		log("format. A program processing this format must ignore all unknown fields.\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool aig_mode = false;
		bool compat_int_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-aig") {
				aig_mode = true;
				continue;
			}
			if (args[argidx] == "-compat-int") {
				compat_int_mode = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		log_header(design, "Executing JSON backend.\n");

		JsonWriter json_writer(*f, false, aig_mode, compat_int_mode);
		json_writer.write_design(design);
	}
} JsonBackend;

struct JsonPass : public Pass {
	JsonPass() : Pass("json", "write design in JSON format") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    json [options] [selection]\n");
		log("\n");
		log("Write a JSON netlist of all selected objects.\n");
		log("\n");
		log("    -o <filename>\n");
		log("        write to the specified file.\n");
		log("\n");
		log("    -aig\n");
		log("        also include AIG models for the different gate types\n");
		log("\n");
		log("    -compat-int\n");
		log("        emit 32-bit or smaller fully-defined parameter values directly\n");
		log("        as JSON numbers (for compatibility with old parsers)\n");
		log("\n");
		log("See 'help write_json' for a description of the JSON format used.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string filename;
		bool aig_mode = false;
		bool compat_int_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-o" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-aig") {
				aig_mode = true;
				continue;
			}
			if (args[argidx] == "-compat-int") {
				compat_int_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::ostream *f;
		std::stringstream buf;

		if (!filename.empty()) {
			rewrite_filename(filename);
			std::ofstream *ff = new std::ofstream;
			ff->open(filename.c_str(), std::ofstream::trunc);
			if (ff->fail()) {
				delete ff;
				log_error("Can't open file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
			}
			f = ff;
		} else {
			f = &buf;
		}

		JsonWriter json_writer(*f, true, aig_mode, compat_int_mode);
		json_writer.write_design(design);

		if (!filename.empty()) {
			delete f;
		} else {
			log("%s", buf.str().c_str());
		}
	}
} JsonPass;

PRIVATE_NAMESPACE_END
