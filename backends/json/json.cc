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

struct JsonWriter
{
	std::ostream &f;
	bool use_selection;

	Design *design;
	Module *module;

	SigMap sigmap;
	int sigidcounter;
	dict<SigBit, string> sigids;

	JsonWriter(std::ostream &f, bool use_selection) : f(f), use_selection(use_selection) { }

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

	void write_module(Module *module_)
	{
		module = module_;
		log_assert(module->design == design);
		sigmap.set(module);
		sigids.clear();

		// reserve 0 and 1 to avoid confusion with "0" and "1"
		sigidcounter = 2;

		f << stringf("    %s: {\n", get_name(module->name).c_str());

		f << stringf("      \"ports\": {");
		bool first = true;
		for (auto n : module->ports) {
			Wire *w = module->wire(n);
			if (use_selection && !module->selected(w))
				continue;
			f << stringf("%s\n", first ? "" : ",");
			f << stringf("        %s: {\n", get_name(n).c_str());
			f << stringf("          \"direction\": \"%s\",\n", w->port_input ? w->port_output ? "inout" : "input" : "output");
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
			f << stringf("          \"parameters\": {");
			bool first2 = true;
			for (auto &param : c->parameters) {
				f << stringf("%s\n", first2 ? "" : ",");
				f << stringf("            %s: ", get_name(param.first).c_str());
				if ((param.second.flags & RTLIL::ConstFlags::CONST_FLAG_STRING) != 0)
					f << get_string(param.second.decode_string());
				else if (GetSize(param.second.bits) > 32)
					f << get_string(param.second.as_string());
				else
					f << stringf("%d", param.second.as_int());
				first2 = false;
			}
			f << stringf("\n          },\n");
			f << stringf("          \"connections\": {");
			first2 = true;
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
			f << stringf("          \"bits\": %s\n", get_bits(w).c_str());
			f << stringf("        }");
			first = false;
		}
		f << stringf("\n      }\n");

		f << stringf("    }");
	}

	void write_design(Design *design_)
	{
		design = design_;
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
		f << stringf("\n  }\n");
		f << stringf("}\n");
	}
};

struct JsonBackend : public Backend {
	JsonBackend() : Backend("json", "write design to a JSON file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_json [options] [filename]\n");
		log("\n");
		log("Write a JSON netlist of the current design.\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-verbose") {
			// 	verbose = true;
			// 	continue;
			// }
			break;
		}
		extra_args(f, filename, args, argidx);

		log_header("Executing JSON backend.\n");

		JsonWriter json_writer(*f, false);
		json_writer.write_design(design);
	}
} JsonBackend;

struct JsonPass : public Pass {
	JsonPass() : Pass("json", "write design to a JSON file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_json [options] [selection]\n");
		log("\n");
		log("Write a JSON netlist of all selected objects.\n");
		log("\n");
		log("    -o <filename>\n");
		log("        write to the specified file.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string filename;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-o" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::ostream *f;
		std::stringstream buf;

		if (!filename.empty()) {
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

		JsonWriter json_writer(*f, true);
		json_writer.write_design(design);

		if (!filename.empty()) {
			delete f;
		} else {
			log("%s", buf.str().c_str());
		}
	}
} JsonPass;

PRIVATE_NAMESPACE_END
