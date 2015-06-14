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

struct SmvWorker
{
	CellTypes ct;
	SigMap sigmap;
	RTLIL::Module *module;
	std::ostream &f;
	bool verbose;

	int idcounter;
	dict<IdString, shared_str> idcache;
	pool<shared_str> used_names;

	const char *cid()
	{
		while (true) {
			shared_str s(stringf("_%d", idcounter++));
			if (!used_names.count(s)) {
				used_names.insert(s);
				return s.c_str();
			}
		}
	}

	const char *cid(IdString id, bool precache = false)
	{
		if (!idcache.count(id))
		{
			string name = log_id(id);

			for (auto &c : name) {
				if (c >= 'a' && c <='z') continue;
				if (c >= 'A' && c <='Z') continue;
				if (c >= '0' && c <='9') continue;
				if (precache) return nullptr;
				c = '_';
			}

			while (used_names.count(name))
				name += "_";

			shared_str s(name);
			used_names.insert(s);
			idcache[id] = s;
		}

		return idcache.at(id).c_str();
	}

	SmvWorker(RTLIL::Module *module, bool verbose, std::ostream &f) :
			ct(module->design), sigmap(module), module(module), f(f), verbose(verbose), idcounter(0)
	{
		for (auto mod : module->design->modules())
			cid(mod->name, true);

		for (auto wire : module->wires())
			cid(wire->name, true);

		for (auto cell : module->cells()) {
			cid(cell->name, true);
			cid(cell->type, true);
			for (auto &conn : cell->connections())
				cid(conn.first, true);
		}
	}

	string rvalue(SigSpec sig)
	{
		string s;
		sigmap.apply(sig);
		for (auto &c : sig.chunks()) {
			if (!s.empty())
				s += " :: ";
			if (c.wire) {
				s += cid(c.wire->name);
				if (c.offset != 0 || c.width != c.wire->width)
					s += stringf("[%d:%d]", c.offset+c.width-1, c.offset);
			} else {
				s += stringf("0ub%d_", c.width);
				for (int i = c.width-1; i >= 0; i--)
					s += c.data.at(i) == State::S1 ? '1' : '0';
			}
		}
		return s;
	}

	string lvalue(SigSpec sig)
	{
		if (sig.is_wire())
			return rvalue(sig);

		log_error("Can not generate lvalue for singal %s. Try running 'splice'.\n", log_signal(sig));
	}

	void run()
	{
		vector<string> assignments;

		f << stringf("MODULE %s\n", cid(module->name));
		f << stringf("  VAR\n");

		for (auto wire : module->wires())
			f << stringf("    %s : unsigned word[%d];\n", cid(wire->name), wire->width);

		for (auto cell : module->cells())
		{
			f << stringf("    %s : %s;\n", cid(cell->name), cid(cell->type));

			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					assignments.push_back(stringf("%s := %s.%s;", lvalue(conn.second).c_str(), cid(cell->name), cid(conn.first)));
				else
					assignments.push_back(stringf("%s.%s := %s;", cid(cell->name), cid(conn.first), rvalue(conn.second).c_str()));
		}

		f << stringf("  ASSIGN\n");
		for (const string &line : assignments)
			f << stringf("    %s\n", line.c_str());
	}
};

struct SmvBackend : public Backend {
	SmvBackend() : Backend("smv", "write design to SMV file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_smv [options] [filename]\n");
		log("\n");
		log("Write an SMV description of the current design.\n");
		log("\n");
		log("    -verbose\n");
		log("        this will print the recursive walk used to export the modules.\n");
		log("\n");
		log("    -tpl <template_file>\n");
		log("        use the given template file. the line containing only the token '%%%%'\n");
		log("        is replaced with the regular output of this command.\n");
		log("\n");
		log("THIS COMMAND IS UNDER CONSTRUCTION\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		std::ifstream template_f;
		bool verbose = false;

		log_header("Executing SMV backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-tpl" && argidx+1 < args.size()) {
				template_f.open(args[++argidx]);
				if (template_f.fail())
					log_error("Can't open template file `%s'.\n", args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-verbose") {
				verbose = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		pool<Module*> modules;

		for (auto module : design->modules())
			if (!module->get_bool_attribute("\\blackbox") && !module->has_memories_warn() && !module->has_processes_warn())
				modules.insert(module);

		if (template_f.is_open())
		{
			std::string line;
			while (std::getline(template_f, line))
			{
				int indent = 0;
				while (indent < GetSize(line) && (line[indent] == ' ' || line[indent] == '\t'))
					indent++;

				if (line[indent] == '$')
				{
					vector<string> stmt = split_tokens(line);

					if (GetSize(stmt) == 1 && stmt[0] == "%%")
						break;

					if (GetSize(stmt) == 2 && stmt[0] == "%module")
					{
						Module *module = design->module(RTLIL::escape_id(stmt[1]));

						if (module == nullptr)
							log_error("Module '%s' not found.\n", stmt[1].c_str());

						*f << stringf("-- SMV description generated by %s\n", yosys_version_str);

						log("Creating SMV representation of module %s.\n", log_id(module));
						SmvWorker worker(module, verbose, *f);
						worker.run();

						*f << stringf("-- end of yosys output\n");
						continue;
					}

					log_error("Unknown template statement: '%s'", line.c_str() + indent);
				}

				*f << line << std::endl;
			}
		}

		*f << stringf("-- SMV description generated by %s\n", yosys_version_str);

		for (auto module : modules) {
			log("Creating SMV representation of module %s.\n", log_id(module));
			SmvWorker worker(module, verbose, *f);
			worker.run();
		}

		*f << stringf("-- end of yosys output\n");

		if (template_f.is_open()) {
			std::string line;
			while (std::getline(template_f, line))
				*f << line << std::endl;
		}
	}
} SmvBackend;

PRIVATE_NAMESPACE_END
