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
	vector<shared_str> strbuf;

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
			string name = stringf("_%s", id.c_str());

			if (name.substr(0, 2) == "_\\")
				name = "_" + name.substr(2);

			for (auto &c : name) {
				if (c == '|' || c == '$' || c == '_') continue;
				if (c >= 'a' && c <='z') continue;
				if (c >= 'A' && c <='Z') continue;
				if (c >= '0' && c <='9') continue;
				if (precache) return nullptr;
				c = '#';
			}

			if (name == "_main")
				name = "main";

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

	const char *rvalue(SigSpec sig)
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

		strbuf.push_back(s);
		return strbuf.back().c_str();
	}

	const char *lvalue(SigSpec sig)
	{
		sigmap.apply(sig);

		if (sig.is_wire())
			return rvalue(sig);

		log_error("Can not generate lvalue for signal %s. Try running 'splice'.\n", log_signal(sig));
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
			// FIXME: $not, $pos, $neg, $slice, $concat,
			// $shl, $shr, $sshl, $sshr, $shift, $shiftx, $mem

			if (cell->type.in("$add", "$sub", "$mul", "$div", "$mod", "$and", "$or", "$xor", "$xnor"))
			{
				int width = GetSize(cell->getPort("\\Y"));
				string expr_a, expr_b, op;

				if (cell->type == "$add")  op = "+";
				if (cell->type == "$sub")  op = "-";
				if (cell->type == "$mul")  op = "*";
				if (cell->type == "$div")  op = "/";
				if (cell->type == "$mod")  op = "%";
				if (cell->type == "$and")  op = "&";
				if (cell->type == "$or")   op = "|";
				if (cell->type == "$xor")  op = "xor";
				if (cell->type == "$xnor") op = "xnor";

				if (cell->getParam("\\A_SIGNED").as_bool())
				{
					expr_a = stringf("resize(signed(%s), %d)", rvalue(cell->getPort("\\A")), width);
					expr_b = stringf("resize(signed(%s), %d)", rvalue(cell->getPort("\\B")), width);
					assignments.push_back(stringf("%s := unsigned(%s %s %s);", lvalue(cell->getPort("\\Y")), expr_a.c_str(), op.c_str(), expr_b.c_str()));
				}
				else
				{
					expr_a = stringf("resize(%s, %d)", rvalue(cell->getPort("\\A")), width);
					expr_b = stringf("resize(%s, %d)", rvalue(cell->getPort("\\B")), width);
					assignments.push_back(stringf("%s := %s %s %s;", lvalue(cell->getPort("\\Y")), expr_a.c_str(), op.c_str(), expr_b.c_str()));
				}

				continue;
			}

			if (cell->type.in("$eq", "$ne", "$eqx", "$nex", "$lt", "$le", "$ge", "$gt"))
			{
				int width = std::max(GetSize(cell->getPort("\\A")), GetSize(cell->getPort("\\B")));
				string expr_a, expr_b, op;

				if (cell->type == "$eq")  op = "=";
				if (cell->type == "$ne")  op = "!=";
				if (cell->type == "$eqx") op = "=";
				if (cell->type == "$nex") op = "!=";
				if (cell->type == "$lt")  op = "<";
				if (cell->type == "$le")  op = "<=";
				if (cell->type == "$ge")  op = ">=";
				if (cell->type == "$gt")  op = ">";

				if (cell->getParam("\\A_SIGNED").as_bool())
				{
					expr_a = stringf("resize(signed(%s), %d)", rvalue(cell->getPort("\\A")), width);
					expr_b = stringf("resize(signed(%s), %d)", rvalue(cell->getPort("\\B")), width);
				}
				else
				{
					expr_a = stringf("resize(%s, %d)", rvalue(cell->getPort("\\A")), width);
					expr_b = stringf("resize(%s, %d)", rvalue(cell->getPort("\\B")), width);
				}

				assignments.push_back(stringf("%s := resize(word1(%s %s %s), %d);", lvalue(cell->getPort("\\Y")),
						expr_a.c_str(), op.c_str(), expr_b.c_str(), GetSize(cell->getPort("\\Y"))));

				continue;
			}

			if (cell->type.in("$reduce_and", "$reduce_or", "$reduce_bool"))
			{
				int width_a = GetSize(cell->getPort("\\A"));
				int width_y = GetSize(cell->getPort("\\Y"));
				const char *expr_a = rvalue(cell->getPort("\\A"));
				const char *expr_y = lvalue(cell->getPort("\\Y"));
				string expr;

				if (cell->type == "$reduce_and")  expr = stringf("%s == !0ub%d_0", expr_a, width_a);
				if (cell->type == "$reduce_or")   expr = stringf("%s != 0ub%d_0", expr_a, width_a);
				if (cell->type == "$reduce_bool") expr = stringf("%s != 0ub%d_0", expr_a, width_a);

				assignments.push_back(stringf("%s := resize(word1(%s), %d);", expr_y, expr.c_str(), width_y));
				continue;
			}

			if (cell->type.in("$reduce_xor", "$reduce_xnor"))
			{
				int width_y = GetSize(cell->getPort("\\Y"));
				const char *expr_y = lvalue(cell->getPort("\\Y"));
				string expr;

				for (auto bit : cell->getPort("\\A")) {
					if (!expr.empty())
						expr += " xor ";
					expr += rvalue(bit);
				}

				if (cell->type == "$reduce_xnor")
					expr = "!(" + expr + ")";

				assignments.push_back(stringf("%s := resize(%s, %d);", expr_y, expr.c_str(), width_y));
				continue;
			}

			if (cell->type.in("$logic_and", "$logic_or"))
			{
				int width_a = GetSize(cell->getPort("\\A"));
				int width_b = GetSize(cell->getPort("\\B"));
				int width_y = GetSize(cell->getPort("\\Y"));

				string expr_a = stringf("(%s != 0ub%d_0)", rvalue(cell->getPort("\\A")), width_a);
				string expr_b = stringf("(%s != 0ub%d_0)", rvalue(cell->getPort("\\B")), width_b);
				const char *expr_y = lvalue(cell->getPort("\\Y"));

				string expr;
				if (cell->type == "$logic_and") expr = expr_a + " & " + expr_b;
				if (cell->type == "$logic_or")  expr = expr_a + " | " + expr_b;

				assignments.push_back(stringf("%s := resize(word1(%s), %d);", expr_y, expr.c_str(), width_y));
				continue;
			}

			if (cell->type.in("$logic_not"))
			{
				int width_a = GetSize(cell->getPort("\\A"));
				int width_y = GetSize(cell->getPort("\\Y"));

				string expr_a = stringf("(%s != 0ub%d_0)", rvalue(cell->getPort("\\A")), width_a);
				const char *expr_y = lvalue(cell->getPort("\\Y"));

				assignments.push_back(stringf("%s := resize(word1(%s), %d);", expr_y, expr_a.c_str(), width_y));
				continue;
			}

			if (cell->type.in("$mux", "$pmux"))
			{
				int width = GetSize(cell->getPort("\\Y"));
				SigSpec sig_a = cell->getPort("\\A");
				SigSpec sig_b = cell->getPort("\\B");
				SigSpec sig_s = cell->getPort("\\S");

				string expr;
				for (int i = 0; i < GetSize(sig_s); i++)
					expr += stringf("bool(%s) ? %s : ", rvalue(sig_s[i]), rvalue(sig_b.extract(i*width, width)));
				expr += rvalue(sig_a);

				assignments.push_back(stringf("%s := %s;", lvalue(cell->getPort("\\Y")), expr.c_str()));
				continue;
			}

			if (cell->type == "$dff")
			{
				// FIXME: use init property
				assignments.push_back(stringf("next(%s) := %s;", lvalue(cell->getPort("\\Q")), rvalue(cell->getPort("\\D"))));
				continue;
			}

			// FIXME: $_BUF_, $_NOT_, $_AND_, $_NAND_, $_OR_, $_NOR_,
			// $_XOR_, $_XNOR_, $_MUX_, $_AOI3_, $_OAI3_, $_AOI4_, $_OAI4_ 

			if (cell->type[0] == '$')
				log_error("Found currently unsupported cell type %s (%s.%s).\n", log_id(cell->type), log_id(module), log_id(cell));

			f << stringf("    %s : %s;\n", cid(cell->name), cid(cell->type));

			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					assignments.push_back(stringf("%s := %s.%s;", lvalue(conn.second), cid(cell->name), cid(conn.first)));
				else
					assignments.push_back(stringf("%s.%s := %s;", cid(cell->name), cid(conn.first), rvalue(conn.second)));
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
