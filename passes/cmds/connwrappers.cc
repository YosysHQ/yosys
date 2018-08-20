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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ConnwrappersWorker
{
	struct portdecl_t {
		// key: celltype, portname;
		std::string widthparam, signparam;
		bool is_signed;
	};

	std::set<RTLIL::IdString> decl_celltypes;
	std::map<std::pair<RTLIL::IdString, RTLIL::IdString>, portdecl_t> decls;

	void add_port(std::string celltype, std::string portname, std::string widthparam, std::string signparam)
	{
		std::pair<std::string, std::string> key(RTLIL::escape_id(celltype), RTLIL::escape_id(portname));
		decl_celltypes.insert(key.first);

		if (decls.count(key))
			log_cmd_error("Duplicate port decl: %s %s\n", celltype.c_str(), portname.c_str());

		portdecl_t decl;
		decl.widthparam = RTLIL::escape_id(widthparam);
		decl.signparam = RTLIL::escape_id(signparam);
		decl.is_signed = false;
		decls[key] = decl;
	}

	void add_port(std::string celltype, std::string portname, std::string widthparam, bool is_signed)
	{
		std::pair<std::string, std::string> key(RTLIL::escape_id(celltype), RTLIL::escape_id(portname));
		decl_celltypes.insert(key.first);

		if (decls.count(key))
			log_cmd_error("Duplicate port decl: %s %s\n", celltype.c_str(), portname.c_str());

		portdecl_t decl;
		decl.widthparam = RTLIL::escape_id(widthparam);
		decl.is_signed = is_signed;
		decls[key] = decl;
	}

	void work(RTLIL::Design *design, RTLIL::Module *module)
	{
		std::map<RTLIL::SigBit, std::pair<bool, RTLIL::SigSpec>> extend_map;
		SigMap sigmap(module);

		for (auto &it : module->cells_)
		{
			RTLIL::Cell *cell = it.second;

			if (!decl_celltypes.count(cell->type))
				continue;

			for (auto &conn : cell->connections())
			{
				std::pair<RTLIL::IdString, RTLIL::IdString> key(cell->type, conn.first);

				if (!decls.count(key))
					continue;

				portdecl_t &decl = decls.at(key);

				if (!cell->parameters.count(decl.widthparam))
					continue;

				if (!decl.signparam.empty() && !cell->parameters.count(decl.signparam))
					continue;

				int inner_width = cell->parameters.at(decl.widthparam).as_int();
				int outer_width = conn.second.size();
				bool is_signed = decl.signparam.empty() ? decl.is_signed : cell->parameters.at(decl.signparam).as_bool();

				if (inner_width >= outer_width)
					continue;

				RTLIL::SigSpec sig = sigmap(conn.second);
				extend_map[sig.extract(inner_width - 1, 1)] = std::pair<bool, RTLIL::SigSpec>(is_signed,
						sig.extract(inner_width, outer_width - inner_width));
			}
		}

		for (auto &it : module->cells_)
		{
			RTLIL::Cell *cell = it.second;

			if (!design->selected(module, cell))
				continue;

			for (auto &conn : cell->connections_)
			{
				std::vector<RTLIL::SigBit> sigbits = sigmap(conn.second).to_sigbit_vector();
				RTLIL::SigSpec old_sig;

				for (size_t i = 0; i < sigbits.size(); i++)
				{
					if (!extend_map.count(sigbits[i]))
						continue;

					bool is_signed = extend_map.at(sigbits[i]).first;
					RTLIL::SigSpec extend_sig = extend_map.at(sigbits[i]).second;

					int extend_width = 0;
					RTLIL::SigBit extend_bit = is_signed ? sigbits[i] : RTLIL::SigBit(RTLIL::State::S0);
					while (extend_width < extend_sig.size() && i + extend_width + 1 < sigbits.size() &&
							sigbits[i + extend_width + 1] == extend_bit) extend_width++;

					if (extend_width == 0)
						continue;

					if (old_sig.size() == 0)
						old_sig = conn.second;

					conn.second.replace(i+1, extend_sig.extract(0, extend_width));
					i += extend_width;
				}

				if (old_sig.size())
					log("Connected extended bits of %s.%s:%s: %s -> %s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name),
							RTLIL::id2cstr(conn.first), log_signal(old_sig), log_signal(conn.second));
			}
		}
	}
};

struct ConnwrappersPass : public Pass {
	ConnwrappersPass() : Pass("connwrappers", "match width of input-output port pairs") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    connwrappers [options] [selection]\n");
		log("\n");
		log("Wrappers are used in coarse-grain synthesis to wrap cells with smaller ports\n");
		log("in wrapper cells with a (larger) constant port size. I.e. the upper bits\n");
		log("of the wrapper output are signed/unsigned bit extended. This command uses this\n");
		log("knowledge to rewire the inputs of the driven cells to match the output of\n");
		log("the driving cell.\n");
		log("\n");
		log("    -signed <cell_type> <port_name> <width_param>\n");
		log("    -unsigned <cell_type> <port_name> <width_param>\n");
		log("        consider the specified signed/unsigned wrapper output\n");
		log("\n");
		log("    -port <cell_type> <port_name> <width_param> <sign_param>\n");
		log("        use the specified parameter to decide if signed or unsigned\n");
		log("\n");
		log("The options -signed, -unsigned, and -port can be specified multiple times.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		ConnwrappersWorker worker;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-signed" && argidx+3 < args.size()) {
				worker.add_port(args[argidx+1], args[argidx+2], args[argidx+3], true);
				argidx += 3;
				continue;
			}
			if (args[argidx] == "-unsigned" && argidx+3 < args.size()) {
				worker.add_port(args[argidx+1], args[argidx+2], args[argidx+3], false);
				argidx += 3;
				continue;
			}
			if (args[argidx] == "-port" && argidx+4 < args.size()) {
				worker.add_port(args[argidx+1], args[argidx+2], args[argidx+3], args[argidx+4]);
				argidx += 4;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		log_header(design, "Executing CONNWRAPPERS pass (connect extended ports of wrapper cells).\n");

		for (auto &mod_it : design->modules_)
			if (design->selected(mod_it.second))
				worker.work(design, mod_it.second);
	}
} ConnwrappersPass;

PRIVATE_NAMESPACE_END
