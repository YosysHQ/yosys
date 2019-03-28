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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct InsbufPass : public Pass {
	InsbufPass() : Pass("insbuf", "insert buffer cells for connected wires") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    insbuf [options] [selection]\n");
		log("\n");
		log("Insert buffer cells into the design for directly connected wires.\n");
		log("\n");
		log("    -buf <celltype> <in-portname> <out-portname>\n");
		log("        Use the given cell type instead of $_BUF_. (Notice that the next\n");
		log("        call to \"clean\" will remove all $_BUF_ in the design.)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing INSBUF pass (insert buffer cells for connected wires).\n");

		std::string celltype = "$_BUF_", in_portname = "\\A", out_portname = "\\Y";

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-buf" && argidx+3 < args.size()) {
				celltype = args[++argidx];
				in_portname = args[++argidx];
				out_portname = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			std::vector<RTLIL::SigSig> new_connections;

			for (auto &conn : module->connections())
			{
				RTLIL::SigSig new_conn;

				for (int i = 0; i < GetSize(conn.first); i++)
				{
					SigBit lhs = conn.first[i];
					SigBit rhs = conn.second[i];

					if (lhs.wire && !design->selected(module, lhs.wire)) {
						new_conn.first.append(lhs);
						new_conn.second.append(rhs);
						continue;
					}

					Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(celltype));
					cell->setPort(RTLIL::escape_id(in_portname), rhs);
					cell->setPort(RTLIL::escape_id(out_portname), lhs);
					log("Added %s.%s: %s -> %s\n", log_id(module), log_id(cell), log_signal(rhs), log_signal(lhs));
				}

				if (GetSize(new_conn.first))
					new_connections.push_back(new_conn);
			}

			module->new_connections(new_connections);
		}
	}
} InsbufPass;

PRIVATE_NAMESPACE_END
