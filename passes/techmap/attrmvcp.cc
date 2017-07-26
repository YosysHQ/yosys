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

struct AttrmvcpPass : public Pass {
	AttrmvcpPass() : Pass("attrmvcp", "move or copy attributes from wires to driving cells") { }
	virtual void help()
	{
		log("\n");
		log("    attrmvcp [options] [selection]\n");
		log("\n");
		log("Move or copy attributes on wires to the cells driving them.\n");
		log("\n");
		log("    -copy\n");
		log("        By default, attributes are moved. This will only add\n");
		log("        the attribute to the cell, without removing it from\n");
		log("        the wire.\n");
		log("\n");
		log("    -purge\n");
		log("        If no selected cell consumes the attribute, then it is\n");
		log("        left on the wire by default. This option will cause the\n");
		log("        attribute to be removed from the wire, even if no selected\n");
		log("        cell takes it.\n");
		log("\n");
		log("    -driven\n");
		log("        By default, attriburtes are moved to the cell driving the\n");
		log("        wire. With this option set it will be moved to the cell\n");
		log("        driven by the wire instead.\n");
		log("\n");
		log("    -attr <attrname>\n");
		log("        Move or copy this attribute. This option can be used\n");
		log("        multiple times.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing ATTRMVCP pass (move or copy attributes).\n");

		bool copy_mode = false;
		bool driven_mode = false;
		bool purge_mode = false;
		pool<IdString> attrnames;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-copy") {
				copy_mode = true;
				continue;
			}
			if (arg == "-driven") {
				driven_mode = true;
				continue;
			}
			if (arg == "-purge") {
				purge_mode = true;
				continue;
			}
			if (arg == "-attr" && argidx+1 < args.size()) {
				attrnames.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			dict<SigBit, pool<Cell*>> net2cells;
			SigMap sigmap(module);

			for (auto cell : module->selected_cells())
			for (auto &conn : cell->connections())
			{
				if (driven_mode) {
					if (cell->input(conn.first))
						for (auto bit : sigmap(conn.second))
							net2cells[bit].insert(cell);
				} else {
					if (cell->output(conn.first))
						for (auto bit : sigmap(conn.second))
							net2cells[bit].insert(cell);
				}
			}

			for (auto wire : module->selected_wires())
			{
				dict<IdString, Const> new_attributes;

				for (auto attr : wire->attributes)
				{
					bool did_something = false;

					if (!attrnames.count(attr.first)) {
						new_attributes[attr.first] = attr.second;
						continue;
					}

					for (auto bit : sigmap(wire))
						if (net2cells.count(bit))
							for (auto cell : net2cells.at(bit)) {
								log("Moving attribute %s=%s from %s.%s to %s.%s.\n", log_id(attr.first), log_const(attr.second),
										log_id(module), log_id(wire), log_id(module), log_id(cell));
								cell->attributes[attr.first] = attr.second;
								did_something = true;
							}

					if (!purge_mode && !did_something)
						new_attributes[attr.first] = attr.second;
				}

				if (!copy_mode)
					wire->attributes.swap(new_attributes);
			}
		}
	}
} AttrmvcpPass;

PRIVATE_NAMESPACE_END
