/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2025  King Lok Chung <king.chung@manchester.ac.uk>
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
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static std::string celltype, cell_portname, cell_paramname;

static RTLIL::Module *module;
static RTLIL::SigChunk value;

void constmap_worker(RTLIL::SigSpec &sig)
{
	if (sig.is_fully_const()){
		value = module->addWire(NEW_ID, sig.size());
		RTLIL::Cell *cell = module->addCell(NEW_ID, celltype);
		cell->setParam(cell_paramname, sig.as_const());
		cell->setPort(cell_portname, value);
		sig = value;
	}
}

struct ConstmapPass : public Pass {
	ConstmapPass() : Pass("constmap", "technology mapping of coarse constant value") { }
	void help() override
	{
		log("\n");
		log("    constmap [options] [selection]\n");
		log("\n");
		log("Map constants to a driver cell.\n");
		log("\n");
		log("    -cell <celltype> <portname> <paramname>\n");
		log("        Replace constant bits with this cell.\n");
		log("        The value of the constant will be stored to the parameter specified.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing CONSTMAP pass (mapping to constant driver).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-cell" && argidx+3 < args.size()){
				celltype = RTLIL::escape_id(args[++argidx]);
				cell_portname = RTLIL::escape_id(args[++argidx]);
				cell_paramname = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);


		if (design->has(celltype)) {
			Module *existing = design->module(celltype);
			bool has_port = false;
			for (auto &p : existing->ports){
				if (p == cell_portname){
					has_port = true;
					break;
				}
			}
			if (!has_port)
				log_cmd_error("Cell type '%s' does not have port '%s'.\n", celltype.c_str(), cell_portname.c_str());

			bool has_param = false;
			for (auto &p : existing->avail_parameters){
				if (p == cell_paramname)
					has_param = true;
			}

			if (!has_param)
				log_cmd_error("Cell type '%s' does not have parameter '%s'.\n", celltype.c_str(), cell_paramname.c_str());
		}


		for (auto mod : design->selected_modules())
		{
			module = mod;
			module->rewrite_sigspecs(constmap_worker);
		}
	}
} ConstmapPass;

PRIVATE_NAMESPACE_END
