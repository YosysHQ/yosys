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
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static std::string hicell_celltype, hicell_portname;
static std::string locell_celltype, locell_portname;
static bool singleton_mode;

static RTLIL::Module *module;
static RTLIL::SigBit last_hi, last_lo;

void hilomap_worker(RTLIL::SigSpec &sig)
{
	for (auto &bit : sig) {
		if (bit == RTLIL::State::S1 && !hicell_celltype.empty()) {
			if (!singleton_mode || last_hi == RTLIL::State::Sm) {
				last_hi = module->addWire(NEW_ID);
				RTLIL::Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(hicell_celltype));
				cell->setPort(RTLIL::escape_id(hicell_portname), last_hi);
			}
			bit = last_hi;
		}
		if (bit == RTLIL::State::S0 && !locell_celltype.empty()) {
			if (!singleton_mode || last_lo == RTLIL::State::Sm) {
				last_lo = module->addWire(NEW_ID);
				RTLIL::Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(locell_celltype));
				cell->setPort(RTLIL::escape_id(locell_portname), last_lo);
			}
			bit = last_lo;
		}
	}
}

struct HilomapPass : public Pass {
	HilomapPass() : Pass("hilomap", "technology mapping of constant hi- and/or lo-drivers") { }
	virtual void help()
	{
		log("\n");
		log("    hilomap [options] [selection]\n");
		log("\n");
		log("Map constants to 'tielo' and 'tiehi' driver cells.\n");
		log("\n");
		log("    -hicell <celltype> <portname>\n");
		log("        Replace constant hi bits with this cell.\n");
		log("\n");
		log("    -locell <celltype> <portname>\n");
		log("        Replace constant lo bits with this cell.\n");
		log("\n");
		log("    -singleton\n");
		log("        Create only one hi/lo cell and connect all constant bits\n");
		log("        to that cell. Per default a separate cell is created for\n");
		log("        each constant bit.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing HILOMAP pass (mapping to constant drivers).\n");

		hicell_celltype = std::string();
		hicell_portname = std::string();
		locell_celltype = std::string();
		locell_portname = std::string();
		singleton_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-hicell" && argidx+2 < args.size()) {
				hicell_celltype = args[++argidx];
				hicell_portname = args[++argidx];
				continue;
			}
			if (args[argidx] == "-locell" && argidx+2 < args.size()) {
				locell_celltype = args[++argidx];
				locell_portname = args[++argidx];
				continue;
			}
			if (args[argidx] == "-singleton") {
				singleton_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &it : design->modules_)
		{
			module = it.second;

			if (!design->selected(module))
				continue;

			last_hi = RTLIL::State::Sm;
			last_lo = RTLIL::State::Sm;

			module->rewrite_sigspecs(hilomap_worker);
		}
	}
} HilomapPass;

PRIVATE_NAMESPACE_END
