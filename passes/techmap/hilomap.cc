/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
static std::string fullcell_celltype, fullcell_portname, fullcell_paramname;
static bool singleton_mode;
static bool multi_bit;

static RTLIL::Module *module;
static RTLIL::SigBit last_hi, last_lo;
static RTLIL::SigChunk value;

void hilomap_worker(RTLIL::SigSpec &sig)
{
	if (multi_bit && sig.is_fully_const()){
		value = module->addWire(NEW_ID, sig.size());
		RTLIL::Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(fullcell_celltype));
		cell->setParam(RTLIL::escape_id(fullcell_paramname), sig.as_const());
		cell->setPort(RTLIL::escape_id(fullcell_portname), value);
		sig = value;
	}
	else{
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
}

struct HilomapPass : public Pass {
	HilomapPass() : Pass("hilomap", "technology mapping of constant hi- and/or lo-drivers") { }
	void help() override
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
		log("    -wrap <celltype> <portname> <paramname>\n");
		log("        Replace constant bits with this cell.\n");
		log("        The value of the constant will be stored to the parameter specified.\n");
		log("\n");
		log("    -singleton\n");
		log("        Create only one hi/lo cell and connect all constant bits\n");
		log("        to that cell. Per default a separate cell is created for\n");
		log("        each constant bit.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing HILOMAP pass (mapping to constant drivers).\n");

		hicell_celltype = std::string();
		hicell_portname = std::string();
		locell_celltype = std::string();
		locell_portname = std::string();
		singleton_mode = false;
		multi_bit = false;
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
			if (args[argidx] == "-wrap" && argidx+3 < args.size()){
				fullcell_celltype = args[++argidx];
				fullcell_portname = args[++argidx];
				fullcell_paramname = args[++argidx];
				multi_bit = true;
				continue;
			}
			if (args[argidx] == "-singleton") {
				singleton_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules())
		{
			module = mod;
			last_hi = RTLIL::State::Sm;
			last_lo = RTLIL::State::Sm;

			module->rewrite_sigspecs(hilomap_worker);
		}
	}
} HilomapPass;

PRIVATE_NAMESPACE_END
