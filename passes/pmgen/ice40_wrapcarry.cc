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

#include "passes/pmgen/ice40_wrapcarry_pm.h"

void create_ice40_wrapcarry(ice40_wrapcarry_pm &pm)
{
	auto &st = pm.st_ice40_wrapcarry;

#if 0
	log("\n");
	log("carry: %s\n", log_id(st.carry, "--"));
	log("lut:   %s\n", log_id(st.lut, "--"));
#endif

	log("  replacing SB_LUT + SB_CARRY with $__ICE40_CARRY_WRAPPER cell.\n");

	Cell *cell = pm.module->addCell(NEW_ID, "$__ICE40_CARRY_WRAPPER");
	pm.module->swap_names(cell, st.carry);

	cell->setPort("\\A", st.carry->getPort("\\I0"));
	cell->setPort("\\B", st.carry->getPort("\\I1"));
	cell->setPort("\\CI", st.carry->getPort("\\CI"));
	cell->setPort("\\CO", st.carry->getPort("\\CO"));

	cell->setPort("\\I0", st.lut->getPort("\\I0"));
	cell->setPort("\\I3", st.lut->getPort("\\I3"));
	cell->setPort("\\O", st.lut->getPort("\\O"));
	cell->setParam("\\LUT", st.lut->getParam("\\LUT_INIT"));

	pm.autoremove(st.carry);
	pm.autoremove(st.lut);
}

struct Ice40WrapCarryPass : public Pass {
	Ice40WrapCarryPass() : Pass("ice40_wrapcarry", "iCE40: wrap carries") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ice40_wrapcarry [selection]\n");
		log("\n");
		log("Wrap manually instantiated SB_CARRY cells, along with their associated SB_LUTs,\n");
		log("into an internal $__ICE40_CARRY_WRAPPER cell for preservation across technology\n");
		log("mapping.");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ICE40_WRAPCARRY pass (wrap carries).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			ice40_wrapcarry_pm(module, module->selected_cells()).run_ice40_wrapcarry(create_ice40_wrapcarry);
	}
} Ice40WrapCarryPass;

PRIVATE_NAMESPACE_END
