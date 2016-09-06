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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void assertpmux_worker(Cell *pmux, bool flag_noinit)
{
	Module *module = pmux->module;

	log("Adding assert for $pmux cell %s.%s.\n", log_id(module), log_id(pmux));

	int swidth = pmux->getParam("\\S_WIDTH").as_int();
	int cntbits = ceil_log2(swidth+1);

	SigSpec sel = pmux->getPort("\\S");
	SigSpec cnt(State::S0, cntbits);

	for (int i = 0; i < swidth; i++)
		cnt = module->Add(NEW_ID, cnt, sel[i]);

	SigSpec assert_a = module->Le(NEW_ID, cnt, SigSpec(1, cntbits));
	SigSpec assert_en = State::S1;

	if (flag_noinit) {
		Cell *initstate_cell = module->addCell(NEW_ID, "$initstate");
		SigSpec initstate_sig = module->addWire(NEW_ID);
		initstate_cell->setPort("\\Y", initstate_sig);
		assert_en = module->LogicNot(NEW_ID, initstate_sig);
	}

	Cell *assert_cell = module->addAssert(NEW_ID, assert_a, assert_en);

	if (pmux->attributes.count("\\src") != 0)
		assert_cell->attributes["\\src"] = pmux->attributes.at("\\src");
}

struct AssertpmuxPass : public Pass {
	AssertpmuxPass() : Pass("assertpmux", "convert internal signals to module ports") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    assertpmux [options] [selection]\n");
		log("\n");
		log("This command adds asserts to the design that assert that all parallel muxes\n");
		log("($pmux cells) have a maximum of one of their inputs enable at any time.\n");
		log("\n");
		log("    -noinit\n");
		log("        do not enforce the pmux condition during the init state\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_noinit = false;

		log_header(design, "Executing ASSERTPMUX pass (add asserts for $pmux cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-noinit") {
				flag_noinit = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			vector<Cell*> pmux_cells;

			for (auto cell : module->selected_cells())
				if (cell->type == "$pmux")
					pmux_cells.push_back(cell);

			for (auto cell : pmux_cells)
				assertpmux_worker(cell, flag_noinit);
		}

	}
} AssertpmuxPass;

PRIVATE_NAMESPACE_END
