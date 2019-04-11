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

struct Pmux2ShiftxPass : public Pass {
	Pmux2ShiftxPass() : Pass("pmux2shiftx", "transform $pmux cells to $shiftx cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    pmux2shiftx [selection]\n");
		log("\n");
		log("This pass transforms $pmux cells to $shiftx cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing PMUX2SHIFTX pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : module->selected_cells())
		{
			if (cell->type != "$pmux")
				continue;

			// Create a new encoder, out of a $pmux, that takes
			// the existing pmux's 'S' input and transforms it
			// back into a binary value
			RTLIL::SigSpec shiftx_a;
			RTLIL::SigSpec pmux_s;

			int s_width = cell->getParam("\\S_WIDTH").as_int();
			if (!cell->getPort("\\A").is_fully_undef()) {
				++s_width;
				shiftx_a.append(cell->getPort("\\A"));
				pmux_s.append(module->Not(NEW_ID, module->ReduceOr(NEW_ID, cell->getPort("\\S"))));
			}
			const int clog2width = ceil(log2(s_width));

			RTLIL::SigSpec pmux_b;
			for (int i = s_width-1; i >= 0; i--)
				pmux_b.append(RTLIL::Const(i, clog2width));
			shiftx_a.append(cell->getPort("\\B"));
			pmux_s.append(cell->getPort("\\S"));

			RTLIL::SigSpec pmux_y = module->addWire(NEW_ID, clog2width);
			module->addPmux(NEW_ID, RTLIL::Const(RTLIL::Sx, clog2width), pmux_b, pmux_s, pmux_y);
			module->addShiftx(NEW_ID, shiftx_a, pmux_y, cell->getPort("\\Y"));
			module->remove(cell);
		}
	}
} Pmux2ShiftxPass;

PRIVATE_NAMESPACE_END
