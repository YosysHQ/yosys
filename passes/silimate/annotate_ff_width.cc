/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Stan Lee <stan@silimate.com>
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

struct AnnotateFfWidthPass : public Pass {
	AnnotateFfWidthPass() : Pass("annotate_ff_width", "annotate every flip-flop with its bit-width") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    annotate_ff_width [selection]\n");
		log("\n");
		log("Annotate every flip-flop with its width.");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ANNOTATE_FF_WIDTH pass.\n");
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
			break;
		extra_args(args, argidx, design);

		// Loop through all flip-flops and annotate with their width
		int annotated = 0;
		for (auto module : design->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;
				int width;
				if (cell->hasParam(ID::WIDTH))
					width = cell->getParam(ID::WIDTH).as_int();
				else if (cell->hasPort(ID::Q))
					width = GetSize(cell->getPort(ID::Q));
				else
					width = 1;
				cell->set_string_attribute(ID(ff_width), std::to_string(width));
				annotated++;
			}
		}
		log("Annotated %d flip-flops.\n", annotated);
	}
} AnnotateFfWidthPass;
PRIVATE_NAMESPACE_END
