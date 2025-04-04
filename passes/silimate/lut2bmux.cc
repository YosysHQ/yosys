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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Lut2BmuxPass : public Pass {
	Lut2BmuxPass() : Pass("lut2bmux", "convert $lut to $bmux") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    lut2bmux [options] [selection]\n");
		log("\n");
		log("This pass converts $lut cells to $bmux cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing LUT2BMUX pass (convert $lut to $bmux).\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : module->selected_cells()) {
			if (cell->type == ID($lut)) {
				cell->type = ID($bmux);
				cell->setPort(ID::S, cell->getPort(ID::A));
				cell->setPort(ID::A, cell->getParam(ID::LUT));
				cell->unsetParam(ID::LUT);
				cell->fixup_parameters();
				log("Converted %s.%s to BMUX cell.\n", log_id(module), log_id(cell));
			}
		}
	}
} Lut2BmuxPass;

PRIVATE_NAMESPACE_END
