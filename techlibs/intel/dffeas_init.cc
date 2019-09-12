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

struct DffeasInitPass : public Pass {
	DffeasInitPass() : Pass("dffeas_init", "Determine the init value of dffeas cells") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    dffeas_init [selection]\n");
		log("\n");
		log("Determine the init value of dffeas cells.\n");
		log("\n");
	}

	Const dffeas_init(Const value)
	{
		if (GetSize(value) !=0 ){
			if (value[0] == State::S1)
				value = Const("high");
			else if (value[0] == State::S0)
				value = Const("low");
			else
				value = Const("dont_care");
		}

		return value;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing DETERMINE_INIT pass (determine init value for cells).\n");

		extra_args(args, args.size(), design);

		int cnt = 0;
                Const value;
		for (auto module : design->selected_modules())
		{
			for (auto cell : module->selected_cells())
			{
				if (cell->type == "\\dffeas")
				{
					cell->setParam("\\power_up", dffeas_init(cell->getParam("\\power_up")));
					cnt++;
				}
			}
		}
		log_header(design, "Updated %d dffeas cells with determined init value.\n", cnt);
	}
} DffeasInitPass;

PRIVATE_NAMESPACE_END

