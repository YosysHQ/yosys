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

bool did_something;

#include "passes/pmgen/peepopt_pm.h"

struct PeepoptPass : public Pass {
	PeepoptPass() : Pass("peepopt", "collection of peephole optimizers") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    peepopt [options] [selection]\n");
		log("\n");
		log("This pass applies a collection of peephole optimizers to the current design.\n");
		log("\n");
		log("This pass employs the following rules:\n");
		log("\n");
		log("   * muldiv - Replace (A*B)/B with A\n");
		log("\n");
		log("   * shiftmul - Replace A>>(B*C) with A'>>(B<<K) where C and K are constants\n");
		log("                and A' is derived from A by appropriately inserting padding\n");
		log("                into the signal. (right variant)\n");
		log("\n");
		log("                Analogously, replace A<<(B*C) with appropriate selection of\n");
		log("                output bits from A<<(B<<K). (left variant)\n");
		log("\n");
		log("   * shiftadd - Replace A>>(B+D) with (A'>>D)>>(B) where D is constant and\n");
		log("                A' is derived from A by padding or cutting inaccessible bits.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing PEEPOPT pass (run peephole optimizers).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			did_something = true;

			while (did_something)
			{
				did_something = false;

				peepopt_pm pm(module);

				pm.setup(module->selected_cells());

				pm.run_shiftadd();
				pm.run_shiftmul_right();
				pm.run_shiftmul_left();
				pm.run_muldiv();
			}
		}
	}
} PeepoptPass;

PRIVATE_NAMESPACE_END
