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
#include "passes/techmap/simplemap.h"
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void run_ice40_opts(Module *module, bool unlut_mode)
{
	pool<SigBit> optimized_co;
	vector<Cell*> sb_lut_cells;
	SigMap sigmap(module);

	for (auto cell : module->selected_cells())
	{
		if (cell->type == "\\SB_LUT4")
		{
			sb_lut_cells.push_back(cell);
			continue;
		}

		if (cell->type == "\\SB_CARRY")
		{
			SigSpec non_const_inputs, replacement_output;
			int count_zeros = 0, count_ones = 0;

			SigBit inbit[3] = {cell->getPort("\\I0"), cell->getPort("\\I1"), cell->getPort("\\CI")};
			for (int i = 0; i < 3; i++)
				if (inbit[i].wire == nullptr) {
					if (inbit[i] == State::S1)
						count_ones++;
					else
						count_zeros++;
				} else
					non_const_inputs.append(inbit[i]);

			if (count_zeros >= 2)
				replacement_output = State::S0;
			else if (count_ones >= 2)
				replacement_output = State::S1;
			else if (GetSize(non_const_inputs) == 1)
				replacement_output = non_const_inputs;

			if (GetSize(replacement_output)) {
				optimized_co.insert(sigmap(cell->getPort("\\CO")));
				module->connect(cell->getPort("\\CO"), replacement_output);
				module->design->scratchpad_set_bool("opt.did_something", true);
				log("Optimized away SB_CARRY cell %s.%s: CO=%s\n",
						log_id(module), log_id(cell), log_signal(replacement_output));
				module->remove(cell);
			}
			continue;
		}
	}

	for (auto cell : sb_lut_cells)
	{
		SigSpec inbits;

		inbits.append(cell->getPort("\\I0"));
		inbits.append(cell->getPort("\\I1"));
		inbits.append(cell->getPort("\\I2"));
		inbits.append(cell->getPort("\\I3"));
		sigmap.apply(inbits);

		if (unlut_mode)
			goto remap_lut;

		if (optimized_co.count(inbits[0])) goto remap_lut;
		if (optimized_co.count(inbits[1])) goto remap_lut;
		if (optimized_co.count(inbits[2])) goto remap_lut;
		if (optimized_co.count(inbits[3])) goto remap_lut;

		if (!sigmap(inbits).is_fully_const())
			continue;

	remap_lut:
		module->design->scratchpad_set_bool("opt.did_something", true);
		log("Mapping SB_LUT4 cell %s.%s back to logic.\n", log_id(module), log_id(cell));

		cell->type ="$lut";
		cell->setParam("\\WIDTH", 4);
		cell->setParam("\\LUT", cell->getParam("\\LUT_INIT"));
		cell->unsetParam("\\LUT_INIT");

		cell->setPort("\\A", SigSpec({cell->getPort("\\I3"), cell->getPort("\\I2"), cell->getPort("\\I1"), cell->getPort("\\I0")}));
		cell->setPort("\\Y", cell->getPort("\\O"));
		cell->unsetPort("\\I0");
		cell->unsetPort("\\I1");
		cell->unsetPort("\\I2");
		cell->unsetPort("\\I3");
		cell->unsetPort("\\O");

		cell->check();
		simplemap_lut(module, cell);
		module->remove(cell);
	}
}

struct Ice40OptPass : public Pass {
	Ice40OptPass() : Pass("ice40_opt", "iCE40: perform simple optimizations") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ice40_opt [options] [selection]\n");
		log("\n");
		log("This command executes the following script:\n");
		log("\n");
		log("    do\n");
		log("        <ice40 specific optimizations>\n");
		log("        opt_expr -mux_undef -undriven [-full]\n");
		log("        opt_merge\n");
		log("        opt_rmdff\n");
		log("        opt_clean\n");
		log("    while <changed design>\n");
		log("\n");
		log("When called with the option -unlut, this command will transform all already\n");
		log("mapped SB_LUT4 cells back to logic.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		string opt_expr_args = "-mux_undef -undriven";
		bool unlut_mode = false;

		log_header(design, "Executing ICE40_OPT pass (performing simple optimizations).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-full") {
				opt_expr_args += " -full";
				continue;
			}
			if (args[argidx] == "-unlut") {
				unlut_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		while (1)
		{
			design->scratchpad_unset("opt.did_something");

			log_header(design, "Running ICE40 specific optimizations.\n");
			for (auto module : design->selected_modules())
				run_ice40_opts(module, unlut_mode);

			Pass::call(design, "opt_expr " + opt_expr_args);
			Pass::call(design, "opt_merge");
			Pass::call(design, "opt_rmdff");
			Pass::call(design, "opt_clean");

			if (design->scratchpad_get_bool("opt.did_something") == false)
				break;

			log_header(design, "Rerunning OPT passes. (Removed registers in this run.)\n");
		}

		design->optimize();
		design->sort();
		design->check();

		log_header(design, "Finished OPT passes. (There is nothing left to do.)\n");
		log_pop();
	}
} Ice40OptPass;

PRIVATE_NAMESPACE_END
