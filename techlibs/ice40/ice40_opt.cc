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

static SigBit get_bit_or_zero(const SigSpec &sig)
{
	if (GetSize(sig) == 0)
		return State::S0;
	return sig[0];
}

static void run_ice40_opts(Module *module)
{
	pool<SigBit> optimized_co;
	vector<Cell*> sb_lut_cells;
	SigMap sigmap(module);

	for (auto cell : module->selected_cells())
	{
		if (!cell->type.in("\\SB_LUT4", "\\SB_CARRY", "$__ICE40_CARRY_WRAPPER"))
			continue;
		if (cell->has_keep_attr())
			continue;

		if (cell->type == "\\SB_LUT4")
		{
			sb_lut_cells.push_back(cell);
			continue;
		}

		if (cell->type == "\\SB_CARRY")
		{
			SigSpec non_const_inputs, replacement_output;
			int count_zeros = 0, count_ones = 0;

			SigBit inbit[3] = {
				get_bit_or_zero(cell->getPort("\\I0")),
				get_bit_or_zero(cell->getPort("\\I1")),
				get_bit_or_zero(cell->getPort("\\CI"))
			};
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
				optimized_co.insert(sigmap(cell->getPort("\\CO")[0]));
				module->connect(cell->getPort("\\CO")[0], replacement_output);
				module->design->scratchpad_set_bool("opt.did_something", true);
				log("Optimized away SB_CARRY cell %s.%s: CO=%s\n",
						log_id(module), log_id(cell), log_signal(replacement_output));
				module->remove(cell);
			}
			continue;
		}

		if (cell->type == "$__ICE40_CARRY_WRAPPER")
		{
			SigSpec non_const_inputs, replacement_output;
			int count_zeros = 0, count_ones = 0;

			SigBit inbit[3] = {
				cell->getPort("\\A"),
				cell->getPort("\\B"),
				cell->getPort("\\CI")
			};
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
				optimized_co.insert(sigmap(cell->getPort("\\CO")[0]));
				auto it = cell->attributes.find(ID(SB_LUT4.name));
				if (it != cell->attributes.end()) {
					module->rename(cell, it->second.decode_string());
					decltype(Cell::attributes) new_attr;
					for (const auto &a : cell->attributes)
						if (a.first.begins_with("\\SB_LUT4.\\"))
							new_attr[a.first.c_str() + strlen("\\SB_LUT4.")] = a.second;
						else if (a.first == ID(src))
							new_attr.insert(std::make_pair(a.first, a.second));
						else if (a.first.in(ID(SB_LUT4.name), ID::keep, ID(module_not_derived)))
							continue;
						else if (a.first.begins_with("\\SB_CARRY.\\"))
							continue;
						else
							log_abort();
					cell->attributes = std::move(new_attr);
				}
				module->connect(cell->getPort("\\CO")[0], replacement_output);
				module->design->scratchpad_set_bool("opt.did_something", true);
				log("Optimized $__ICE40_CARRY_WRAPPER cell back to logic (without SB_CARRY) %s.%s: CO=%s\n",
						log_id(module), log_id(cell), log_signal(replacement_output));
				cell->type = "$lut";
				auto I3 = get_bit_or_zero(cell->getPort(cell->getParam(ID(I3_IS_CI)).as_bool() ? ID(CI) : ID(I3)));
				cell->setPort("\\A", { I3, inbit[1], inbit[0], get_bit_or_zero(cell->getPort("\\I0")) });
				cell->setPort("\\Y", cell->getPort("\\O"));
				cell->unsetPort("\\B");
				cell->unsetPort("\\CI");
				cell->unsetPort("\\I0");
				cell->unsetPort("\\I3");
				cell->unsetPort("\\CO");
				cell->unsetPort("\\O");
				cell->setParam("\\WIDTH", 4);
				cell->unsetParam("\\I3_IS_CI");
			}
			continue;
		}
	}

	for (auto cell : sb_lut_cells)
	{
		SigSpec inbits;

		inbits.append(get_bit_or_zero(cell->getPort("\\I0")));
		inbits.append(get_bit_or_zero(cell->getPort("\\I1")));
		inbits.append(get_bit_or_zero(cell->getPort("\\I2")));
		inbits.append(get_bit_or_zero(cell->getPort("\\I3")));
		sigmap.apply(inbits);

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

		cell->setPort("\\A", SigSpec({
			get_bit_or_zero(cell->getPort("\\I3")),
			get_bit_or_zero(cell->getPort("\\I2")),
			get_bit_or_zero(cell->getPort("\\I1")),
			get_bit_or_zero(cell->getPort("\\I0"))
		}));
		cell->setPort("\\Y", cell->getPort("\\O")[0]);
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
	void help() YS_OVERRIDE
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
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		string opt_expr_args = "-mux_undef -undriven";

		log_header(design, "Executing ICE40_OPT pass (performing simple optimizations).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-full") {
				opt_expr_args += " -full";
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
				run_ice40_opts(module);

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
