/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020 QuickLogic Corp.
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

static void run_ap3_opts(Module *module)
{
	pool<SigBit> optimized_co;
	vector<Cell*> sb_lut_cells;
	SigMap sigmap(module);

	for (auto cell : module->selected_cells())
	{
		if (!cell->type.in(ID(LUT4), ID(QL_CARRY), ID($__AP3_CARRY_WRAPPER)))
			continue;
		if (cell->has_keep_attr())
			continue;

		if (cell->type == ID(LUT4))
		{
			sb_lut_cells.push_back(cell);
			continue;
		}

		if (cell->type == ID(QL_CARRY))
		{
			SigSpec non_const_inputs, replacement_output;
			int count_zeros = 0, count_ones = 0;

			SigBit inbit[3] = {
				get_bit_or_zero(cell->getPort(ID(I0))),
				get_bit_or_zero(cell->getPort(ID(I1))),
				get_bit_or_zero(cell->getPort(ID::CI))
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
				optimized_co.insert(sigmap(cell->getPort(ID::CO)[0]));
				module->connect(cell->getPort(ID::CO)[0], replacement_output);
				module->design->scratchpad_set_bool("opt.did_something", true);
				log("Optimized away QL_CARRY cell %s.%s: CO=%s\n",
						log_id(module), log_id(cell), log_signal(replacement_output));
				module->remove(cell);
			}
			continue;
		}

		if (cell->type == ID($__AP3_CARRY_WRAPPER))
		{
			SigSpec non_const_inputs, replacement_output;
			int count_zeros = 0, count_ones = 0;

			SigBit inbit[3] = {
				cell->getPort(ID::A),
				cell->getPort(ID::B),
				cell->getPort(ID::CI)
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
				optimized_co.insert(sigmap(cell->getPort(ID::CO)[0]));
				auto it = cell->attributes.find(ID(LUT4.name));
				if (it != cell->attributes.end()) {
					module->rename(cell, it->second.decode_string());
					decltype(Cell::attributes) new_attr;
					for (const auto &a : cell->attributes)
						if (a.first.begins_with("\\LUT4.\\"))
							new_attr[a.first.c_str() + strlen("\\LUT4.")] = a.second;
						else if (a.first == ID::src)
							new_attr.insert(std::make_pair(a.first, a.second));
						else if (a.first.in(ID(LUT4.name), ID::keep, ID::module_not_derived))
							continue;
						else if (a.first.begins_with("\\QL_CARRY.\\"))
							continue;
						else
							log_abort();
					cell->attributes = std::move(new_attr);
				}
				module->connect(cell->getPort(ID::CO)[0], replacement_output);
				module->design->scratchpad_set_bool("opt.did_something", true);
				log("Optimized $__AP3_CARRY_WRAPPER cell back to logic (without QL_CARRY) %s.%s: CO=%s\n",
						log_id(module), log_id(cell), log_signal(replacement_output));
				cell->type = ID($lut);
				auto I2 = get_bit_or_zero(cell->getPort(cell->getParam(ID(I2_IS_CI)).as_bool() ? ID::CI : ID(I2)));
				cell->setPort(ID::A, { get_bit_or_zero(cell->getPort(ID(I3))), I2, inbit[1], inbit[0] });
				cell->setPort(ID::Y, cell->getPort(ID::O));
				cell->unsetPort(ID::B);
				cell->unsetPort(ID::CI);
				cell->unsetPort(ID(I2));
				cell->unsetPort(ID(I3));
				cell->unsetPort(ID::CO);
				cell->unsetPort(ID::O);
				cell->setParam(ID::WIDTH, 4);
				cell->unsetParam(ID(I2_IS_CI));
			}
			continue;
		}
	}

	for (auto cell : sb_lut_cells)
	{
		SigSpec inbits;

		inbits.append(get_bit_or_zero(cell->getPort(ID(I0))));
		inbits.append(get_bit_or_zero(cell->getPort(ID(I1))));
		inbits.append(get_bit_or_zero(cell->getPort(ID(I2))));
		inbits.append(get_bit_or_zero(cell->getPort(ID(I3))));
		sigmap.apply(inbits);

		if (optimized_co.count(inbits[0])) goto remap_lut;
		if (optimized_co.count(inbits[1])) goto remap_lut;
		if (optimized_co.count(inbits[2])) goto remap_lut;
		if (optimized_co.count(inbits[3])) goto remap_lut;

		if (!sigmap(inbits).is_fully_const())
			continue;

	remap_lut:
		module->design->scratchpad_set_bool("opt.did_something", true);
		log("Mapping LUT4 cell %s.%s back to logic.\n", log_id(module), log_id(cell));

		cell->type = ID($lut);
		cell->setParam(ID::WIDTH, 4);
		cell->setParam(ID::LUT, cell->getParam(ID(INIT)));
		cell->unsetParam(ID(INIT));

		cell->setPort(ID::A, SigSpec({
			get_bit_or_zero(cell->getPort(ID(I3))),
			get_bit_or_zero(cell->getPort(ID(I2))),
			get_bit_or_zero(cell->getPort(ID(I1))),
			get_bit_or_zero(cell->getPort(ID(I0)))
		}));
		cell->setPort(ID::Y, cell->getPort(ID::O)[0]);
		cell->unsetPort(ID(I0));
		cell->unsetPort(ID(I1));
		cell->unsetPort(ID(I2));
		cell->unsetPort(ID(I3));
		cell->unsetPort(ID::O);

		cell->check();
		simplemap_lut(module, cell);
		module->remove(cell);
	}
}

struct AP3OptPass : public Pass {
	AP3OptPass() : Pass("ap3_opt", "AP3: perform simple optimizations") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ap3_opt [options] [selection]\n");
		log("\n");
		log("This command executes the following script:\n");
		log("\n");
		log("    do\n");
		log("        <AP3 specific optimizations>\n");
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

		log_header(design, "Executing ap3_opt pass (performing simple optimizations).\n");
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

			log_header(design, "Running AP3 specific optimizations.\n");
			for (auto module : design->selected_modules())
				run_ap3_opts(module);

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
} AP3OptPass;

PRIVATE_NAMESPACE_END
