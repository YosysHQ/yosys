/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018  whitequark <whitequark@whitequark.org>
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
#include "kernel/modtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static bool evaluate_lut(SigMap &sigmap, RTLIL::Cell *lut, dict<SigBit, bool> inputs)
{
	SigSpec lut_input = sigmap(lut->getPort("\\A"));
	int lut_width = lut->getParam("\\WIDTH").as_int();
	Const lut_table = lut->getParam("\\LUT");
	int lut_index = 0;

	for (int i = 0; i < lut_width; i++)
	{
		SigBit input = sigmap(lut_input[i]);
		if (inputs.count(input))
		{
			lut_index |= inputs[input] << i;
		}
		else
		{
			lut_index |= SigSpec(lut_input[i]).as_bool() << i;
		}
	}

	return lut_table.extract(lut_index).as_int();
}

static void run_lut_opts(Module *module)
{
	ModIndex index(module);
	SigMap sigmap(module);

	log("Discovering LUTs.\n");

	pool<RTLIL::Cell*> luts;
	dict<RTLIL::Cell*, int> luts_arity;
	for (auto cell : module->selected_cells())
	{
		if (cell->type == "$lut")
		{
			int lut_width = cell->getParam("\\WIDTH").as_int();
			SigSpec lut_input = cell->getPort("\\A");
			int lut_arity = 0;

			for (auto &bit : lut_input)
			{
				if (bit.wire)
					lut_arity++;
			}

			log("Found $lut cell %s.%s with WIDTH=%d implementing %d-LUT.\n", log_id(module), log_id(cell), lut_width, lut_arity);
			luts.insert(cell);
			luts_arity[cell] = lut_arity;
		}
	}

	log("\n");
	log("Combining LUTs.\n");

	pool<RTLIL::Cell*> worklist = luts;
	while (worklist.size())
	{
		auto lutA = worklist.pop();
		SigSpec lutA_input = sigmap(lutA->getPort("\\A"));
		SigSpec lutA_output = sigmap(lutA->getPort("\\Y")[0]);
		int lutA_width = lutA->getParam("\\WIDTH").as_int();
		int lutA_arity = luts_arity[lutA];

		auto lutA_output_ports = index.query_ports(lutA->getPort("\\Y"));
		if (lutA_output_ports.size() != 2)
			continue;

		for (auto port : lutA_output_ports)
		{
			if (port.cell == lutA)
				continue;

			if (luts.count(port.cell))
			{
				auto lutB = port.cell;
				SigSpec lutB_input = sigmap(lutB->getPort("\\A"));
				SigSpec lutB_output = sigmap(lutB->getPort("\\Y")[0]);
				int lutB_width = lutB->getParam("\\WIDTH").as_int();
				int lutB_arity = luts_arity[lutB];

				log("Found %s.%s (cell A) feeding %s.%s (cell B).\n", log_id(module), log_id(lutA), log_id(module), log_id(lutB));

				pool<SigBit> lutA_inputs;
				pool<SigBit> lutB_inputs;
				for (auto &bit : lutA_input)
				{
					if (bit.wire)
						lutA_inputs.insert(sigmap(bit));
				}
				for (auto &bit : lutB_input)
				{
					if(bit.wire)
						lutB_inputs.insert(sigmap(bit));
				}

				pool<SigBit> common_inputs;
				for (auto &bit : lutA_inputs)
				{
					if (lutB_inputs.count(bit))
						common_inputs.insert(bit);
				}

				int lutM_arity = lutA_arity + lutB_arity - 1 - common_inputs.size();
				log("  Cell A is a %d-LUT. Cell B is a %d-LUT. Cells share %zu input(s) and can be merged into one %d-LUT.\n", lutA_arity, lutB_arity, common_inputs.size(), lutM_arity);

				int combine = -1;
				if (combine == -1)
				{
					if (lutM_arity > lutA_width)
					{
						log("  Not combining LUTs into cell A (combined LUT too wide).\n");
					}
					else if (lutB->get_bool_attribute("\\lut_keep"))
					{
						log("  Not combining LUTs into cell A (cell B has attribute \\lut_keep).\n");
					}
					else combine = 0;
				}
				if (combine == -1)
				{
					if (lutM_arity > lutB_width)
					{
						log("  Not combining LUTs into cell B (combined LUT too wide).\n");
					}
					else if (lutA->get_bool_attribute("\\lut_keep"))
					{
						log("  Not combining LUTs into cell B (cell A has attribute \\lut_keep).\n");
					}
					else combine = 1;
				}

				RTLIL::Cell *lutM, *lutR;
				pool<SigBit> lutM_inputs, lutR_inputs;
				if (combine == 0)
				{
					log("  Combining LUTs into cell A.\n");
					lutM = lutA;
					lutM_inputs = lutA_inputs;
					lutR = lutB;
					lutR_inputs = lutB_inputs;
				}
				else if (combine == 1)
				{
					log("  Combining LUTs into cell B.\n");
					lutM = lutB;
					lutM_inputs = lutB_inputs;
					lutR = lutA;
					lutR_inputs = lutA_inputs;
				}
				else
				{
					log("  Cannot combine LUTs.\n");
					continue;
				}

				pool<SigBit> lutR_unique;
				for (auto &bit : lutR_inputs)
				{
					if (!common_inputs.count(bit) && bit != lutA_output)
						lutR_unique.insert(bit);
				}

				int lutM_width = lutM->getParam("\\WIDTH").as_int();
				SigSpec lutM_input = sigmap(lutM->getPort("\\A"));
				std::vector<SigBit> lutM_new_inputs;
				for (int i = 0; i < lutM_width; i++)
				{
					if ((!lutM_input[i].wire || sigmap(lutM_input[i]) == lutA_output) && lutR_unique.size())
					{
						SigBit new_input = lutR_unique.pop();
						log("    Connecting input %d as %s.\n", i, log_signal(new_input));
						lutM_new_inputs.push_back(new_input);
					}
					else if (sigmap(lutM_input[i]) == lutA_output)
					{
						log("    Disconnecting input %d.\n", i);
						lutM_new_inputs.push_back(SigBit());
					}
					else
					{
						log("    Leaving input %d as %s.\n", i, log_signal(lutM_input[i]));
						lutM_new_inputs.push_back(lutM_input[i]);
					}
				}
				log_assert(lutR_unique.size() == 0);

				RTLIL::Const lutM_new_table(State::Sx, 1 << lutM_width);
				for (int eval = 0; eval < 1 << lutM_width; eval++)
				{
					dict<SigBit, bool> eval_inputs;
					for (size_t i = 0; i < lutM_new_inputs.size(); i++)
					{
						eval_inputs[lutM_new_inputs[i]] = (eval >> i) & 1;
					}
					eval_inputs[lutA_output] = evaluate_lut(sigmap, lutA, eval_inputs);
					lutM_new_table[eval] = (RTLIL::State) evaluate_lut(sigmap, lutB, eval_inputs);
				}

				log("  Old truth table: %s.\n", lutM->getParam("\\LUT").as_string().c_str());
				log("  New truth table: %s.\n", lutM_new_table.as_string().c_str());

				lutM->setParam("\\LUT", lutM_new_table);
				lutM->setPort("\\A", lutM_new_inputs);
				lutM->setPort("\\Y", lutB_output);

				luts_arity[lutM] = lutM_arity;
				luts.erase(lutR);
				luts_arity.erase(lutR);
				lutR->module->remove(lutR);

				worklist.insert(lutM);
				worklist.erase(lutR);
			}
		}
	}
}

struct OptLutPass : public Pass {
	OptLutPass() : Pass("opt_lut", "optimize LUT cells") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    opt_lut [options] [selection]\n");
		log("\n");
		log("This pass combines cascaded $lut cells with unused inputs.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing OPT_LUT pass (optimize LUTs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-???") {
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			run_lut_opts(module);
	}
} OptLutPass;

PRIVATE_NAMESPACE_END
