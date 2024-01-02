/*
 * Copyright 2020-2022 F4PGA Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 */

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#define MODE_BITS_REGISTER_INPUTS_ID 92
#define MODE_BITS_OUTPUT_SELECT_START_ID 81
#define MODE_BITS_OUTPUT_SELECT_WIDTH 3

// ============================================================================

struct QlDspIORegs : public Pass {
	SigMap sigmap;

	// ..........................................

	QlDspIORegs() : Pass("ql_dsp_io_regs", "change types of QL_DSP2 depending on configuration") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ql_dsp_io_regs [options] [selection]\n");
		log("\n");
		log("This pass looks for QL_DSP2 cells and changes their cell type depending on their\n");
		log("configuration.\n");
	}

	void execute(std::vector<std::string> a_Args, RTLIL::Design *a_Design) override
	{
		log_header(a_Design, "Executing QL_DSP_IO_REGS pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < a_Args.size(); argidx++) {
			break;
		}
		extra_args(a_Args, argidx, a_Design);

		for (auto module : a_Design->selected_modules()) {
			ql_dsp_io_regs_pass(module);
		}
	}

	void ql_dsp_io_regs_pass(RTLIL::Module *module)
	{
		static const std::vector<IdString> ports2del_mult = {ID(load_acc), ID(subtract), ID(acc_fir), ID(dly_b),
														ID(saturate_enable), ID(shift_right), ID(round)};
		static const std::vector<IdString> ports2del_mult_acc = {ID(acc_fir), ID(dly_b)};


		sigmap.set(module);

		for (auto cell : module->cells()) {
			if (cell->type != ID(QL_DSP2))
				continue;

			// If the cell does not have the "is_inferred" attribute set
			// then don't touch it.
			if (!cell->get_bool_attribute(ID(is_inferred)))
				continue;

			// Get DSP configuration
			for (auto cfg_port : {ID(register_inputs), ID(output_select)})
			if (!cell->hasPort(cfg_port) || !sigmap(cell->getPort(cfg_port)).is_fully_const())
				log_error("Missing or non-constant '%s' port on DSP cell %s\n",
						  log_id(cfg_port), log_id(cell));
			int reg_in_i = sigmap(cell->getPort(ID(register_inputs))).as_int();
			int out_sel_i = sigmap(cell->getPort(ID(output_select))).as_int();

			// Get the feedback port
			if (!cell->hasPort(ID(feedback)))
				log_error("Missing 'feedback' port on %s", log_id(cell));
			SigSpec feedback = sigmap(cell->getPort(ID(feedback)));

			// Check the top two bits on 'feedback' to be constant zero.
			// That's what we are expecting from inference.
			if (feedback.extract(1, 2) != SigSpec(0, 2))
				log_error("Unexpected feedback configuration on %s\n", log_id(cell));

			// Build new type name
			std::string new_type = "\\QL_DSP2_MULT";

			// Decide if we should be deleting the clock port
			bool del_clk = true;

			switch (out_sel_i) {
				case 1:
				case 2:
				case 3:
				case 5:
				case 7:
					del_clk = false;
					new_type += "ACC";
					break;
				default:
					break;
			}

			if (reg_in_i) {
				del_clk = false;
				new_type += "_REGIN";
			}

			if (out_sel_i > 3) {
				del_clk = false;
				new_type += "_REGOUT";
			}

			// Set new type name
			cell->type = RTLIL::IdString(new_type);

			std::vector<std::string> ports2del;

			if (del_clk)
				cell->unsetPort(ID(clk));

			switch (out_sel_i) {
			case 0:
			case 4:
			case 6:
				for (auto port : ports2del_mult)
					cell->unsetPort(port);
				break;
			case 1:
			case 2:
			case 3:
			case 5:
			case 7:
				for (auto port : ports2del_mult_acc)
					cell->unsetPort(port);
				break;
			}
		}
	}
} QlDspIORegs;

PRIVATE_NAMESPACE_END
