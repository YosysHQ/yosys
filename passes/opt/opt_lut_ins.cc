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

struct OptLutInsPass : public Pass {
	OptLutInsPass() : Pass("opt_lut_ins", "discard unused LUT inputs") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_lut_ins [options] [selection]\n");
		log("\n");
		log("This pass removes unused inputs from LUT cells (that is, inputs that can not\n");
		log("influence the output signal given this LUT's value).  While such LUTs cannot\n");
		log("be directly emitted by ABC, they can be a result of various post-ABC\n");
		log("transformations, such as mapping wide LUTs (not all sub-LUTs will use the\n");
		log("full set of inputs) or optimizations such as xilinx_dffopt.\n");
		log("\n");
		log("    -tech <technology>\n");
		log("        Instead of generic $lut cells, operate on LUT cells specific\n");
		log("        to the given technology.  Valid values are: xilinx, ecp5, gowin.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing OPT_LUT_INS pass (discard unused LUT inputs).\n");
		string techname;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-tech" && argidx+1 < args.size()) {
				techname = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (techname != "" && techname != "xilinx" && techname != "ecp5" && techname != "gowin")
			log_cmd_error("Unsupported technology: '%s'\n", techname.c_str());

		for (auto module : design->selected_modules())
		{
			log("Optimizing LUTs in %s.\n", log_id(module));

			std::vector<Cell *> remove_cells;
			// Gather LUTs.
			for (auto cell : module->selected_cells())
			{
				if (cell->get_bool_attribute(ID::keep))
					continue;
				Const lut;
				std::vector<SigBit> inputs;
				std::vector<SigBit> output;
				bool ignore_const = false;
				if (techname == "") {
					if (cell->type != ID($lut))
						continue;
					inputs = cell->getPort(ID::A).bits();
					output = cell->getPort(ID::Y);
					lut = cell->getParam(ID(LUT));
				} else if (techname == "xilinx" || techname == "gowin") {
					if (cell->type == ID(LUT1)) {
						inputs = {
							cell->getPort(ID(I0)),
						};
					} else if (cell->type == ID(LUT2)) {
						inputs = {
							cell->getPort(ID(I0)),
							cell->getPort(ID(I1)),
						};
					} else if (cell->type == ID(LUT3)) {
						inputs = {
							cell->getPort(ID(I0)),
							cell->getPort(ID(I1)),
							cell->getPort(ID(I2)),
						};
					} else if (cell->type == ID(LUT4)) {
						inputs = {
							cell->getPort(ID(I0)),
							cell->getPort(ID(I1)),
							cell->getPort(ID(I2)),
							cell->getPort(ID(I3)),
						};
					} else if (cell->type == ID(LUT5)) {
						inputs = {
							cell->getPort(ID(I0)),
							cell->getPort(ID(I1)),
							cell->getPort(ID(I2)),
							cell->getPort(ID(I3)),
							cell->getPort(ID(I4)),
						};
					} else if (cell->type == ID(LUT6)) {
						inputs = {
							cell->getPort(ID(I0)),
							cell->getPort(ID(I1)),
							cell->getPort(ID(I2)),
							cell->getPort(ID(I3)),
							cell->getPort(ID(I4)),
							cell->getPort(ID(I5)),
						};
					} else {
						// Not a LUT.
						continue;
					}
					lut = cell->getParam(ID(INIT));
					if (techname == "xilinx")
						output = cell->getPort(ID(O));
					else
						output = cell->getPort(ID(F));
				} else if (techname == "ecp5") {
					if (cell->type == ID(LUT4)) {
						inputs = {
							cell->getPort(ID::A),
							cell->getPort(ID::B),
							cell->getPort(ID(C)),
							cell->getPort(ID(D)),
						};
						lut = cell->getParam(ID(INIT));
						output = cell->getPort(ID(Z));
						ignore_const = true;
					} else {
						// Not a LUT.
						continue;
					}
				}
				std::vector<int> swizzle;
				std::vector<SigBit> new_inputs;
				bool doit = false;
				for (int i = 0; i < GetSize(inputs); i++) {
					SigBit input = inputs[i];
					if (!input.wire) {
						if (input.data == State::S1)
							swizzle.push_back(-2);
						else
							swizzle.push_back(-1);
						// For ECP5, smaller LUTs are
						// implemented as LUT4s with
						// extra const inputs.  Do not
						// consider that to be a reason
						// to redo a LUT.
						if (!ignore_const)
							doit = true;
					} else {
						bool redundant = true;
						for (int j = 0; j < GetSize(lut); j++) {
							if (lut[j] != lut[j ^ 1 << i])
								redundant = false;
						}
						if (redundant) {
							swizzle.push_back(-1);
							doit = true;
						} else {
							swizzle.push_back(GetSize(new_inputs));
							new_inputs.push_back(input);
						}
					}
				}
				if (!doit)
					continue;
				log("  Optimizing lut %s (%d -> %d)\n", log_id(cell), GetSize(inputs), GetSize(new_inputs));
				if (techname == "ecp5") {
					// Pad the LUT to 4 inputs, adding consts from the front.
					int extra = 4 - GetSize(new_inputs);
					log_assert(extra >= 0);
					if (extra) {
						for (int i = 0; i < extra; i++)
							new_inputs.insert(new_inputs.begin(), State::S0);
						for (auto &swz : swizzle)
							if (swz >= 0)
								swz += extra;
					}
				}
				Const new_lut(0, 1 << GetSize(new_inputs));
				for (int i = 0; i < GetSize(new_lut); i++) {
					int lidx = 0;
					for (int j = 0; j < GetSize(inputs); j++) {
						int val;
						if (swizzle[j] == -2) {
							val = 1;
						} else if (swizzle[j] == -1) {
							val = 0;
						} else {
							val = (i >> swizzle[j]) & 1;
						}
						lidx |= val << j;
					}
					new_lut[i] = lut[lidx];
				}
				// For ecp5, do not replace with a const driver — the nextpnr
				// packer requires a complete set of LUTs for wide LUT muxes.
				if (new_inputs.empty() && techname != "ecp5") {
					// const driver.
					remove_cells.push_back(cell);
					module->connect(output, new_lut[0]);
				} else {
					if (techname == "") {
						cell->setParam(ID(LUT), new_lut);
						cell->setParam(ID(WIDTH), GetSize(new_inputs));
						cell->setPort(ID::A, new_inputs);
					} else if (techname == "ecp5") {
						log_assert(GetSize(new_inputs) == 4);
						cell->setParam(ID(INIT), new_lut);
						cell->setPort(ID::A, new_inputs[0]);
						cell->setPort(ID::B, new_inputs[1]);
						cell->setPort(ID(C), new_inputs[2]);
						cell->setPort(ID(D), new_inputs[3]);
					} else {
						// xilinx, gowin
						cell->setParam(ID(INIT), new_lut);
						if (techname == "xilinx")
							log_assert(GetSize(new_inputs) <= 6);
						else
							log_assert(GetSize(new_inputs) <= 4);
						if (GetSize(new_inputs) == 1)
							cell->type = ID(LUT1);
						else if (GetSize(new_inputs) == 2)
							cell->type = ID(LUT2);
						else if (GetSize(new_inputs) == 3)
							cell->type = ID(LUT3);
						else if (GetSize(new_inputs) == 4)
							cell->type = ID(LUT4);
						else if (GetSize(new_inputs) == 5)
							cell->type = ID(LUT5);
						else if (GetSize(new_inputs) == 6)
							cell->type = ID(LUT6);
						else
							log_assert(0);
						cell->unsetPort(ID(I0));
						cell->unsetPort(ID(I1));
						cell->unsetPort(ID(I2));
						cell->unsetPort(ID(I3));
						cell->unsetPort(ID(I4));
						cell->unsetPort(ID(I5));
						cell->setPort(ID(I0), new_inputs[0]);
						if (GetSize(new_inputs) >= 2)
							cell->setPort(ID(I1), new_inputs[1]);
						if (GetSize(new_inputs) >= 3)
							cell->setPort(ID(I2), new_inputs[2]);
						if (GetSize(new_inputs) >= 4)
							cell->setPort(ID(I3), new_inputs[3]);
						if (GetSize(new_inputs) >= 5)
							cell->setPort(ID(I4), new_inputs[4]);
						if (GetSize(new_inputs) >= 6)
							cell->setPort(ID(I5), new_inputs[5]);
					}
				}
			}
			for (auto cell : remove_cells)
				module->remove(cell);
		}
	}
} XilinxDffOptPass;

PRIVATE_NAMESPACE_END

