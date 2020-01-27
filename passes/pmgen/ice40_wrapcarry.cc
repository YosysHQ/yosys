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

#include "passes/pmgen/ice40_wrapcarry_pm.h"

void create_ice40_wrapcarry(ice40_wrapcarry_pm &pm)
{
	auto &st = pm.st_ice40_wrapcarry;

#if 0
	log("\n");
	log("carry: %s\n", log_id(st.carry, "--"));
	log("lut:   %s\n", log_id(st.lut, "--"));
#endif

	log("  replacing SB_LUT + SB_CARRY with $__ICE40_CARRY_WRAPPER cell.\n");

	Cell *cell = pm.module->addCell(NEW_ID, "$__ICE40_CARRY_WRAPPER");
	pm.module->swap_names(cell, st.carry);

	cell->setPort("\\A", st.carry->getPort("\\I0"));
	cell->setPort("\\B", st.carry->getPort("\\I1"));
	auto CI = st.carry->getPort("\\CI");
	cell->setPort("\\CI", CI);
	cell->setPort("\\CO", st.carry->getPort("\\CO"));

	cell->setPort("\\I0", st.lut->getPort("\\I0"));
	auto I3 = st.lut->getPort("\\I3");
	if (pm.sigmap(CI) == pm.sigmap(I3)) {
		cell->setParam("\\I3_IS_CI", State::S1);
		I3 = State::Sx;
	}
	else
		cell->setParam("\\I3_IS_CI", State::S0);
	cell->setPort("\\I3", I3);
	cell->setPort("\\O", st.lut->getPort("\\O"));
	cell->setParam("\\LUT", st.lut->getParam("\\LUT_INIT"));

	for (const auto &a : st.carry->attributes)
		cell->attributes[stringf("\\SB_CARRY.%s", a.first.c_str())] = a.second;
	for (const auto &a : st.lut->attributes)
		cell->attributes[stringf("\\SB_LUT4.%s", a.first.c_str())] = a.second;
	cell->attributes[ID(SB_LUT4.name)] = Const(st.lut->name.str());
	if (st.carry->get_bool_attribute(ID::keep) || st.lut->get_bool_attribute(ID::keep))
		cell->attributes[ID::keep] = true;

	pm.autoremove(st.carry);
	pm.autoremove(st.lut);
}

struct Ice40WrapCarryPass : public Pass {
	Ice40WrapCarryPass() : Pass("ice40_wrapcarry", "iCE40: wrap carries") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ice40_wrapcarry [selection]\n");
		log("\n");
		log("Wrap manually instantiated SB_CARRY cells, along with their associated SB_LUT4s,\n");
		log("into an internal $__ICE40_CARRY_WRAPPER cell for preservation across technology\n");
		log("mapping.\n");
		log("\n");
		log("Attributes on both cells will have their names prefixed with 'SB_CARRY.' or\n");
		log("'SB_LUT4.' and attached to the wrapping cell.\n");
		log("A (* keep *) attribute on either cell will be logically OR-ed together.\n");
		log("\n");
		log("    -unwrap\n");
		log("        unwrap $__ICE40_CARRY_WRAPPER cells back into SB_CARRYs and SB_LUT4s,\n");
		log("        including restoring their attributes.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool unwrap = false;

		log_header(design, "Executing ICE40_WRAPCARRY pass (wrap carries).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-unwrap") {
				unwrap = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			if (!unwrap)
				ice40_wrapcarry_pm(module, module->selected_cells()).run_ice40_wrapcarry(create_ice40_wrapcarry);
			else {
				for (auto cell : module->selected_cells()) {
					if (cell->type != ID($__ICE40_CARRY_WRAPPER))
						continue;

					auto carry = module->addCell(NEW_ID, ID(SB_CARRY));
					carry->setPort(ID(I0), cell->getPort(ID(A)));
					carry->setPort(ID(I1), cell->getPort(ID(B)));
					carry->setPort(ID(CI), cell->getPort(ID(CI)));
					carry->setPort(ID(CO), cell->getPort(ID(CO)));
					module->swap_names(carry, cell);
					auto lut_name = cell->attributes.at(ID(SB_LUT4.name), Const(NEW_ID.str())).decode_string();
					auto lut = module->addCell(lut_name, ID($lut));
					lut->setParam(ID(WIDTH), 4);
					lut->setParam(ID(LUT), cell->getParam(ID(LUT)));
					auto I3 = cell->getPort(cell->getParam(ID(I3_IS_CI)).as_bool() ? ID(CI) : ID(I3));
					lut->setPort(ID(A), { I3, cell->getPort(ID(B)), cell->getPort(ID(A)), cell->getPort(ID(I0)) });
					lut->setPort(ID(Y), cell->getPort(ID(O)));

					Const src;
					for (const auto &a : cell->attributes)
						if (a.first.begins_with("\\SB_CARRY.\\"))
							carry->attributes[a.first.c_str() + strlen("\\SB_CARRY.")] = a.second;
						else if (a.first.begins_with("\\SB_LUT4.\\"))
							lut->attributes[a.first.c_str() + strlen("\\SB_LUT4.")] = a.second;
						else if (a.first == ID(src))
							src = a.second;
						else if (a.first.in(ID(SB_LUT4.name), ID::keep, ID(module_not_derived)))
							continue;
						else
							log_abort();

					if (!src.empty()) {
						carry->attributes.insert(std::make_pair(ID(src), src));
						lut->attributes.insert(std::make_pair(ID(src), src));
					}

					module->remove(cell);
				}
			}
		}
	}
} Ice40WrapCarryPass;

PRIVATE_NAMESPACE_END
