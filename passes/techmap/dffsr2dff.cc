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

void dffsr_worker(SigMap &sigmap, Module *module, Cell *cell)
{
	if (cell->type == "$dffsr")
	{
		int width = cell->getParam("\\WIDTH").as_int();
		bool setpol = cell->getParam("\\SET_POLARITY").as_bool();
		bool clrpol = cell->getParam("\\CLR_POLARITY").as_bool();

		SigBit setunused = setpol ? State::S0 : State::S1;
		SigBit clrunused = clrpol ? State::S0 : State::S1;

		SigSpec setsig = sigmap(cell->getPort("\\SET"));
		SigSpec clrsig = sigmap(cell->getPort("\\CLR"));

		Const reset_val;
		SigSpec setctrl, clrctrl;

		for (int i = 0; i < width; i++)
		{
			SigBit setbit = setsig[i], clrbit = clrsig[i];

			if (setbit == setunused) {
				clrctrl.append(clrbit);
				reset_val.bits.push_back(State::S0);
				continue;
			}

			if (clrbit == clrunused) {
				setctrl.append(setbit);
				reset_val.bits.push_back(State::S1);
				continue;
			}

			return;
		}

		setctrl.sort_and_unify();
		clrctrl.sort_and_unify();

		if (GetSize(setctrl) > 1 || GetSize(clrctrl) > 1)
			return;

		if (GetSize(setctrl) == 0 && GetSize(clrctrl) == 0)
			return;

		if (GetSize(setctrl) == 1 && GetSize(clrctrl) == 1) {
			if (setpol != clrpol)
				return;
			if (setctrl != clrctrl)
				return;
		}

		log("Converting %s cell %s.%s to $adff.\n", log_id(cell->type), log_id(module), log_id(cell));

		if (GetSize(setctrl) == 1) {
			cell->setPort("\\ARST", setctrl);
			cell->setParam("\\ARST_POLARITY", setpol);
		} else {
			cell->setPort("\\ARST", clrctrl);
			cell->setParam("\\ARST_POLARITY", clrpol);
		}

		cell->type = "$adff";
		cell->unsetPort("\\SET");
		cell->unsetPort("\\CLR");
		cell->setParam("\\ARST_VALUE", reset_val);
		cell->unsetParam("\\SET_POLARITY");
		cell->unsetParam("\\CLR_POLARITY");

		return;
	}

	if (cell->type.in("$_DFFSR_NNN_", "$_DFFSR_NNP_", "$_DFFSR_NPN_", "$_DFFSR_NPP_",
			"$_DFFSR_PNN_", "$_DFFSR_PNP_", "$_DFFSR_PPN_", "$_DFFSR_PPP_"))
	{
		char clkpol = cell->type.c_str()[8];
		char setpol = cell->type.c_str()[9];
		char clrpol = cell->type.c_str()[10];

		SigBit setbit = sigmap(cell->getPort("\\S"));
		SigBit clrbit = sigmap(cell->getPort("\\R"));

		SigBit setunused = setpol == 'P' ? State::S0 : State::S1;
		SigBit clrunused = clrpol == 'P' ? State::S0 : State::S1;

		IdString oldtype = cell->type;

		if (setbit == setunused) {
			cell->type = stringf("$_DFF_%c%c0_", clkpol, clrpol);
			cell->unsetPort("\\S");
			goto converted_gate;
		}

		if (clrbit == clrunused) {
			cell->type = stringf("$_DFF_%c%c1_", clkpol, setpol);
			cell->setPort("\\R", cell->getPort("\\S"));
			cell->unsetPort("\\S");
			goto converted_gate;
		}

		return;

	converted_gate:
		log("Converting %s cell %s.%s to %s.\n", log_id(oldtype), log_id(module), log_id(cell), log_id(cell->type));
		return;
	}
}

void adff_worker(SigMap &sigmap, Module *module, Cell *cell)
{
	if (cell->type == "$adff")
	{
		bool rstpol = cell->getParam("\\ARST_POLARITY").as_bool();
		SigBit rstunused = rstpol ? State::S0 : State::S1;
		SigSpec rstsig = sigmap(cell->getPort("\\ARST"));

		if (rstsig != rstunused)
			return;

		log("Converting %s cell %s.%s to $dff.\n", log_id(cell->type), log_id(module), log_id(cell));

		cell->type = "$dff";
		cell->unsetPort("\\ARST");
		cell->unsetParam("\\ARST_VALUE");
		cell->unsetParam("\\ARST_POLARITY");

		return;
	}

	if (cell->type.in("$_DFF_NN0_", "$_DFF_NN1_", "$_DFF_NP0_", "$_DFF_NP1_",
			"$_DFF_PN0_", "$_DFF_PN1_", "$_DFF_PP0_", "$_DFF_PP1_"))
	{
		char clkpol = cell->type.c_str()[6];
		char rstpol = cell->type.c_str()[7];

		SigBit rstbit = sigmap(cell->getPort("\\R"));
		SigBit rstunused = rstpol == 'P' ? State::S0 : State::S1;

		if (rstbit != rstunused)
			return;

		IdString newtype = stringf("$_DFF_%c_", clkpol);
		log("Converting %s cell %s.%s to %s.\n", log_id(cell->type), log_id(module), log_id(cell), log_id(newtype));

		cell->type = newtype;
		cell->unsetPort("\\R");

		return;
	}
}

struct Dffsr2dffPass : public Pass {
	Dffsr2dffPass() : Pass("dffsr2dff", "convert DFFSR cells to simpler FF cell types") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dffsr2dff [options] [selection]\n");
		log("\n");
		log("This pass converts DFFSR cells ($dffsr, $_DFFSR_???_) and ADFF cells ($adff,\n");
		log("$_DFF_???_) to simpler FF cell types when any of the set/reset inputs is unused.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing DFFSR2DFF pass (mapping DFFSR cells to simpler FFs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-v") {
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			SigMap sigmap(module);
			for (auto cell : module->selected_cells()) {
				dffsr_worker(sigmap, module, cell);
				adff_worker(sigmap, module, cell);
			}
		}
	}
} Dffsr2dffPass;

PRIVATE_NAMESPACE_END
