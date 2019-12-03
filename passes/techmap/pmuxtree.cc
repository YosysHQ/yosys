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

static SigSpec or_generator(Module *module, const SigSpec &sig)
{
	switch (GetSize(sig))
	{
	case 0:
		return State::S0;
	case 1:
		return sig;
	case 2:
		return module->Or(NEW_ID, sig[0], sig[1]);
	default:
		return module->ReduceOr(NEW_ID, sig);
	}
}

static SigSpec recursive_mux_generator(Module *module, const SigSpec &sig_data, const SigSpec &sig_sel, SigSpec &sig_or)
{
	if (GetSize(sig_sel) == 1) {
		sig_or.append(sig_sel);
		return sig_data;
	}

	int left_size = GetSize(sig_sel) / 2;
	int right_size = GetSize(sig_sel) - left_size;
	int stride = GetSize(sig_data) / GetSize(sig_sel);

	SigSpec left_data = sig_data.extract(0, stride*left_size);
	SigSpec right_data = sig_data.extract(stride*left_size, stride*right_size);

	SigSpec left_sel = sig_sel.extract(0, left_size);
	SigSpec right_sel = sig_sel.extract(left_size, right_size);

	SigSpec left_or, left_result, right_result;

	left_result = recursive_mux_generator(module, left_data, left_sel, left_or);
	right_result = recursive_mux_generator(module, right_data, right_sel, sig_or);
	left_or = or_generator(module, left_or);
	sig_or.append(left_or);

	return module->Mux(NEW_ID, right_result, left_result, left_or);
}

struct PmuxtreePass : public Pass {
	PmuxtreePass() : Pass("pmuxtree", "transform $pmux cells to trees of $mux cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    pmuxtree [selection]\n");
		log("\n");
		log("This pass transforms $pmux cells to trees of $mux cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing PMUXTREE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : module->selected_cells())
		{
			if (cell->type != ID($pmux))
				continue;

			SigSpec sig_data = cell->getPort(ID::B);
			SigSpec sig_sel = cell->getPort(ID(S));

			if (!cell->getPort(ID::A).is_fully_undef()) {
				sig_data.append(cell->getPort(ID::A));
				SigSpec sig_sel_or = module->ReduceOr(NEW_ID, sig_sel);
				sig_sel.append(module->Not(NEW_ID, sig_sel_or));
			}

			SigSpec result, result_or;
			result = recursive_mux_generator(module, sig_data, sig_sel, result_or);
			module->connect(cell->getPort(ID::Y), result);
			module->remove(cell);
		}
	}
} PmuxtreePass;

PRIVATE_NAMESPACE_END
