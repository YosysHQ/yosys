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

int lut2mux(Cell *cell, bool word_mode)
{
	SigSpec sig_a = cell->getPort(ID::A);
	SigSpec sig_y = cell->getPort(ID::Y);
	Const lut = cell->getParam(ID::LUT);
	int count = 1;

	if (GetSize(sig_a) == 1)
	{
		if (!word_mode)
			cell->module->addMuxGate(NEW_ID2, lut.extract(0)[0], lut.extract(1)[0], sig_a, sig_y, cell->get_src_attribute()); // SILIMATE: Improve the naming
		else
			cell->module->addMux(NEW_ID2, lut.extract(0)[0], lut.extract(1)[0], sig_a, sig_y, cell->get_src_attribute()); // SILIMATE: Improve the naming
	}
	else
	{
		SigSpec sig_a_hi = sig_a[GetSize(sig_a)-1];
		SigSpec sig_a_lo = sig_a.extract(0, GetSize(sig_a)-1);
		SigSpec sig_y1 = cell->module->addWire(NEW_ID2); // SILIMATE: Improve the naming
		SigSpec sig_y2 = cell->module->addWire(NEW_ID2); // SILIMATE: Improve the naming

		Const lut1 = lut.extract(0, GetSize(lut)/2);
		Const lut2 = lut.extract(GetSize(lut)/2, GetSize(lut)/2);

		count += lut2mux(cell->module->addLut(NEW_ID2, sig_a_lo, sig_y1, lut1), word_mode); // SILIMATE: Improve the naming
		count += lut2mux(cell->module->addLut(NEW_ID2, sig_a_lo, sig_y2, lut2), word_mode); // SILIMATE: Improve the naming

		if (!word_mode)
			cell->module->addMuxGate(NEW_ID2, sig_y1, sig_y2, sig_a_hi, sig_y, cell->get_src_attribute()); // SILIMATE: Improve the naming
		else
			cell->module->addMux(NEW_ID2, sig_y1, sig_y2, sig_a_hi, sig_y, cell->get_src_attribute()); // SILIMATE: Improve the naming
	}

	cell->module->remove(cell);
	return count;
}

struct Lut2muxPass : public Pass {
	Lut2muxPass() : Pass("lut2mux", "convert $lut to $mux/$_MUX_") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    lut2mux [options] [selection]\n");
		log("\n");
		log("This pass converts $lut cells to $mux/$_MUX_ gates.\n");
		log("\n");
		log("    -word\n");
		log("        Convert $lut cells with a single input to word-level $mux gates.\n");
		log("   	   The default is to convert them to bit-level $_MUX_ gates.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing LUT2MUX pass (convert $lut to $mux/$_MUX_).\n");

		size_t argidx;
		bool word_mode = false;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-word") {
				word_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : module->selected_cells()) {
			if (cell->type == ID($lut)) {
				IdString cell_name = cell->name;
				int count = lut2mux(cell, word_mode);
				log("Converted %s.%s to %d MUX cells.\n", log_id(module), log_id(cell_name), count);
			}
		}
	}
} Lut2muxPass;

PRIVATE_NAMESPACE_END
