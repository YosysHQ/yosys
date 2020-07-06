/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019  Miodrag Milanovic <miodrag@symbioticeda.com>
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

static void handle_gbufs(Module *module)
{
	SigMap sigmap(module);

	pool<SigBit> clk_bits;
	dict<SigBit, SigBit> rewrite_bits;
	vector<pair<Cell*, SigBit>> pad_bits;

	for (auto cell : module->cells())
	{
		if (cell->type == "\\EFX_FF") {
			for (auto bit : sigmap(cell->getPort("\\CLK")))
				clk_bits.insert(bit);
		}
		if (cell->type == "\\EFX_RAM_5K") {
			for (auto bit : sigmap(cell->getPort("\\RCLK")))
				clk_bits.insert(bit);
			for (auto bit : sigmap(cell->getPort("\\WCLK")))
				clk_bits.insert(bit);
		}
	}

	for (auto wire : vector<Wire*>(module->wires()))
	{
		if (!wire->port_input)
			continue;

		for (int index = 0; index < GetSize(wire); index++)
		{
			SigBit bit(wire, index);
			SigBit canonical_bit = sigmap(bit);

			if (!clk_bits.count(canonical_bit))
				continue;

			Cell *c = module->addCell(NEW_ID, "\\EFX_GBUFCE");
			SigBit new_bit = module->addWire(NEW_ID);
			c->setParam("\\CE_POLARITY", State::S1);
			c->setPort("\\O", new_bit);
			c->setPort("\\CE", State::S1);
			pad_bits.push_back(make_pair(c, bit));
			rewrite_bits[canonical_bit] = new_bit;

			log("Added %s cell %s for port bit %s.\n", log_id(c->type), log_id(c), log_signal(bit));
		}
	}

	auto rewrite_function = [&](SigSpec &s) {
		for (auto &bit : s) {
			SigBit canonical_bit = sigmap(bit);
			if (rewrite_bits.count(canonical_bit))
				bit = rewrite_bits.at(canonical_bit);
		}
	};

	module->rewrite_sigspecs(rewrite_function);

	for (auto &it : pad_bits)
		it.first->setPort("\\I", it.second);
}

struct EfinixGbufPass : public Pass {
	EfinixGbufPass() : Pass("efinix_gbuf", "Efinix: insert global clock buffers") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    efinix_gbuf [options] [selection]\n");
		log("\n");
		log("Add Efinix global clock buffers to top module as needed.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing efinix_gbuf pass (insert global clock buffers).\n");
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);

		Module *module = design->top_module();

		if (module == nullptr)
			log_cmd_error("No top module found.\n");

		handle_gbufs(module);		
	}
} EfinixGbufPass;

PRIVATE_NAMESPACE_END
