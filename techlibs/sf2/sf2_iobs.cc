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

static void handle_iobufs(Module *module, bool clkbuf_mode)
{
	SigMap sigmap(module);

	pool<SigBit> clk_bits;
	pool<SigBit> handled_io_bits;
	dict<SigBit, SigBit> rewrite_bits;
	vector<pair<Cell*, SigBit>> pad_bits;

	for (auto cell : module->cells())
	{
		if (clkbuf_mode && cell->type == "\\SLE") {
			for (auto bit : sigmap(cell->getPort("\\CLK")))
				clk_bits.insert(bit);
		}
		if (cell->type.in("\\INBUF", "\\OUTBUF", "\\TRIBUFF", "\\BIBUF", "\\CLKBUF", "\\CLKBIBUF",
				"\\INBUF_DIFF", "\\OUTBUF_DIFF", "\\BIBUFF_DIFF", "\\TRIBUFF_DIFF", "\\CLKBUF_DIFF",
				"\\GCLKBUF", "\\GCLKBUF_DIFF", "\\GCLKBIBUF")) {
			for (auto bit : sigmap(cell->getPort("\\PAD")))
				handled_io_bits.insert(bit);
		}
	}

	for (auto wire : vector<Wire*>(module->wires()))
	{
		if (!wire->port_input && !wire->port_output)
			continue;

		for (int index = 0; index < GetSize(wire); index++)
		{
			SigBit bit(wire, index);
			SigBit canonical_bit = sigmap(bit);

			if (handled_io_bits.count(canonical_bit))
				continue;

			if (wire->port_input && wire->port_output)
				log_error("Failed to add buffer for inout port bit %s.\n", log_signal(bit));

			IdString buf_type, buf_port;

			if (wire->port_output) {
				buf_type = "\\OUTBUF";
				buf_port = "\\D";
			} else if (clkbuf_mode && clk_bits.count(canonical_bit)) {
				buf_type = "\\CLKBUF";
				buf_port = "\\Y";
			} else {
				buf_type = "\\INBUF";
				buf_port = "\\Y";
			}

			Cell *c = module->addCell(NEW_ID, buf_type);
			SigBit new_bit = module->addWire(NEW_ID);
			c->setPort(buf_port, new_bit);
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
		it.first->setPort("\\PAD", it.second);
}

static void handle_clkint(Module *module)
{
	SigMap sigmap(module);

	pool<SigBit> clk_bits;
	vector<SigBit> handled_clk_bits;

	for (auto cell : module->cells())
	{
		if (cell->type == "\\SLE") {
			for (auto bit : sigmap(cell->getPort("\\CLK")))
				clk_bits.insert(bit);
		}
		if (cell->type.in("\\CLKBUF", "\\CLKBIBUF", "\\CLKBUF_DIFF", "\\GCLKBUF", "\\GCLKBUF_DIFF", "\\GCLKBIBUF",
				"\\CLKINT", "\\CLKINT_PRESERVE", "\\GCLKINT", "\\RCLKINT", "\\RGCLKINT")) {
			for (auto bit : sigmap(cell->getPort("\\Y")))
				handled_clk_bits.push_back(bit);
		}
	}

	for (auto bit : handled_clk_bits)
		clk_bits.erase(bit);

	for (auto cell : vector<Cell*>(module->cells()))
	for (auto &conn : cell->connections())
	{
		if (!cell->output(conn.first))
			continue;

		SigSpec sig = conn.second;
		bool did_something = false;

		for (auto &bit : sig) {
			SigBit canonical_bit = sigmap(bit);
			if (clk_bits.count(canonical_bit)) {
				Cell *c = module->addCell(NEW_ID, "\\CLKINT");
				SigBit new_bit = module->addWire(NEW_ID);
				c->setPort("\\A", new_bit);
				c->setPort("\\Y", bit);
				log("Added %s cell %s for clock signal %s.\n", log_id(c->type), log_id(c), log_signal(bit));
				clk_bits.erase(canonical_bit);
				did_something = true;
				bit = new_bit;
			}
		}

		if (did_something)
			cell->setPort(conn.first, sig);
	}

	for (auto bit : clk_bits)
		log_error("Failed to insert CLKINT for clock signal %s.\n", log_signal(bit));
}

struct Sf2IobsPass : public Pass {
	Sf2IobsPass() : Pass("sf2_iobs", "SF2: insert IO buffers") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sf2_iobs [options] [selection]\n");
		log("\n");
		log("Add SF2 I/O buffers and global buffers to top module as needed.\n");
		log("\n");
		log("    -clkbuf\n");
		log("        Insert PAD->global_net clock buffers\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool clkbuf_mode = false;

		log_header(design, "Executing sf2_iobs pass (insert IO buffers).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-clkbuf") {
				clkbuf_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		Module *module = design->top_module();

		if (module == nullptr)
			log_cmd_error("No top module found.\n");

		handle_iobufs(module, clkbuf_mode);
		handle_clkint(module);
	}
} Sf2IobsPass;

PRIVATE_NAMESPACE_END
