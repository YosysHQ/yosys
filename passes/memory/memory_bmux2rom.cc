/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Marcelina Kościelnicka <mwk@0x04.net>
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
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryBmux2RomPass : public Pass {
	MemoryBmux2RomPass() : Pass("memory_bmux2rom", "convert muxes to ROMs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_bmux2rom [options] [selection]\n");
		log("\n");
		log("This pass converts $bmux cells with constant A input to ROMs.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing MEMORY_BMUX2ROM pass (converting muxes to ROMs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				if (cell->type != ID($bmux))
					continue;

				SigSpec sig_a = cell->getPort(ID::A);
				if (!sig_a.is_fully_const())
					continue;

				int abits = cell->getParam(ID::S_WIDTH).as_int();
				int width = cell->getParam(ID::WIDTH).as_int();
				if (abits < 3)
					continue;

				// Ok, let's do it.
				Mem mem(module, NEW_ID, width, 0, 1 << abits);
				mem.attributes = cell->attributes;

				MemInit init;
				init.addr = 0;
				init.data = sig_a.as_const();
				init.en = Const(State::S1, width);
				mem.inits.push_back(std::move(init));

				MemRd rd;
				rd.addr = cell->getPort(ID::S);
				rd.data = cell->getPort(ID::Y);
				rd.init_value = Const(State::Sx, width);
				rd.arst_value = Const(State::Sx, width);
				rd.srst_value = Const(State::Sx, width);
				mem.rd_ports.push_back(std::move(rd));

				mem.emit();
				module->remove(cell);
			}
		}
	}
} MemoryBmux2RomPass;

PRIVATE_NAMESPACE_END
