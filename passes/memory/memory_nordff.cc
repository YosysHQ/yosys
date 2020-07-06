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

struct MemoryNordffPass : public Pass {
	MemoryNordffPass() : Pass("memory_nordff", "extract read port FFs from memories") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_nordff [options] [selection]\n");
		log("\n");
		log("This pass extracts FFs from memory read ports. This results in a netlist\n");
		log("similar to what one would get from calling memory_dff with -nordff.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing MEMORY_NORDFF pass (extracting $dff cells from $mem).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-nordff" || args[argidx] == "-wr_only") {
			// 	flag_wr_only = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : vector<Cell*>(module->selected_cells()))
		{
			if (cell->type != "$mem")
				continue;

			int rd_ports = cell->getParam("\\RD_PORTS").as_int();
			int abits = cell->getParam("\\ABITS").as_int();
			int width = cell->getParam("\\WIDTH").as_int();

			SigSpec rd_addr = cell->getPort("\\RD_ADDR");
			SigSpec rd_data = cell->getPort("\\RD_DATA");
			SigSpec rd_clk = cell->getPort("\\RD_CLK");
			SigSpec rd_en = cell->getPort("\\RD_EN");
			Const rd_clk_enable = cell->getParam("\\RD_CLK_ENABLE");
			Const rd_clk_polarity = cell->getParam("\\RD_CLK_POLARITY");

			for (int i = 0; i < rd_ports; i++)
			{
				bool clk_enable = rd_clk_enable[i] == State::S1;

				if (clk_enable)
				{
					bool clk_polarity = cell->getParam("\\RD_CLK_POLARITY")[i] == State::S1;
					bool transparent = cell->getParam("\\RD_TRANSPARENT")[i] == State::S1;

					SigSpec clk = cell->getPort("\\RD_CLK")[i] ;
					SigSpec en = cell->getPort("\\RD_EN")[i];
					Cell *c;

					if (transparent)
					{
						SigSpec sig_q = module->addWire(NEW_ID, abits);
						SigSpec sig_d = rd_addr.extract(abits * i, abits);
						rd_addr.replace(abits * i, sig_q);
						if (en != State::S1)
							sig_d = module->Mux(NEW_ID, sig_q, sig_d, en);
						c = module->addDff(NEW_ID, clk, sig_d, sig_q, clk_polarity);
					}
					else
					{
						SigSpec sig_d = module->addWire(NEW_ID, width);
						SigSpec sig_q = rd_data.extract(width * i, width);
						rd_data.replace(width *i, sig_d);
						if (en != State::S1)
							sig_d = module->Mux(NEW_ID, sig_q, sig_d, en);
						c = module->addDff(NEW_ID, clk, sig_d, sig_q, clk_polarity);
					}

					log("Extracted %s FF from read port %d of %s.%s: %s\n", transparent ? "addr" : "data",
							i, log_id(module), log_id(cell), log_id(c));
				}

				rd_en[i] = State::S1;
				rd_clk[i] = State::S0;
				rd_clk_enable[i] = State::S0;
				rd_clk_polarity[i] = State::S1;
			}

			cell->setPort("\\RD_ADDR", rd_addr);
			cell->setPort("\\RD_DATA", rd_data);
			cell->setPort("\\RD_CLK", rd_clk);
			cell->setPort("\\RD_EN", rd_en);
			cell->setParam("\\RD_CLK_ENABLE", rd_clk_enable);
			cell->setParam("\\RD_CLK_POLARITY", rd_clk_polarity);
		}
	}
} MemoryNordffPass;

PRIVATE_NAMESPACE_END
