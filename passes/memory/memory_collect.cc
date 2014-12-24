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

#include "kernel/register.h"
#include "kernel/log.h"
#include <sstream>
#include <algorithm>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool memcells_cmp(RTLIL::Cell *a, RTLIL::Cell *b)
{
	if (a->type == "$memrd" && b->type == "$memrd")
		return a->name < b->name;
	if (a->type == "$memrd" || b->type == "$memrd")
		return (a->type == "$memrd") < (b->type == "$memrd");
	return a->parameters.at("\\PRIORITY").as_int() < b->parameters.at("\\PRIORITY").as_int();
}

void handle_memory(RTLIL::Module *module, RTLIL::Memory *memory)
{
	log("Collecting $memrd and $memwr for memory `%s' in module `%s':\n",
			memory->name.c_str(), module->name.c_str());

	int addr_bits = 0;
	while ((1 << addr_bits) < memory->size)
		addr_bits++;

	int wr_ports = 0;
	RTLIL::SigSpec sig_wr_clk;
	RTLIL::SigSpec sig_wr_clk_enable;
	RTLIL::SigSpec sig_wr_clk_polarity;
	RTLIL::SigSpec sig_wr_addr;
	RTLIL::SigSpec sig_wr_data;
	RTLIL::SigSpec sig_wr_en;

	int rd_ports = 0;
	RTLIL::SigSpec sig_rd_clk;
	RTLIL::SigSpec sig_rd_clk_enable;
	RTLIL::SigSpec sig_rd_clk_polarity;
	RTLIL::SigSpec sig_rd_transparent;
	RTLIL::SigSpec sig_rd_addr;
	RTLIL::SigSpec sig_rd_data;

	std::vector<RTLIL::Cell*> del_cells;
	std::vector<RTLIL::Cell*> memcells;

	for (auto &cell_it : module->cells_) {
		RTLIL::Cell *cell = cell_it.second;
		if ((cell->type == "$memwr" || cell->type == "$memrd") && memory->name == cell->parameters["\\MEMID"].decode_string())
			memcells.push_back(cell);
	}

	std::sort(memcells.begin(), memcells.end(), memcells_cmp);

	for (auto cell : memcells)
	{
		if (cell->type == "$memwr" && memory->name == cell->parameters["\\MEMID"].decode_string())
		{
			wr_ports++;
			del_cells.push_back(cell);

			RTLIL::SigSpec clk = cell->getPort("\\CLK");
			RTLIL::SigSpec clk_enable = RTLIL::SigSpec(cell->parameters["\\CLK_ENABLE"]);
			RTLIL::SigSpec clk_polarity = RTLIL::SigSpec(cell->parameters["\\CLK_POLARITY"]);
			RTLIL::SigSpec addr = cell->getPort("\\ADDR");
			RTLIL::SigSpec data = cell->getPort("\\DATA");
			RTLIL::SigSpec en = cell->getPort("\\EN");

			clk.extend_u0(1, false);
			clk_enable.extend_u0(1, false);
			clk_polarity.extend_u0(1, false);
			addr.extend_u0(addr_bits, false);
			data.extend_u0(memory->width, false);
			en.extend_u0(memory->width, false);

			sig_wr_clk.append(clk);
			sig_wr_clk_enable.append(clk_enable);
			sig_wr_clk_polarity.append(clk_polarity);
			sig_wr_addr.append(addr);
			sig_wr_data.append(data);
			sig_wr_en.append(en);
		}

		if (cell->type == "$memrd" && memory->name == cell->parameters["\\MEMID"].decode_string())
		{
			rd_ports++;
			del_cells.push_back(cell);

			RTLIL::SigSpec clk = cell->getPort("\\CLK");
			RTLIL::SigSpec clk_enable = RTLIL::SigSpec(cell->parameters["\\CLK_ENABLE"]);
			RTLIL::SigSpec clk_polarity = RTLIL::SigSpec(cell->parameters["\\CLK_POLARITY"]);
			RTLIL::SigSpec transparent = RTLIL::SigSpec(cell->parameters["\\TRANSPARENT"]);
			RTLIL::SigSpec addr = cell->getPort("\\ADDR");
			RTLIL::SigSpec data = cell->getPort("\\DATA");

			clk.extend_u0(1, false);
			clk_enable.extend_u0(1, false);
			clk_polarity.extend_u0(1, false);
			transparent.extend_u0(1, false);
			addr.extend_u0(addr_bits, false);
			data.extend_u0(memory->width, false);

			sig_rd_clk.append(clk);
			sig_rd_clk_enable.append(clk_enable);
			sig_rd_clk_polarity.append(clk_polarity);
			sig_rd_transparent.append(transparent);
			sig_rd_addr.append(addr);
			sig_rd_data.append(data);
		}
	}

	std::stringstream sstr;
	sstr << "$mem$" << memory->name.str() << "$" << (autoidx++);

	RTLIL::Cell *mem = module->addCell(sstr.str(), "$mem");
	mem->parameters["\\MEMID"] = RTLIL::Const(memory->name.str());
	mem->parameters["\\WIDTH"] = RTLIL::Const(memory->width);
	mem->parameters["\\OFFSET"] = RTLIL::Const(memory->start_offset);
	mem->parameters["\\SIZE"] = RTLIL::Const(memory->size);
	mem->parameters["\\ABITS"] = RTLIL::Const(addr_bits);

	log_assert(sig_wr_clk.size() == wr_ports);
	log_assert(sig_wr_clk_enable.size() == wr_ports && sig_wr_clk_enable.is_fully_const());
	log_assert(sig_wr_clk_polarity.size() == wr_ports && sig_wr_clk_polarity.is_fully_const());
	log_assert(sig_wr_addr.size() == wr_ports * addr_bits);
	log_assert(sig_wr_data.size() == wr_ports * memory->width);
	log_assert(sig_wr_en.size() == wr_ports * memory->width);

	mem->parameters["\\WR_PORTS"] = RTLIL::Const(wr_ports);
	mem->parameters["\\WR_CLK_ENABLE"] = wr_ports ? sig_wr_clk_enable.as_const() : RTLIL::Const(0, 0);
	mem->parameters["\\WR_CLK_POLARITY"] = wr_ports ? sig_wr_clk_polarity.as_const() : RTLIL::Const(0, 0);

	mem->setPort("\\WR_CLK", sig_wr_clk);
	mem->setPort("\\WR_ADDR", sig_wr_addr);
	mem->setPort("\\WR_DATA", sig_wr_data);
	mem->setPort("\\WR_EN", sig_wr_en);

	log_assert(sig_rd_clk.size() == rd_ports);
	log_assert(sig_rd_clk_enable.size() == rd_ports && sig_rd_clk_enable.is_fully_const());
	log_assert(sig_rd_clk_polarity.size() == rd_ports && sig_rd_clk_polarity.is_fully_const());
	log_assert(sig_rd_addr.size() == rd_ports * addr_bits);
	log_assert(sig_rd_data.size() == rd_ports * memory->width);

	mem->parameters["\\RD_PORTS"] = RTLIL::Const(rd_ports);
	mem->parameters["\\RD_CLK_ENABLE"] = rd_ports ? sig_rd_clk_enable.as_const() : RTLIL::Const(0, 0);
	mem->parameters["\\RD_CLK_POLARITY"] = rd_ports ? sig_rd_clk_polarity.as_const() : RTLIL::Const(0, 0);
	mem->parameters["\\RD_TRANSPARENT"] = rd_ports ? sig_rd_transparent.as_const() : RTLIL::Const(0, 0);

	mem->setPort("\\RD_CLK", sig_rd_clk);
	mem->setPort("\\RD_ADDR", sig_rd_addr);
	mem->setPort("\\RD_DATA", sig_rd_data);

	for (auto c : del_cells)
		module->remove(c);
}

static void handle_module(RTLIL::Design *design, RTLIL::Module *module)
{
	std::vector<RTLIL::IdString> delme;
	for (auto &mem_it : module->memories)
		if (design->selected(module, mem_it.second)) {
			handle_memory(module, mem_it.second);
			delme.push_back(mem_it.first);
		}
	for (auto &it : delme) {
		delete module->memories.at(it);
		module->memories.erase(it);
	}
}

struct MemoryCollectPass : public Pass {
	MemoryCollectPass() : Pass("memory_collect", "creating multi-port memory cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_collect [selection]\n");
		log("\n");
		log("This pass collects memories and memory ports and creates generic multiport\n");
		log("memory cells.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		log_header("Executing MEMORY_COLLECT pass (generating $mem cells).\n");
		extra_args(args, 1, design);
		for (auto &mod_it : design->modules_)
			if (design->selected(mod_it.second))
				handle_module(design, mod_it.second);
	}
} MemoryCollectPass;
 
PRIVATE_NAMESPACE_END
