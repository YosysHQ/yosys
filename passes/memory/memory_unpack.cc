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

void handle_memory(RTLIL::Module *module, RTLIL::Cell *memory)
{
	log("Creating $memrd and $memwr for memory `%s' in module `%s':\n",
			memory->name.c_str(), module->name.c_str());

	RTLIL::IdString mem_name = RTLIL::escape_id(memory->parameters.at("\\MEMID").decode_string());

	while (module->memories.count(mem_name) != 0)
		mem_name = mem_name.str() + stringf("_%d", autoidx++);

	RTLIL::Memory *mem = new RTLIL::Memory;
	mem->name = mem_name;
	mem->width = memory->parameters.at("\\WIDTH").as_int();
	mem->start_offset = memory->parameters.at("\\OFFSET").as_int();
	mem->size = memory->parameters.at("\\SIZE").as_int();
	module->memories[mem_name] = mem;

	int abits = memory->parameters.at("\\ABITS").as_int();
	int num_rd_ports = memory->parameters.at("\\RD_PORTS").as_int();
	int num_wr_ports = memory->parameters.at("\\WR_PORTS").as_int();

	for (int i = 0; i < num_rd_ports; i++)
	{
		RTLIL::Cell *cell = module->addCell(NEW_ID, "$memrd");
		cell->parameters["\\MEMID"] = mem_name.str();
		cell->parameters["\\ABITS"] = memory->parameters.at("\\ABITS");
		cell->parameters["\\WIDTH"] = memory->parameters.at("\\WIDTH");
		cell->parameters["\\CLK_ENABLE"] = RTLIL::SigSpec(memory->parameters.at("\\RD_CLK_ENABLE")).extract(i, 1).as_const();
		cell->parameters["\\CLK_POLARITY"] = RTLIL::SigSpec(memory->parameters.at("\\RD_CLK_POLARITY")).extract(i, 1).as_const();
		cell->parameters["\\TRANSPARENT"] = RTLIL::SigSpec(memory->parameters.at("\\RD_TRANSPARENT")).extract(i, 1).as_const();
		cell->setPort("\\CLK", memory->getPort("\\RD_CLK").extract(i, 1));
		cell->setPort("\\EN", memory->getPort("\\RD_EN").extract(i, 1));
		cell->setPort("\\ADDR", memory->getPort("\\RD_ADDR").extract(i*abits, abits));
		cell->setPort("\\DATA", memory->getPort("\\RD_DATA").extract(i*mem->width, mem->width));
	}

	for (int i = 0; i < num_wr_ports; i++)
	{
		RTLIL::Cell *cell = module->addCell(NEW_ID, "$memwr");
		cell->parameters["\\MEMID"] = mem_name.str();
		cell->parameters["\\ABITS"] = memory->parameters.at("\\ABITS");
		cell->parameters["\\WIDTH"] = memory->parameters.at("\\WIDTH");
		cell->parameters["\\CLK_ENABLE"] = RTLIL::SigSpec(memory->parameters.at("\\WR_CLK_ENABLE")).extract(i, 1).as_const();
		cell->parameters["\\CLK_POLARITY"] = RTLIL::SigSpec(memory->parameters.at("\\WR_CLK_POLARITY")).extract(i, 1).as_const();
		cell->parameters["\\PRIORITY"] = i;
		cell->setPort("\\CLK", memory->getPort("\\WR_CLK").extract(i, 1));
		cell->setPort("\\EN", memory->getPort("\\WR_EN").extract(i*mem->width, mem->width));
		cell->setPort("\\ADDR", memory->getPort("\\WR_ADDR").extract(i*abits, abits));
		cell->setPort("\\DATA", memory->getPort("\\WR_DATA").extract(i*mem->width, mem->width));
	}

	Const initval = memory->parameters.at("\\INIT");
	RTLIL::Cell *last_init_cell = nullptr;
	SigSpec last_init_data;
	int last_init_addr=0;

	for (int i = 0; i < GetSize(initval) && i/mem->width < (1 << abits); i += mem->width) {
		Const val = initval.extract(i, mem->width, State::Sx);
		for (auto bit : val.bits)
			if (bit != State::Sx)
				goto found_non_undef_initval;
		continue;
	found_non_undef_initval:
		if (last_init_cell && last_init_addr+1 == i/mem->width) {
			last_init_cell->parameters["\\WORDS"] = last_init_cell->parameters["\\WORDS"].as_int() + 1;
			last_init_data.append(val);
			last_init_addr++;
		} else {
			if (last_init_cell)
				last_init_cell->setPort("\\DATA", last_init_data);
			RTLIL::Cell *cell = module->addCell(NEW_ID, "$meminit");
			cell->parameters["\\MEMID"] = mem_name.str();
			cell->parameters["\\ABITS"] = memory->parameters.at("\\ABITS");
			cell->parameters["\\WIDTH"] = memory->parameters.at("\\WIDTH");
			cell->parameters["\\WORDS"] = 1;
			cell->parameters["\\PRIORITY"] = i/mem->width;
			cell->setPort("\\ADDR", SigSpec(i/mem->width, abits));
			last_init_cell = cell;
			last_init_addr = i/mem->width;
			last_init_data = val;
		}
	}

	if (last_init_cell)
		last_init_cell->setPort("\\DATA", last_init_data);

	module->remove(memory);
}

void handle_module(RTLIL::Design *design, RTLIL::Module *module)
{
	std::vector<RTLIL::IdString> memcells;
	for (auto &cell_it : module->cells_)
		if (cell_it.second->type == "$mem" && design->selected(module, cell_it.second))
			memcells.push_back(cell_it.first);
	for (auto &it : memcells)
		handle_memory(module, module->cells_.at(it));
}

struct MemoryUnpackPass : public Pass {
	MemoryUnpackPass() : Pass("memory_unpack", "unpack multi-port memory cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_unpack [selection]\n");
		log("\n");
		log("This pass converts the multi-port $mem memory cells into individual $memrd and\n");
		log("$memwr cells. It is the counterpart to the memory_collect pass.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		log_header(design, "Executing MEMORY_UNPACK pass (generating $memrd/$memwr cells form $mem cells).\n");
		extra_args(args, 1, design);
		for (auto &mod_it : design->modules_)
			if (design->selected(mod_it.second))
				handle_module(design, mod_it.second);
	}
} MemoryUnpackPass;

PRIVATE_NAMESPACE_END
