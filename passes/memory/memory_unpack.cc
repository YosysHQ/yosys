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

	RTLIL::IdString mem_name = RTLIL::escape_id(memory->parameters.at(ID::MEMID).decode_string());

	while (module->memories.count(mem_name) != 0)
		mem_name = mem_name.str() + stringf("_%d", autoidx++);

	RTLIL::Memory *mem = new RTLIL::Memory;
	mem->name = mem_name;
	mem->width = memory->parameters.at(ID::WIDTH).as_int();
	mem->start_offset = memory->parameters.at(ID::OFFSET).as_int();
	mem->size = memory->parameters.at(ID::SIZE).as_int();
	module->memories[mem_name] = mem;

	int abits = memory->parameters.at(ID::ABITS).as_int();
	int num_rd_ports = memory->parameters.at(ID::RD_PORTS).as_int();
	int num_wr_ports = memory->parameters.at(ID::WR_PORTS).as_int();

	for (int i = 0; i < num_rd_ports; i++)
	{
		RTLIL::Cell *cell = module->addCell(NEW_ID, ID($memrd));
		cell->parameters[ID::MEMID] = mem_name.str();
		cell->parameters[ID::ABITS] = memory->parameters.at(ID::ABITS);
		cell->parameters[ID::WIDTH] = memory->parameters.at(ID::WIDTH);
		cell->parameters[ID::CLK_ENABLE] = RTLIL::SigSpec(memory->parameters.at(ID::RD_CLK_ENABLE)).extract(i, 1).as_const();
		cell->parameters[ID::CLK_POLARITY] = RTLIL::SigSpec(memory->parameters.at(ID::RD_CLK_POLARITY)).extract(i, 1).as_const();
		cell->parameters[ID::TRANSPARENT] = RTLIL::SigSpec(memory->parameters.at(ID::RD_TRANSPARENT)).extract(i, 1).as_const();
		cell->setPort(ID::CLK, memory->getPort(ID::RD_CLK).extract(i, 1));
		cell->setPort(ID::EN, memory->getPort(ID::RD_EN).extract(i, 1));
		cell->setPort(ID::ADDR, memory->getPort(ID::RD_ADDR).extract(i*abits, abits));
		cell->setPort(ID::DATA, memory->getPort(ID::RD_DATA).extract(i*mem->width, mem->width));
	}

	for (int i = 0; i < num_wr_ports; i++)
	{
		RTLIL::Cell *cell = module->addCell(NEW_ID, ID($memwr));
		cell->parameters[ID::MEMID] = mem_name.str();
		cell->parameters[ID::ABITS] = memory->parameters.at(ID::ABITS);
		cell->parameters[ID::WIDTH] = memory->parameters.at(ID::WIDTH);
		cell->parameters[ID::CLK_ENABLE] = RTLIL::SigSpec(memory->parameters.at(ID::WR_CLK_ENABLE)).extract(i, 1).as_const();
		cell->parameters[ID::CLK_POLARITY] = RTLIL::SigSpec(memory->parameters.at(ID::WR_CLK_POLARITY)).extract(i, 1).as_const();
		cell->parameters[ID::PRIORITY] = i;
		cell->setPort(ID::CLK, memory->getPort(ID::WR_CLK).extract(i, 1));
		cell->setPort(ID::EN, memory->getPort(ID::WR_EN).extract(i*mem->width, mem->width));
		cell->setPort(ID::ADDR, memory->getPort(ID::WR_ADDR).extract(i*abits, abits));
		cell->setPort(ID::DATA, memory->getPort(ID::WR_DATA).extract(i*mem->width, mem->width));
	}

	Const initval = memory->parameters.at(ID::INIT);
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
			last_init_cell->parameters[ID::WORDS] = last_init_cell->parameters[ID::WORDS].as_int() + 1;
			last_init_data.append(val);
			last_init_addr++;
		} else {
			if (last_init_cell)
				last_init_cell->setPort(ID::DATA, last_init_data);
			RTLIL::Cell *cell = module->addCell(NEW_ID, ID($meminit));
			cell->parameters[ID::MEMID] = mem_name.str();
			cell->parameters[ID::ABITS] = memory->parameters.at(ID::ABITS);
			cell->parameters[ID::WIDTH] = memory->parameters.at(ID::WIDTH);
			cell->parameters[ID::WORDS] = 1;
			cell->parameters[ID::PRIORITY] = i/mem->width;
			cell->setPort(ID::ADDR, SigSpec(i/mem->width, abits));
			last_init_cell = cell;
			last_init_addr = i/mem->width;
			last_init_data = val;
		}
	}

	if (last_init_cell)
		last_init_cell->setPort(ID::DATA, last_init_data);

	module->remove(memory);
}

void handle_module(RTLIL::Design *design, RTLIL::Module *module)
{
	std::vector<RTLIL::IdString> memcells;
	for (auto cell : module->cells())
		if (cell->type == ID($mem) && design->selected(module, cell))
			memcells.push_back(cell->name);
	for (auto &it : memcells)
		handle_memory(module, module->cell(it));
}

struct MemoryUnpackPass : public Pass {
	MemoryUnpackPass() : Pass("memory_unpack", "unpack multi-port memory cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_unpack [selection]\n");
		log("\n");
		log("This pass converts the multi-port $mem memory cells into individual $memrd and\n");
		log("$memwr cells. It is the counterpart to the memory_collect pass.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing MEMORY_UNPACK pass (generating $memrd/$memwr cells form $mem cells).\n");
		extra_args(args, 1, design);
		for (auto module : design->selected_modules())
			handle_module(design, module);
	}
} MemoryUnpackPass;

PRIVATE_NAMESPACE_END
