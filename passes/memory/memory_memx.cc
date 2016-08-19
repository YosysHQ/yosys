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
#include <set>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryMemxPass : public Pass {
	MemoryMemxPass() : Pass("memory_memx", "emulate vlog sim behavior for mem ports") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_memx [selection]\n");
		log("\n");
		log("This pass adds additional circuitry that emulates the Verilog simulation\n");
		log("behavior for out-of-bounds memory reads and writes.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		log_header(design, "Executing MEMORY_MEMX pass (converting $mem cells to logic and flip-flops).\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules())
		{
			vector<Cell*> mem_port_cells;

			for (auto cell : module->selected_cells())
				if (cell->type.in("$memrd", "$memwr"))
					mem_port_cells.push_back(cell);

			for (auto cell : mem_port_cells)
			{
				IdString memid = cell->getParam("\\MEMID").decode_string();
				RTLIL::Memory *mem = module->memories.at(memid);

				int lowest_addr = mem->start_offset;
				int highest_addr = mem->start_offset + mem->size - 1;

				SigSpec addr = cell->getPort("\\ADDR");
				addr.extend_u0(32);

				SigSpec addr_ok = module->Nex(NEW_ID, module->ReduceXor(NEW_ID, addr), module->ReduceXor(NEW_ID, {addr, State::S1}));
				if (lowest_addr != 0)
					addr_ok = module->LogicAnd(NEW_ID, addr_ok, module->Ge(NEW_ID, addr, lowest_addr));
				addr_ok = module->LogicAnd(NEW_ID, addr_ok, module->Le(NEW_ID, addr, highest_addr));

				if (cell->type == "$memrd")
				{
					if (cell->getParam("\\CLK_ENABLE").as_bool())
						log_error("Cell %s.%s (%s) has an enabled clock. Clocked $memrd cells are not supported by memory_memx!\n",
								log_id(module), log_id(cell), log_id(cell->type));

					SigSpec rdata = cell->getPort("\\DATA");
					Wire *raw_rdata = module->addWire(NEW_ID, GetSize(rdata));
					module->addMux(NEW_ID, SigSpec(State::Sx, GetSize(rdata)), raw_rdata, addr_ok, rdata);
					cell->setPort("\\DATA", raw_rdata);
				}

				if (cell->type == "$memwr")
				{
					SigSpec en = cell->getPort("\\EN");
					en = module->And(NEW_ID, en, addr_ok.repeat(GetSize(en)));
					cell->setPort("\\EN", en);
				}
			}
		}
	}
} MemoryMemxPass;

PRIVATE_NAMESPACE_END
