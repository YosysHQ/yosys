/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
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
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "kernel/consteval.h"
#include "kernel/log.h"
#include <sstream>
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void proc_memwr(RTLIL::Module *mod, RTLIL::Process *proc, dict<IdString, int> &next_priority)
{
	for (auto sr : proc->syncs)
	{
		for (auto memwr : sr->mem_write_actions) {
			RTLIL::Cell *cell = mod->addCell(NEW_ID, ID($memwr));
			cell->attributes = memwr.attributes;
			cell->setParam(ID::MEMID, Const(memwr.memid.str()));
			cell->setParam(ID::ABITS, GetSize(memwr.address));
			cell->setParam(ID::WIDTH, GetSize(memwr.data));
			cell->setParam(ID::PRIORITY, next_priority[memwr.memid]++);
			cell->setPort(ID::ADDR, memwr.address);
			cell->setPort(ID::DATA, memwr.data);
			SigSpec enable = memwr.enable;
			for (auto sr2 : proc->syncs) {
				if (sr2->type == RTLIL::SyncType::ST0) {
					log_assert(sr2->mem_write_actions.empty());
					enable = mod->Mux(NEW_ID, Const(State::S0, GetSize(enable)), enable, sr2->signal);
				} else if (sr2->type == RTLIL::SyncType::ST1) {
					log_assert(sr2->mem_write_actions.empty());
					enable = mod->Mux(NEW_ID, enable, Const(State::S0, GetSize(enable)), sr2->signal);
				}
			}
			cell->setPort(ID::EN, enable);
			if (sr->type == RTLIL::SyncType::STa) {
				cell->setPort(ID::CLK, State::Sx);
				cell->setParam(ID::CLK_ENABLE, State::S0);
				cell->setParam(ID::CLK_POLARITY, State::Sx);
			} else if (sr->type == RTLIL::SyncType::STp) {
				cell->setPort(ID::CLK, sr->signal);
				cell->setParam(ID::CLK_ENABLE, State::S1);
				cell->setParam(ID::CLK_POLARITY, State::S1);
			} else if (sr->type == RTLIL::SyncType::STn) {
				cell->setPort(ID::CLK, sr->signal);
				cell->setParam(ID::CLK_ENABLE, State::S1);
				cell->setParam(ID::CLK_POLARITY, State::S0);
			} else {
				log_error("process memory write with unsupported sync type in %s.%s", log_id(mod), log_id(proc));
			}
		}
		sr->mem_write_actions.clear();
	}
}

struct ProcMemWrPass : public Pass {
	ProcMemWrPass() : Pass("proc_memwr", "extract memory writes from processes") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_memwr [selection]\n");
		log("\n");
		log("This pass converts memory writes in processes into $memwr cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing PROC_MEMWR pass (convert process memory writes to cells).\n");

		extra_args(args, 1, design);

		for (auto module : design->selected_modules()) {
			dict<IdString, int> next_priority;
			for (auto cell : module->cells()) {
				if (cell->type == ID($memwr)) {
					IdString memid = cell->parameters.at(ID::MEMID).decode_string();
					int priority = cell->parameters.at(ID::PRIORITY).as_int();
					if (priority >= next_priority[memid])
						next_priority[memid] = priority + 1;
				}
			}
			for (auto &proc_it : module->processes)
				if (design->selected(module, proc_it.second))
					proc_memwr(module, proc_it.second, next_priority);
		}
	}
} ProcMemWrPass;

PRIVATE_NAMESPACE_END

