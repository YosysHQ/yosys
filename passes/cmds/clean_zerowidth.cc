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

#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CleanZeroWidthPass : public Pass {
	CleanZeroWidthPass() : Pass("clean_zerowidth", "clean zero-width connections from the design") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clean_zerowidth [selection]\n");
		log("\n");
		log("Fixes the selected cells and processes to contain no zero-width connections.\n");
		log("Depending on the cell type, this may be implemented by removing the connection,\n");
		log("widening it to 1-bit, or removing the cell altogether.\n");
		log("\n");
	}

	void clean_case(RTLIL::CaseRule *cs)
	{
		std::vector<SigSig> new_actions;
		for (auto &action : cs->actions)
			if (GetSize(action.first) != 0)
				new_actions.push_back(action);
		std::swap(new_actions, cs->actions);
		for (auto sw : cs->switches)
			for (auto scs : sw->cases)
				clean_case(scs);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);

		CellTypes ct;
		ct.setup();

		for (auto module : design->selected_modules())
		{
			for (auto cell : module->selected_cells())
			{
				if (!ct.cell_known(cell->type)) {
					// User-defined cell: just prune zero-width connections.
					for (auto it: cell->connections()) {
						if (GetSize(it.second) == 0) {
							cell->unsetPort(it.first);
						}
					}
				} else if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
					// Coarse FF cells: remove if WIDTH == 0 (no outputs).
					// This will also trigger on fine cells, so use the Q port
					// width instead of actual WIDTH parameter.
					if (GetSize(cell->getPort(ID::Q)) == 0) {
						module->remove(cell);
					}
				} else if (cell->type.in(ID($pmux), ID($bmux), ID($demux))) {
					// Remove altogether if WIDTH is 0, replace with
					// a connection if S_WIDTH is 0.
					if (cell->getParam(ID::WIDTH).as_int() == 0) {
						module->remove(cell);
					}
					if (cell->getParam(ID::S_WIDTH).as_int() == 0) {
						module->connect(cell->getPort(ID::Y), cell->getPort(ID::A));
						module->remove(cell);
					}
				} else if (cell->type == ID($concat)) {
					// If a concat has a zero-width input: replace with direct
					// connection to the other input.
					if (cell->getParam(ID::A_WIDTH).as_int() == 0) {
						module->connect(cell->getPort(ID::Y), cell->getPort(ID::B));
						module->remove(cell);
					} else if (cell->getParam(ID::B_WIDTH).as_int() == 0) {
						module->connect(cell->getPort(ID::Y), cell->getPort(ID::A));
						module->remove(cell);
					}
				} else if (cell->type == ID($fsm)) {
					// TODO: not supported
				} else if (cell->is_mem_cell()) {
					// Skip — will be handled below.
				} else if (cell->type == ID($lut)) {
					// Zero-width LUT is just a const driver.
					if (cell->getParam(ID::WIDTH).as_int() == 0) {
						module->connect(cell->getPort(ID::Y), cell->getParam(ID::LUT)[0]);
						module->remove(cell);
					}
				} else if (cell->type == ID($sop)) {
					// Zero-width SOP is just a const driver.
					if (cell->getParam(ID::WIDTH).as_int() == 0) {
						// The value is 1 iff DEPTH is non-0.
						bool val = cell->getParam(ID::DEPTH).as_int() != 0;
						module->connect(cell->getPort(ID::Y), val);
						module->remove(cell);
					}
				} else if (cell->hasParam(ID::WIDTH)) {
					// For cells with WIDTH parameter: remove if zero.
					if (cell->getParam(ID::WIDTH).as_int() == 0) {
						module->remove(cell);
					}
				} else if (cell->hasParam(ID::Y_WIDTH)) {
					// For most operators: remove if Y width is 0, expand
					// A and B to 1-bit if their width is 0.
					if (cell->getParam(ID::Y_WIDTH).as_int() == 0) {
						module->remove(cell);
					} else if (cell->type == ID($macc)) {
						// TODO: fixing zero-width A and B not supported.
					} else {
						if (cell->getParam(ID::A_WIDTH).as_int() == 0) {
							cell->setPort(ID::A, State::S0);
							cell->setParam(ID::A_WIDTH, 1);
						}
						if (cell->hasParam(ID::B_WIDTH) && cell->getParam(ID::B_WIDTH).as_int() == 0) {
							cell->setPort(ID::B, State::S0);
							cell->setParam(ID::B_WIDTH, 1);
						}
					}
				}
			}

			// NOTE: Zero-width switch signals are left alone for processes, as there
			// is no simple way of cleaning them up.
			for (auto &it: module->processes) {
				if (!design->selected(module, it.second))
					continue;
				clean_case(&it.second->root_case);
				for (auto sync : it.second->syncs) {
					std::vector<int> swizzle;
					std::vector<RTLIL::MemWriteAction> new_memwr_actions;
					for (int i = 0; i < GetSize(sync->mem_write_actions); i++) {
						auto &memwr = sync->mem_write_actions[i];
						if (GetSize(memwr.data) == 0)
							continue;
						if (GetSize(memwr.address) == 0)
							memwr.address = State::S0;
						Const priority_mask;
						for (auto x : swizzle) {
							priority_mask.bits().push_back(memwr.priority_mask[x]);
						}
						memwr.priority_mask = priority_mask;
						swizzle.push_back(i);
						new_memwr_actions.push_back(memwr);
					}
					std::swap(new_memwr_actions, sync->mem_write_actions);
					std::vector<SigSig> new_actions;
					for (auto &action : sync->actions)
						if (GetSize(action.first) != 0)
							new_actions.push_back(action);
					std::swap(new_actions, sync->actions);
				}
			}

			for (auto &mem : Mem::get_selected_memories(module)) {
				if (mem.width == 0) {
					mem.remove();
					continue;
				}
				for (auto &init : mem.inits) {
					if (GetSize(init.addr) == 0) {
						init.addr = State::S0;
					}
				}
				for (auto &port : mem.rd_ports) {
					if (GetSize(port.addr) == 0) {
						port.addr = State::S0;
					}
				}
				for (auto &port : mem.wr_ports) {
					if (GetSize(port.addr) == 0) {
						port.addr = State::S0;
					}
				}
				mem.emit();
			}

			std::vector<SigSig> new_conns;
			for (auto &conn : module->connections())
				if (GetSize(conn.first) != 0)
					new_conns.push_back(conn);
			module->new_connections(new_conns);
		}
	}
} CleanZeroWidthPass;

PRIVATE_NAMESPACE_END
