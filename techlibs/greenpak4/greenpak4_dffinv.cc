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

void invert_gp_dff(Cell *cell, bool invert_input)
{
	string cell_type = cell->type.str();
	bool cell_type_latch = cell_type.find("LATCH") != string::npos;
	bool cell_type_i = cell_type.find('I') != string::npos;
	bool cell_type_r = cell_type.find('R') != string::npos;
	bool cell_type_s = cell_type.find('S') != string::npos;

	if (!invert_input)
	{
		Const initval = cell->getParam(ID::INIT);
		if (GetSize(initval) >= 1) {
			if (initval.bits[0] == State::S0)
				initval.bits[0] = State::S1;
			else if (initval.bits[0] == State::S1)
				initval.bits[0] = State::S0;
			cell->setParam(ID::INIT, initval);
		}

		if (cell_type_r && cell_type_s)
		{
			Const srmode = cell->getParam(ID(SRMODE));
			if (GetSize(srmode) >= 1) {
				if (srmode.bits[0] == State::S0)
					srmode.bits[0] = State::S1;
				else if (srmode.bits[0] == State::S1)
					srmode.bits[0] = State::S0;
				cell->setParam(ID(SRMODE), srmode);
			}
		}
		else
		{
			if (cell_type_r) {
				cell->setPort(ID(nSET), cell->getPort(ID(nRST)));
				cell->unsetPort(ID(nRST));
				cell_type_r = false;
				cell_type_s = true;
			} else
			if (cell_type_s) {
				cell->setPort(ID(nRST), cell->getPort(ID(nSET)));
				cell->unsetPort(ID(nSET));
				cell_type_r = true;
				cell_type_s = false;
			}
		}
	}

	if (cell_type_i) {
		cell->setPort(ID::Q, cell->getPort(ID(nQ)));
		cell->unsetPort(ID(nQ));
		cell_type_i = false;
	} else {
		cell->setPort(ID(nQ), cell->getPort(ID::Q));
		cell->unsetPort(ID::Q);
		cell_type_i = true;
	}

	if(cell_type_latch)
		cell->type = stringf("\\GP_DLATCH%s%s%s", cell_type_s ? "S" : "", cell_type_r ? "R" : "", cell_type_i ? "I" : "");
	else
		cell->type = stringf("\\GP_DFF%s%s%s", cell_type_s ? "S" : "", cell_type_r ? "R" : "", cell_type_i ? "I" : "");

	log("Merged %s inverter into cell %s.%s: %s -> %s\n", invert_input ? "input" : "output",
			log_id(cell->module), log_id(cell), cell_type.c_str()+1, log_id(cell->type));
}

struct Greenpak4DffInvPass : public Pass {
	Greenpak4DffInvPass() : Pass("greenpak4_dffinv", "merge greenpak4 inverters and DFF/latches") { }
	void help() override
	{
		log("\n");
		log("    greenpak4_dffinv [options] [selection]\n");
		log("\n");
		log("Merge GP_INV cells with GP_DFF* and GP_DLATCH* cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing GREENPAK4_DFFINV pass (merge input/output inverters into FF/latch cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		pool<IdString> gp_dff_types;
		gp_dff_types.insert(ID(GP_DFF));
		gp_dff_types.insert(ID(GP_DFFI));
		gp_dff_types.insert(ID(GP_DFFR));
		gp_dff_types.insert(ID(GP_DFFRI));
		gp_dff_types.insert(ID(GP_DFFS));
		gp_dff_types.insert(ID(GP_DFFSI));
		gp_dff_types.insert(ID(GP_DFFSR));
		gp_dff_types.insert(ID(GP_DFFSRI));

		gp_dff_types.insert(ID(GP_DLATCH));
		gp_dff_types.insert(ID(GP_DLATCHI));
		gp_dff_types.insert(ID(GP_DLATCHR));
		gp_dff_types.insert(ID(GP_DLATCHRI));
		gp_dff_types.insert(ID(GP_DLATCHS));
		gp_dff_types.insert(ID(GP_DLATCHSI));
		gp_dff_types.insert(ID(GP_DLATCHSR));
		gp_dff_types.insert(ID(GP_DLATCHSRI));

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			dict<SigBit, int> sig_use_cnt;
			dict<SigBit, SigBit> inv_in2out, inv_out2in;
			dict<SigBit, Cell*> inv_in2cell;
			pool<Cell*> dff_cells;

			for (auto wire : module->wires())
			{
				if (!wire->port_output)
					continue;

				for (auto bit : sigmap(wire))
					sig_use_cnt[bit]++;
			}

			for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->input(conn.first) || !cell->known())
					for (auto bit : sigmap(conn.second))
						sig_use_cnt[bit]++;

			for (auto cell : module->selected_cells())
			{
				if (gp_dff_types.count(cell->type)) {
					dff_cells.insert(cell);
					continue;
				}

				if (cell->type == ID(GP_INV)) {
					SigBit in_bit = sigmap(cell->getPort(ID(IN)));
					SigBit out_bit = sigmap(cell->getPort(ID(OUT)));
					inv_in2out[in_bit] = out_bit;
					inv_out2in[out_bit] = in_bit;
					inv_in2cell[in_bit] = cell;
					continue;
				}
			}

			for (auto cell : dff_cells)
			{
				SigBit d_bit = sigmap(cell->getPort(ID::D));
				SigBit q_bit = sigmap(cell->hasPort(ID::Q) ? cell->getPort(ID::Q) : cell->getPort(ID(nQ)));

				while (inv_out2in.count(d_bit))
				{
					sig_use_cnt[d_bit]--;
					invert_gp_dff(cell, true);
					d_bit = inv_out2in.at(d_bit);
					cell->setPort(ID::D, d_bit);
					sig_use_cnt[d_bit]++;
				}

				while (inv_in2out.count(q_bit) && sig_use_cnt[q_bit] == 1)
				{
					SigBit new_q_bit = inv_in2out.at(q_bit);
					module->remove(inv_in2cell.at(q_bit));
					sig_use_cnt.erase(q_bit);
					inv_in2out.erase(q_bit);
					inv_out2in.erase(new_q_bit);
					inv_in2cell.erase(q_bit);

					invert_gp_dff(cell, false);
					if (cell->hasPort(ID::Q))
						cell->setPort(ID::Q, new_q_bit);
					else
						cell->setPort(ID(nQ), new_q_bit);
				}
			}
		}
	}
} Greenpak4DffInvPass;

PRIVATE_NAMESPACE_END
