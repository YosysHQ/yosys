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
#include "kernel/cellaigs.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct AigmapPass : public Pass {
	AigmapPass() : Pass("aigmap", "map logic to and-inverter-graph circuit") { }
	virtual void help()
	{
		log("\n");
		log("    aigmap [options] [selection]\n");
		log("\n");
		log("Replace all logic cells with circuits made of only $_AND_ and\n");
		log("$_NOT_ cells.\n");
		log("\n");
		log("    -nand\n");
		log("        Enable creation of $_NAND_ cells\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool nand_mode = false;

		log_header(design, "Executing AIGMAP pass (map logic to AIG).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-nand") {
				nand_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			vector<Cell*> replaced_cells;
			int not_replaced_count = 0;
			dict<IdString, int> stat_replaced;
			dict<IdString, int> stat_not_replaced;
			int orig_num_cells = GetSize(module->cells());

			for (auto cell : module->selected_cells())
			{
				Aig aig(cell);

				if (cell->type == "$_AND_" || cell->type == "$_NOT_")
					aig.name.clear();

				if (nand_mode && cell->type == "$_NAND_")
					aig.name.clear();

				if (aig.name.empty()) {
					not_replaced_count++;
					stat_not_replaced[cell->type]++;
					continue;
				}

				vector<SigBit> sigs;
				dict<pair<int, int>, SigBit> and_cache;

				for (int node_idx = 0; node_idx < GetSize(aig.nodes); node_idx++)
				{
					SigBit bit;
					auto &node = aig.nodes[node_idx];

					if (node.portbit >= 0) {
						bit = cell->getPort(node.portname)[node.portbit];
					} else if (node.left_parent < 0 && node.right_parent < 0) {
						bit = node.inverter ? State::S1 : State::S0;
						goto skip_inverter;
					} else {
						SigBit A = sigs.at(node.left_parent);
						SigBit B = sigs.at(node.right_parent);
						if (nand_mode && node.inverter) {
							bit = module->NandGate(NEW_ID, A, B);
							goto skip_inverter;
						} else {
							pair<int, int> key(node.left_parent, node.right_parent);
							if (and_cache.count(key))
								bit = and_cache.at(key);
							else
								bit = module->AndGate(NEW_ID, A, B);
						}
					}

					if (node.inverter)
						bit = module->NotGate(NEW_ID, bit);

				skip_inverter:
					for (auto &op : node.outports)
						module->connect(cell->getPort(op.first)[op.second], bit);

					sigs.push_back(bit);
				}

				replaced_cells.push_back(cell);
				stat_replaced[cell->type]++;
			}

			if (not_replaced_count == 0 && replaced_cells.empty())
				continue;

			log("Module %s: replaced %d cells with %d new cells, skipped %d cells.\n", log_id(module),
					GetSize(replaced_cells), GetSize(module->cells()) - orig_num_cells, not_replaced_count);

			if (!stat_replaced.empty()) {
				stat_replaced.sort();
				log("  replaced %d cell types:\n", GetSize(stat_replaced));
				for (auto &it : stat_replaced)
					log("%8d %s\n", it.second, log_id(it.first));
			}

			if (!stat_not_replaced.empty()) {
				stat_not_replaced.sort();
				log("  not replaced %d cell types:\n", GetSize(stat_not_replaced));
				for (auto &it : stat_not_replaced)
					log("%8d %s\n", it.second, log_id(it.first));
			}

			for (auto cell : replaced_cells)
				module->remove(cell);
		}
	}
} AigmapPass;

PRIVATE_NAMESPACE_END
