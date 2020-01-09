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

// [[CITE]] Tarjan's strongly connected components algorithm
// Tarjan, R. E. (1972), "Depth-first search and linear graph algorithms", SIAM Journal on Computing 1 (2): 146-160, doi:10.1137/0201010
// http://en.wikipedia.org/wiki/Tarjan's_strongly_connected_components_algorithm

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SccWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap;
	CellTypes ct;

	std::set<RTLIL::Cell*> workQueue;
	std::map<RTLIL::Cell*, std::set<RTLIL::Cell*>> cellToNextCell;
	std::map<RTLIL::Cell*, RTLIL::SigSpec> cellToPrevSig, cellToNextSig;

	std::map<RTLIL::Cell*, std::pair<int, int>> cellLabels;
	std::map<RTLIL::Cell*, int> cellDepth;
	std::set<RTLIL::Cell*> cellsOnStack;
	std::vector<RTLIL::Cell*> cellStack;
	int labelCounter;

	std::map<RTLIL::Cell*, int> cell2scc;
	std::vector<std::set<RTLIL::Cell*>> sccList;

	void run(RTLIL::Cell *cell, int depth, int maxDepth)
	{
		log_assert(workQueue.count(cell) > 0);

		workQueue.erase(cell);
		cellLabels[cell] = std::pair<int, int>(labelCounter, labelCounter);
		labelCounter++;

		cellsOnStack.insert(cell);
		cellStack.push_back(cell);

		if (maxDepth >= 0)
			cellDepth[cell] = depth;

		for (auto nextCell : cellToNextCell[cell])
			if (cellLabels.count(nextCell) == 0) {
				run(nextCell, depth+1, maxDepth);
				cellLabels[cell].second = min(cellLabels[cell].second, cellLabels[nextCell].second);
			} else
			if (cellsOnStack.count(nextCell) > 0 && (maxDepth < 0 || cellDepth[nextCell] + maxDepth > depth)) {
					cellLabels[cell].second = min(cellLabels[cell].second, cellLabels[nextCell].second);
			}

		if (cellLabels[cell].first == cellLabels[cell].second)
		{
			if (cellStack.back() == cell)
			{
				cellStack.pop_back();
				cellsOnStack.erase(cell);
			}
			else
			{
				log("Found an SCC:");
				std::set<RTLIL::Cell*> scc;
				while (cellsOnStack.count(cell) > 0) {
					RTLIL::Cell *c = cellStack.back();
					cellStack.pop_back();
					cellsOnStack.erase(c);
					log(" %s", RTLIL::id2cstr(c->name));
					cell2scc[c] = sccList.size();
					scc.insert(c);
				}
				sccList.push_back(scc);
				log("\n");
			}
		}
	}

	SccWorker(RTLIL::Design *design, RTLIL::Module *module, bool nofeedbackMode, bool allCellTypes, int maxDepth) :
			design(design), module(module), sigmap(module)
	{
		if (module->processes.size() > 0) {
			log("Skipping module %s as it contains processes (run 'proc' pass first).\n", module->name.c_str());
			return;
		}

		if (allCellTypes) {
			ct.setup(design);
		} else {
			ct.setup_internals();
			ct.setup_stdcells();
		}

		SigPool selectedSignals;
		SigSet<RTLIL::Cell*> sigToNextCells;

		for (auto &it : module->wires_)
			if (design->selected(module, it.second))
				selectedSignals.add(sigmap(RTLIL::SigSpec(it.second)));

		for (auto &it : module->cells_)
		{
			RTLIL::Cell *cell = it.second;

			if (!design->selected(module, cell))
				continue;

			if (!allCellTypes && !ct.cell_known(cell->type))
				continue;

			workQueue.insert(cell);

			RTLIL::SigSpec inputSignals, outputSignals;

			for (auto &conn : cell->connections())
			{
				bool isInput = true, isOutput = true;

				if (ct.cell_known(cell->type)) {
					isInput = ct.cell_input(cell->type, conn.first);
					isOutput = ct.cell_output(cell->type, conn.first);
				}

				RTLIL::SigSpec sig = selectedSignals.extract(sigmap(conn.second));
				sig.sort_and_unify();

				if (isInput)
					inputSignals.append(sig);
				if (isOutput)
					outputSignals.append(sig);
			}

			inputSignals.sort_and_unify();
			outputSignals.sort_and_unify();

			cellToPrevSig[cell] = inputSignals;
			cellToNextSig[cell] = outputSignals;
			sigToNextCells.insert(inputSignals, cell);
		}

		for (auto cell : workQueue)
		{
			cellToNextCell[cell] = sigToNextCells.find(cellToNextSig[cell]);

			if (!nofeedbackMode && cellToNextCell[cell].count(cell)) {
				log("Found an SCC:");
				std::set<RTLIL::Cell*> scc;
				log(" %s", RTLIL::id2cstr(cell->name));
				cell2scc[cell] = sccList.size();
				scc.insert(cell);
				sccList.push_back(scc);
				log("\n");
			}
		}

		labelCounter = 0;
		cellLabels.clear();

		while (!workQueue.empty())
		{
			RTLIL::Cell *cell = *workQueue.begin();
			log_assert(cellStack.size() == 0);
			cellDepth.clear();

			run(cell, 0, maxDepth);
		}

		log("Found %d SCCs in module %s.\n", int(sccList.size()), RTLIL::id2cstr(module->name));
	}

	void select(RTLIL::Selection &sel)
	{
		for (int i = 0; i < int(sccList.size()); i++)
		{
			std::set<RTLIL::Cell*> &cells = sccList[i];
			RTLIL::SigSpec prevsig, nextsig, sig;

			for (auto cell : cells) {
				sel.selected_members[module->name].insert(cell->name);
				prevsig.append(cellToPrevSig[cell]);
				nextsig.append(cellToNextSig[cell]);
			}

			prevsig.sort_and_unify();
			nextsig.sort_and_unify();
			sig = prevsig.extract(nextsig);

			for (auto &chunk : sig.chunks())
				if (chunk.wire != NULL)
					sel.selected_members[module->name].insert(chunk.wire->name);
		}
	}
};

struct SccPass : public Pass {
	SccPass() : Pass("scc", "detect strongly connected components (logic loops)") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    scc [options] [selection]\n");
		log("\n");
		log("This command identifies strongly connected components (aka logic loops) in the\n");
		log("design.\n");
		log("\n");
		log("    -expect <num>\n");
		log("        expect to find exactly <num> SSCs. A different number of SSCs will\n");
		log("        produce an error.\n");
		log("\n");
		log("    -max_depth <num>\n");
		log("        limit to loops not longer than the specified number of cells. This\n");
		log("        can e.g. be useful in identifying small local loops in a module that\n");
		log("        implements one large SCC.\n");
		log("\n");
		log("    -nofeedback\n");
		log("        do not count cells that have their output fed back into one of their\n");
		log("        inputs as single-cell scc.\n");
		log("\n");
		log("    -all_cell_types\n");
		log("        Usually this command only considers internal non-memory cells. With\n");
		log("        this option set, all cells are considered. For unknown cells all ports\n");
		log("        are assumed to be bidirectional 'inout' ports.\n");
		log("\n");
		log("    -set_attr <name> <value>\n");
		log("        set the specified attribute on all cells that are part of a logic\n");
		log("        loop. the special token {} in the value is replaced with a unique\n");
		log("        identifier for the logic loop.\n");
		log("\n");
		log("    -select\n");
		log("        replace the current selection with a selection of all cells and wires\n");
		log("        that are part of a found logic loop\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::map<std::string, std::string> setAttr;
		bool allCellTypes = false;
		bool selectMode = false;
		bool nofeedbackMode = false;
		int maxDepth = -1;
		int expect = -1;

		log_header(design, "Executing SCC pass (detecting logic loops).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_depth" && argidx+1 < args.size()) {
				maxDepth = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-expect" && argidx+1 < args.size()) {
				expect = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-nofeedback") {
				nofeedbackMode = true;
				continue;
			}
			if (args[argidx] == "-all_cell_types") {
				allCellTypes = true;
				continue;
			}
			if (args[argidx] == "-set_attr" && argidx+2 < args.size()) {
				setAttr[args[argidx+1]] = args[argidx+2];
				argidx += 2;
				continue;
			}
			if (args[argidx] == "-select") {
				selectMode = true;
				continue;
			}
			break;
		}
		int origSelectPos = design->selection_stack.size() - 1;
		extra_args(args, argidx, design);

		RTLIL::Selection newSelection(false);
		int scc_counter = 0;

		for (auto mod : design->selected_modules())
		{
			SccWorker worker(design, mod, nofeedbackMode, allCellTypes, maxDepth);

			if (!setAttr.empty())
			{
				for (const auto &cells : worker.sccList)
				{
					for (auto attr : setAttr)
					{
						IdString attr_name(RTLIL::escape_id(attr.first));
						string attr_valstr = attr.second;
						string index = stringf("%d", scc_counter);

						for (size_t pos = 0; (pos = attr_valstr.find("{}", pos)) != string::npos; pos += index.size())
							attr_valstr.replace(pos, 2, index);

						Const attr_value(attr_valstr);

						for (auto cell : cells)
							cell->attributes[attr_name] = attr_value;
					}

					scc_counter++;
				}
			}
			else
			{
				scc_counter += GetSize(worker.sccList);
			}

			if (selectMode)
				worker.select(newSelection);
		}

		if (expect >= 0) {
			if (scc_counter == expect)
				log("Found and expected %d SCCs.\n", scc_counter);
			else
				log_error("Found %d SCCs but expected %d.\n", scc_counter, expect);
		} else
			log("Found %d SCCs.\n", scc_counter);

		if (selectMode) {
			log_assert(origSelectPos >= 0);
			design->selection_stack[origSelectPos] = newSelection;
			design->selection_stack[origSelectPos].optimize(design);
		}
	}
} SccPass;

PRIVATE_NAMESPACE_END
