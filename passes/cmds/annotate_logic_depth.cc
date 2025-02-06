/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

typedef RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell> cell_ptr_cmp;

struct AnnotateLogicDepth : public ScriptPass {
	AnnotateLogicDepth() : ScriptPass("annotate_logic_depth", "Annotate logic depth per cells and modules") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    annotate_logic_depth [-module] [-cell]\n");
		log("\n");
	}
	void script() override {}

	// Adapted from the torder pass
	void toposorting(std::vector<Cell *> &cells, SigMap &sigmap,
			 TopoSort<RTLIL::Cell *, RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell>> &toposort)
	{
		dict<SigBit, pool<Cell *>> bit_drivers, bit_users;
		for (Cell *cell : cells) {
			for (auto conn : cell->connections()) {
				bool noautostop = false;
				if (!noautostop && yosys_celltypes.cell_known(cell->type)) {
					if (conn.first.in(ID::Q, ID::CTRL_OUT, ID::RD_DATA))
						continue;
					if (cell->type.in(ID($memrd), ID($memrd_v2)) && conn.first == ID::DATA)
						continue;
				}

				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						bit_users[bit].insert(cell);

				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						bit_drivers[bit].insert(cell);

				toposort.node(cell);
			}
		}
		for (auto &it : bit_users)
			if (bit_drivers.count(it.first))
				for (auto driver_cell : bit_drivers.at(it.first))
					for (auto user_cell : it.second)
						toposort.edge(driver_cell, user_cell);

		toposort.analyze_loops = false;
		toposort.sort();
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		if (design == nullptr) {
			log_error("No design object");
			return;
		}
		size_t argidx;
		bool annotate_modules = false;
		bool annotate_cells = false;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-module") {
				annotate_modules = true;
			} else if (args[argidx] == "-cell") {
				annotate_cells = true;
			} else {
				break;
			}
		}
		extra_args(args, argidx, design);
		int design_max_depth = 0;
		for (auto module : design->selected_modules()) {
			int module_max_depth = 0;
			SigMap sigmap(module);
			std::vector<Cell *> cells;
			std::map<RTLIL::Cell *, int> celllevel;
			for (auto cell : module->selected_cells()) {
				cells.push_back(cell);
				celllevel.emplace(cell, 0);
			}
			TopoSort<RTLIL::Cell *, RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell>> toposort;
			toposorting(cells, sigmap, toposort);
			std::map<RTLIL::Cell *, std::set<RTLIL::Cell *, cell_ptr_cmp>, cell_ptr_cmp> topo_cell_drivers = toposort.get_database();
			for (auto cell : toposort.sorted) {
				int level = 0;
				auto itrAdj = topo_cell_drivers.find(cell);
				for (auto c : (*itrAdj).second) {
					level = std::max(level, celllevel[c]);
				}
				level++;
				celllevel[cell] = level;
				module_max_depth = std::max(module_max_depth, level);
				if (annotate_cells)
					cell->set_string_attribute("$DEPTH", std::to_string(level));
			}
			design_max_depth = std::max(design_max_depth, module_max_depth);
			if (annotate_modules)
				module->set_string_attribute("$MAX_DEPTH", std::to_string(module_max_depth));
		}
		design->top_module()->set_string_attribute("$DESIGN_MAX_DEPTH", std::to_string(design_max_depth));
		log("Max logic depth: %d\n", design_max_depth);
	}
} AnnotateLogicDepth;

PRIVATE_NAMESPACE_END
