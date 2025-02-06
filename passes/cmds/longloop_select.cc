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

struct LongLoopSelect : public ScriptPass {
	LongLoopSelect()
	    : ScriptPass("longloop_select", "Selects long for-loops (Creating logic above a certain logic depth) for further optimizations")
	{
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    longloop_select [-depth <for-loop threshold depth>] [-abc_opt <ABC options>] [-abc_script <ABC script>]\n");
		log("    If no ABC script/option is provided, this pass simply selects cells in for-loops\n");
		log("    If an ABC script/option is provided, this pass selects cells in a per for-loop basis and runs ABC with the given script\n");
		log("\n");
	}
	void script() override {}

	// Adapted from the torder pass
	void toposorting(std::vector<Cell *> &cells, SigMap &sigmap,
			 TopoSort<RTLIL::Cell *, RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell>> &toposort, bool debug)
	{
		if (debug) {
			log("  Collecting design data\n");
			log_flush();
		}
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
		if (debug) {
			log("  Creating sorting data structure\n");
			log_flush();
		}
		for (auto &it : bit_users)
			if (bit_drivers.count(it.first))
				for (auto driver_cell : bit_drivers.at(it.first))
					for (auto user_cell : it.second)
						toposort.edge(driver_cell, user_cell);

		toposort.analyze_loops = false;
		if (debug) {
			log("  Sorting\n");
			log_flush();
		}
		toposort.sort();
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		if (design == nullptr) {
			log_error("No design object");
			return;
		}
		uint32_t threshold_depth = 100;
		bool debug = false;
		size_t argidx;
		std::string abc_script;
		std::string abc_options;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-depth") {
				argidx++;
				threshold_depth = std::stoul(args[argidx], nullptr, 10);
			} else if (args[argidx] == "-debug") {
				debug = true;
			} else if (args[argidx] == "-abc_script") {
				argidx++;
				abc_script = args[argidx];
			} else if (args[argidx] == "-abc_opt") {
				argidx++;
				abc_options = args[argidx];
			} else {
				break;
			}
		}
		extra_args(args, argidx, design);

		if (std::getenv("DEBUG_LONGLOOPS")) {
			debug = true;
		}
		log("Running longloop_select pass\n");
		log_flush();

		Pass::call(design, "select -none");

		for (auto module : design->modules()) {
			if (debug) {
				log("Module %s\n", log_id(module));
				log_flush();
			}
			if (debug) {
				log("  Creating sigmap\n");
				log_flush();
			}
			SigMap sigmap(module);
			std::map<std::string, std::vector<Cell *>> loopIndexCellMap;
			if (debug) {
				log("  Creating sorting datastructures\n");
				log_flush();
			}

			for (auto cell : module->cells()) {
				std::string loopIndex = cell->get_string_attribute("\\in_for_loop");
				if (!loopIndex.empty()) {
					std::map<std::string, std::vector<Cell *>>::iterator itr = loopIndexCellMap.find(loopIndex);
					if (itr == loopIndexCellMap.end()) {
						std::vector<Cell *> cellSet;
						cellSet.push_back(cell);
						loopIndexCellMap.emplace(loopIndex, cellSet);
					} else {
						itr->second.push_back(cell);
					}
				}
			}

			if (!loopIndexCellMap.empty()) {
				log("  Found %ld for-loop clusters in module %s\n", loopIndexCellMap.size(), module->name.c_str());
				log_flush();
			}

			for (std::map<std::string, std::vector<Cell *>>::iterator itrCluster = loopIndexCellMap.begin();
			     itrCluster != loopIndexCellMap.end(); itrCluster++) {
				std::string loopInd = itrCluster->first;
				if (itrCluster->second.size() < threshold_depth) {
					if (debug) {
						log("  Skipping loop location %s as it contains only %ld cells\n", loopInd.c_str(),
						    itrCluster->second.size());
						log_flush();
					}
					continue;
				}
				if (debug) {
					log("  Analyzing loop location %s containing %ld cells\n", loopInd.c_str(), itrCluster->second.size());
					log_flush();
				}
				// For a given for-loop cell group, perform topological sorting to get the logic depth of the ending cell in
				// the group
				std::map<RTLIL::Cell *, int> celllevel;
				for (auto cell : itrCluster->second) {
					celllevel.emplace(cell, 0);
				}
				TopoSort<RTLIL::Cell *, RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell>> toposort;
				toposorting(itrCluster->second, sigmap, toposort, debug);
				std::vector<Cell *>::reverse_iterator itrLastCell = toposort.sorted.rbegin();
				int logicdepth = 0;
				std::map<RTLIL::Cell *, std::set<RTLIL::Cell *, cell_ptr_cmp>, cell_ptr_cmp> topo_cell_drivers =
				  toposort.get_database();
				for (auto cell : toposort.sorted) {
					int level = 0;
					auto itrAdj = topo_cell_drivers.find(cell);
					for (auto c : (*itrAdj).second) {
						level = std::max(level, celllevel[c]);
					}
					level++;
					celllevel[cell] = level;
					logicdepth = std::max(logicdepth, level);
				}
				if (debug) {
					log("  Logic depth: %d\n", logicdepth);
					log_flush();
				}
				if (logicdepth > (int)threshold_depth) {
					log("  Selecting %ld cells in for-loop location %s of depth %d ending with cell %s\n",
					    itrCluster->second.size(), loopInd.c_str(), logicdepth, log_id((*itrLastCell)));
					log_flush();
					std::string src_info = (*itrLastCell)->get_src_attribute();
					if (!(*itrLastCell)->get_string_attribute("\\in_for_loop").empty()) {
						src_info = (*itrLastCell)->get_string_attribute("\\in_for_loop");
					}
					// Select all cells in the loop cluster
					if (!abc_script.empty()) {
						// If an ABC script is provided, select on a per-loop basis
						Pass::call(design, "select -none");
					}
					for (auto cell : itrCluster->second) {
						design->select(module, cell);
						if (cell->get_string_attribute("\\in_for_loop").empty()) {
							cell->set_string_attribute("\\in_for_loop", src_info);
						} else {
							src_info = cell->get_string_attribute("\\in_for_loop");
						}
					}
					if (!abc_script.empty()) {
						std::string command = "abc -map_src " + src_info + " -script " + abc_script;
						log("  Executing: %s\n", command.c_str());
						log_flush();
						Pass::call(design, command);
					} else if (!abc_options.empty()) {
						abc_options.erase(std::remove(abc_options.begin(), abc_options.end(), '"'), abc_options.end());
						std::string command = "abc -map_src " + src_info + " " + abc_options;
						log("  Executing: %s\n", command.c_str());
						log_flush();
						Pass::call(design, command);
					}
				}
			}
		}

		log("End longloop_select pass\n");
		log_flush();
	}
} LongLoopSelect;

PRIVATE_NAMESPACE_END
