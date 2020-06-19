/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Alberto Gonzalez <boqwxp@airmail.cc>
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
#include "kernel/cost.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PartitionWorker {
	//Constructs a hypergraph from a module, partitions the hypergraph, recovers the cell
	//partition assignments, creates partition modules with the appropriate cells, ports,
	//and intra-partition connections, then replaces the original module with one that
	//instantiates and connects the partition modules.
	int opt_k = -1, opt_imbalance = 5;
	bool opt_verbose = false, opt_nocleanup = false;
	RTLIL::Module *module = nullptr, *new_module = nullptr;
	RTLIL::Design *design = nullptr;
	dict<RTLIL::IdString, int> cell_type_costs = CellCosts::unit_gate_cost();
	dict<RTLIL::SigBit, int> sigbit_to_edgenum = {};
	dict<int, pool<int>> edge_nodes = {};
	dict<int, pool<int>> partition_nodes = {};
	dict<int, bool> edge_cut = {};
	pool<RTLIL::IdString> cut_wires = {};
	int node_ctr = 0, edge_ctr = 0, cut_edge_ctr = 0, partitions = 2;
	std::vector<RTLIL::Module *> partition_modules = {};

	void create_hypergraph() {
		//Initial set up on sigbit_to_edgenum for the cell output ports and on edge_nodes with just that output node for now:
		for (auto cell : module->cells()) {
			if (cell_type_costs.find(cell->type) == cell_type_costs.end())
				log_cmd_error("Module must be techmapped; encountered unknown cell type %s\n", cell->type.c_str());

			if (opt_verbose) log("Adding cell %s as node #%d\n", cell->name.c_str(), node_ctr);
			for (auto port : cell->connections()) {
				if (cell->output(port.first)) {
					for (auto i = 0; i < GetSize(port.second); ++i) {
						auto sigbit = port.second[i];
						sigbit_to_edgenum.emplace(sigbit, edge_ctr);
						edge_nodes.emplace(edge_ctr++, {node_ctr});
						if (opt_verbose) log("Defined hyperedge #%d starting with driver node #%d\n", edge_ctr-1, node_ctr);
					}
				}
			}
			node_ctr++;
		}

		//Go through connections to find more drivers and fully set up sigbit_to_edgenum:
		for (auto conn : module->connections()) {
			if (!conn.second.is_wire() || !conn.second.as_wire()->port_input) {
				for (auto i = 0; i < GetSize(conn.first); ++i) {
					auto it = sigbit_to_edgenum.find(conn.second[i]);
					if (it != sigbit_to_edgenum.end())
						sigbit_to_edgenum.emplace(conn.first[i], it->second);
					else
						log_cmd_error("Cannot find driver for connection %s = %s\n", log_signal(conn.first[i]), log_signal(conn.second[i]));
				}
			}
		}

		//Fully populate edge_nodes, relying on a consistent iteration order over `module->cells()` to avoid storing
		//a dict<RTLIL::Cell *, int> cell_to_nodenum:
		node_ctr = 0;
		for (auto cell : module->cells()) {
			for (auto port : cell->connections()) {
				if (port.first != ID::Y) {
					for (auto i = 0; i < GetSize(port.second); ++i) {
						auto sigbit = port.second[i];
						auto it = sigbit_to_edgenum.find(sigbit);
						if (it != sigbit_to_edgenum.end()) {
							if (opt_verbose) log("Found driver hyperedge #%d for %s on node #%d\n", it->second, log_signal(sigbit), node_ctr);
							edge_nodes[it->second].insert(node_ctr);
						} else {
							if (sigbit.wire == nullptr || !sigbit.wire->port_input)
								log_cmd_error("Cannot find driver for net %s\n", log_signal(sigbit));
						}
					}
				}
			}
			node_ctr++;
		}
	}

	void write_hypergraph(const std::string &out_fname) {
		//#edges #nodes 10
		//[[node] foreach node in edge_nodes[i]] foreach 0 <= i < edge_ctr
		//[weight(cell[i])] foreach 0 <= i < node_ctr
		std::ofstream fout(out_fname);
		if (!fout)
			log_cmd_error("Could not open temporary file for writing.\n");

		fout << edge_ctr << " " << node_ctr << " 10" << std::endl;
		fout << "% edge definitions" << std::endl;
		for (auto i = 0; i < edge_ctr; ++i) {
			std::vector<int> nodes(edge_nodes[i].begin(), edge_nodes[i].end());
			for (auto j = 0; j < GetSize(nodes); ++j) {
				fout << nodes[j] + 1; //shift from 0-based indexing to 1-based indexing
				if (j != GetSize(nodes) - 1)
					fout << " ";
			}
			fout << std::endl;
		}
		fout << "% node weights" << std::endl;
		for (auto i = 0; i < node_ctr; ++i) {
			RTLIL::Cell *cell = *(module->cells().begin() + i);
			fout << cell_type_costs.at(cell->type) << std::endl;
		}
		fout.close();
	}

	void call_solver(const std::string &problem_fname, const std::string &solution_fname) {
		if (opt_k == -1)
			partitions = 2;
		else if (opt_k != -1 && opt_k >= 2)
			partitions = opt_k;
		else if (opt_k != -1)
			return; //nothing to do
		std::string partitions_str = opt_k != 1? stringf(" -k %d", partitions) : "";
		std::string imbalance_str = opt_imbalance != 5? stringf(" -e %d", opt_imbalance) : "";
		std::string input_file_str = " -i " + problem_fname;
		std::string output_file_str = " -o " + solution_fname;
		std::string minipart_cmd = "minipart" + input_file_str + output_file_str + partitions_str + imbalance_str;
		if (run_command(minipart_cmd, [](const std::string &){}) != 0)
			log_cmd_error("Could not solve with minipart; is it installed and on the PATH?\n");
	}

	void recover_partitions_edge_cuts(const std::string &solution_fname) {
		std::ifstream fin(solution_fname);
		std::string buf;

		//Recover partitions and fill partition_nodes:
		for (auto i = 0; i < partitions; ++i)
			partition_nodes[i] = {};
		for (auto i = 0; std::getline(fin, buf); ++i) {
			int partition = atoi(buf.c_str());
			partition_nodes[partition].insert(i);
		}

		//Determine which edges were cut and fill out edge_cut:
		for (auto i = 0; i < edge_ctr; ++i) {
			pool<int> nodes = edge_nodes[i];
			log_assert(GetSize(nodes) >= 1);
			int needle = nodes.pop();
			int j = 0, partition = 0;
			bool cut = false;
			for (j = 0; j < partitions; ++j) {
				if (partition_nodes[j][needle])
					break;
			}
			log_assert(j != partitions);
			partition = j;

			while(!nodes.empty()) {
				int needle = nodes.pop();
				if (!partition_nodes[partition][needle]) {
					cut = true;
					if (opt_verbose) log("Hyperedge #%d is cut; node #%d is not in partition %d.\n", i, needle, partition);
					break;
				}
			}

			edge_cut[i] = cut;
			if (cut)
				cut_edge_ctr++;
		}

		//Also mark edges with module outputs as cut, so the outputs get included in their partition's ports list:
		for (auto port : module->ports) {
			RTLIL::Wire *wire = module->wire(port);
			log_assert(wire != nullptr);

			if (wire->port_output) {
				for (auto i = 0; i < GetSize(wire); ++i) {
					int edgenum = sigbit_to_edgenum[RTLIL::SigBit(wire, i)];
					edge_cut[edgenum] = true;
					if (opt_verbose) log("Marking hyperedge #%d as cut because of PO %s\n", edgenum, wire->name.c_str());
				}
			}
		}
	}

	void create_partition_modules() {
		for (auto i = 0; i < partitions; ++i) {
			//Create new module for the partition:
			RTLIL::IdString dest_module_name = stringf("%s_partition%d", module->name.c_str(), i);
			partition_modules.emplace_back(design->addModule(dest_module_name));
			RTLIL::Module *dest_module = design->module(dest_module_name);
			design->select(dest_module);

			//Copy cells and cell ports to this partition:
			for (auto node : partition_nodes[i]) {
				RTLIL::Cell *cell = *(module->cells().begin() + node);
				RTLIL::Cell *dest_cell = dest_module->addCell(cell->name, cell->type);
				//Copy cell ports, creating a new wire for each port if one does not already exist:
				for (auto &it : cell->connections()) {
					log_assert(it.second.is_wire());
					RTLIL::IdString wire_name = it.second.as_wire()->name.c_str();
					RTLIL::Wire *dest_wire = dest_module->wire(wire_name);
					if (dest_wire == nullptr) {
						dest_wire = dest_module->addWire(it.second.as_wire()->name, GetSize(it.second));

						//if the wire is a PI or PO in the original module, make it so for this module:
						if (it.second.as_wire()->port_input)
							dest_wire->port_input = true;
						if (it.second.as_wire()->port_output)
							dest_wire->port_output = true;
					}
					//if the wire corresponds to a cut edge, determine if we need to mark it a module
					//input or a module output of this partition:
					for (auto j = 0; j < GetSize(it.second); ++j) {
						int edgenum = sigbit_to_edgenum[RTLIL::SigBit(it.second.as_wire(), j)];
						if (edge_cut[edgenum]) {
							cut_wires.insert(it.second.as_wire()->name);
							if (opt_verbose) log("Found a cut hyperedge #%d, marking %s as port\n", edgenum, dest_wire->name.c_str());
							if (cell->input(it.first) && !dest_wire->port_output)
								dest_wire->port_input = true;
							else if (cell->output(it.first)) {
								dest_wire->port_input = false;
								dest_wire->port_output = true;
							}
							break;
						}
						else if (opt_verbose) {
							log("Hyperedge #%d not cut, not marking %s as port\n", edgenum, dest_wire->name.c_str());
						}
					}
					dest_cell->setPort(it.first, dest_wire);
				}
			}

			dest_module->fixup_ports();
		}
	}

	void create_partitioned_module() {
		new_module = design->addModule(NEW_ID);

		//Add wires for PIs and POs:
		for (auto id : module->ports) {
			RTLIL::Wire *old_io = module->wire(id);
			RTLIL::Wire *new_io = new_module->addWire(id, GetSize(old_io));
			new_io->port_input = old_io->port_input;
			new_io->port_output = old_io->port_output;
		}
		new_module->fixup_ports();

		//Add wires for cut hyperedges, i.e. signals crossing partitions:
		for (auto id : cut_wires) {
			if (new_module->wire(id) == nullptr) {
				if (opt_verbose) log("Adding cut wire %s\n", id.c_str());
				new_module->addWire(id, GetSize(module->wire(id)));
			} else if (opt_verbose) {
				 log("Skipping cut wire %s\n", id.c_str());
			}
		}

		//Add and connect partition submodule instances:
		pool<RTLIL::IdString> pos;
		for (auto port : module->ports)
			if (module->wire(port)->port_output)
				pos.insert(port);
		for (auto i = 0; i < partitions; ++i) {
			RTLIL::IdString module_name = stringf("%s_partition%d", module->name.c_str(), i);
			RTLIL::Cell *partition = new_module->addCell(module_name.str() + "_inst", module_name);
			RTLIL::Module *partition_mod = design->module(module_name);
			log_assert(partition_mod != nullptr);
			for (auto id : partition_mod->ports) {
				RTLIL::Wire *new_module_wire = new_module->wire(id);
				partition->setPort(id, new_module_wire);
				if (pos[id])
					pos.erase(id); //PO is driven directly by this partition instance
			}
		}

		//Follow connections backwards from each PO until (hopefully) we reach a port of a partition module:
		int old_pos_size = 0;
		while (GetSize(pos) != old_pos_size) {
			old_pos_size = GetSize(pos);
			for (auto &conn : module->connections()) {
				log_assert(conn.first.is_wire());
				RTLIL::Wire *old_mod_lhs = conn.first.as_wire();
				if (pos[old_mod_lhs->name]) {
					log_assert(conn.second.is_wire());
					RTLIL::Wire *old_mod_rhs = conn.second.as_wire();
					RTLIL::Wire *new_mod_rhs = new_module->wire(old_mod_rhs->name);
					if (new_mod_rhs == nullptr) {
						new_mod_rhs = new_module->addWire(old_mod_rhs->name, GetSize(old_mod_rhs));
						pos.insert(old_mod_rhs->name);
					}
					new_module->connect(new_module->wire(old_mod_lhs->name), new_mod_rhs);
					pos.erase(old_mod_lhs->name);
				}
			}
		}
		if (GetSize(pos) != 0)
			log_cmd_error("Could not find connection for %d primary output(s) including %s\n", GetSize(pos), pos.pop().c_str());

		RTLIL::IdString new_module_name = module->name;
		design->remove(module);
		design->rename(new_module, new_module_name);
		design->select(new_module);
	}

	PartitionWorker(RTLIL::Design *_design, RTLIL::Module *_module, int _opt_k, int _opt_imbalance, const dict<RTLIL::IdString, int> &_cell_type_costs, bool _opt_verbose, bool _opt_nocleanup) {
		int64_t t_begin = PerformanceTimer::query();

		//Set config:
		design = _design;
		module = _module;
		opt_k = _opt_k;
		opt_imbalance = _opt_imbalance;
		cell_type_costs = _cell_type_costs;
		opt_verbose = _opt_verbose;
		opt_nocleanup = _opt_nocleanup;

		//Build sigbit_to_edgenum and edge_nodes:
		create_hypergraph();
		log("Found %d nodes and %d hyperedges.\n", node_ctr, edge_ctr);

		//Create hypergraph partitioning problem:
		const std::string tempdir_name = make_temp_dir("/tmp/yosys-partition-XXXXXX");
		write_hypergraph(tempdir_name + "/problem.hgr");

		//Run hypergraph partitioning tool:
		call_solver(tempdir_name + "/problem.hgr", tempdir_name + "/problem.sol");

		//Recover partitions and cut edges:
		recover_partitions_edge_cuts(tempdir_name + "/problem.sol");
		if (!opt_nocleanup)
			remove_directory(tempdir_name);

		//Make partition submodules and move cells to them:
		create_partition_modules();

		//Finally, make a new module that instantiates and connects partition cells:
		create_partitioned_module();

		int64_t t_end = PerformanceTimer::query();
		log("Module %s partitioned %d ways with %d cut wires in %.3f seconds.\n", module->name.c_str(), partitions, cut_edge_ctr, (t_end - t_begin) * 1e-9f);
	}
};

struct PartitionPass : public Pass {
	PartitionPass() : Pass("partition", "split techmapped module into equal-sized parts") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    partition [options] [selection]\n");
		log("\n");
		log("This command splits a flat combinational gate-level module into partitions,\n");
		log("with an emphasis on minimizing the connectivity between partitions. Multiple\n");
		log("new modules will be created and selected, with names described by:\n");
		log("  `printf(\"%%s_partition%%d\", name, i)`,\n");
		log("where `name` is the name of the module being partitioned and `i` is the\n");
		log("partition number.\n");
		log("\n");
		log("Options: \n");
		log("\n");
		log("  -k <num partitions>\n");
		log("    Set the desired number of partitions (at least two).\n");
		log("\n");
		log("  -imbalance <percent>\n");
		log("    Allowed size mismatch between partitions. For example \"5\" allows 45%%/55%%.\n");
		log("    Must be between 1 and 49.\n");
		log("\n");
		log("  -cell-costs <option>\n");
		log("    Specify the weights cell types for the hypergraph partitioner and for option\n");
		log("    `-s` above. Acceptable options are \"default\" (which, confusingly, is not\n");
		log("    the default here), \"cmos\", and \"unit\", which is the default option.\n");
		log("\n");
		log("  -v\n");
		log("    Print verbose output.\n");
		log("\n");
		log("  -nocleanup\n");
		log("    Do not clean up temporary `/tmp/yosys-partition-XXXXXX` directory.\n");
		log("\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		int opt_k = -1, opt_imbalance = 5;
		bool opt_verbose = false, opt_nocleanup = false;
		RTLIL::Module *module = nullptr;
		dict<RTLIL::IdString, int> cell_type_costs = CellCosts::unit_gate_cost();
		size_t argidx = 1;

		log_header(design, "Executing PARTITION pass (splitting module into equal-sized parts).\n");
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-k") {
				if (args.size() <= argidx + 1)
					log_cmd_error("k value not specified.\n");
				else {
					int k = atoi(args[argidx+1].c_str());
					if (k >= 2)
						opt_k = k;
					else
						log_cmd_error("k must be at least 2.\n");
					argidx++;
				}
				continue;
			}
			else if (args[argidx] == "-imbalance") {
				if (args.size() <= argidx + 1)
					log_cmd_error("Imbalance value not specified.\n");
				else {
					int e = atoi(args[argidx+1].c_str());
					if (e >= 1 && e <= 49)
						opt_imbalance = e;
					else
						log_cmd_error("Specified imbalance value is out of range.\n");
					argidx++;
				}
				continue;
			}
			else if (args[argidx] == "-cell-costs") {
				if (args.size() <= argidx + 1)
					log_cmd_error("Cell cost type not specified.\n");
				else {
					std::string type = args[argidx+1].c_str();
					if (type == "default")
						cell_type_costs = CellCosts::default_gate_cost();
					if (type == "cmos")
						cell_type_costs = CellCosts::cmos_gate_cost();
					if (type == "unit")
						cell_type_costs = CellCosts::unit_gate_cost();
					else
						log_cmd_error("\"%s\" is not a known cell cost type.\n", type.c_str());
					argidx++;
				}
				continue;
			}
			else if (args[argidx] == "-v") {
				opt_verbose = true;
				continue;
			}
			else if (args[argidx] == "-nocleanup") {
				opt_nocleanup = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto m : design->selected_modules()){
			if (module != nullptr)
				log_cmd_error("This command can only operate on a single selected module.\n");
			else {
				if (!design->selected_whole_module(m->name))
					log_cmd_error("This command cannot operate on a partially-selected module.\n");
				module = m;
			}
		}

		PartitionWorker(design, module, opt_k, opt_imbalance, cell_type_costs, opt_verbose, opt_nocleanup);
	}
} PartitionPass;

PRIVATE_NAMESPACE_END
