/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Martin Povišer <povik@cutebit.org>
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

#include "kernel/sigtools.h"
#include "kernel/register.h"
#include "kernel/cellaigs.h"
#include "kernel/utils.h"
#include "kernel/ff.h"
#include "kernel/mem.h"

#include <assert.h>
#include <limits>

USING_YOSYS_NAMESPACE
template<> struct Yosys::hashlib::hash_ops<AigNode *> : Yosys::hashlib::hash_ptr_ops {};

PRIVATE_NAMESPACE_BEGIN

typedef long int arrivalint;
const arrivalint INF_PAST = std::numeric_limits<arrivalint>::min();

// each clock domain must have its own EstimateSta structure
struct EstimateSta {
	SigMap sigmap;
	Module *m;
	SigBit clk;

	dict<std::pair<RTLIL::IdString, dict<RTLIL::IdString, RTLIL::Const>>, Aig> aigs;
	dict<Cell *, Aig *> cell_aigs;

	std::vector<std::pair<Cell *, SigBit>> launchers;
	std::vector<std::pair<Cell *, SigBit>> samplers;
	bool all_paths = false;
	bool select = false;

	void add_seq(Cell *cell, SigSpec launch, SigSpec sample)
	{
		sigmap.apply(launch);
		sigmap.apply(sample);
		launch.sort_and_unify();
		sample.sort_and_unify();
		for (auto bit : launch)
			launchers.push_back(std::make_pair(cell, bit));
		for (auto bit : sample)
			samplers.push_back(std::make_pair(cell, bit));
	}

	// we include a discount factor for cells that can be implemented using carry chain logic
	// and to account for the AIG model not being balanced
	int cell_type_factor(IdString type)
	{
		if (type.in(ID($gt), ID($ge), ID($lt), ID($le), ID($add), ID($sub),
					ID($logic_not), ID($reduce_and), ID($reduce_or), ID($eq)))
			return 1;
		else
			return 2;
	}

	// TODO: ignores clock polarity
	EstimateSta(Module *m, SigBit clk)
		: sigmap(m), m(m), clk(clk)
	{
		sigmap.apply(clk);
	}

	void run()
	{
		log("Domain %s\n", log_signal(clk));

		// first, we collect launch and sample points and convert the combinational logic to AIG
		std::vector<Cell *> combinational;

		for (auto cell : m->cells()) {
			SigSpec launch, sample;
			if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
				// collect launch and sample points for FF cell
				FfData ff(nullptr, cell);
				if (!ff.has_clk) {
					log_warning("Ignoring unsupported storage element '%s' (%s)\n",
								log_id(cell), log_id(cell->type));
					continue;
				}
				if (ff.sig_clk != clk)
					continue;
				launch.append(ff.sig_q);
				sample.append(ff.sig_d);
				if (ff.has_ce)
					sample.append(ff.sig_ce);
				if (ff.has_srst)
					sample.append(ff.sig_srst);
				add_seq(cell, launch, sample);
			} else if (cell->is_mem_cell()) {
				// memories handled separately
				continue;
			} else if (cell->type == ID($scopeinfo)) {
				continue;
			} else {
				// find or build AIG model of combinational cell
				auto fingerprint = std::make_pair(cell->type, cell->parameters);
				if (!aigs.count(fingerprint)) {
					aigs.emplace(fingerprint, Aig(cell));
					if (aigs.at(fingerprint).name.empty()) {
						log_error("Unsupported cell '%s' in module '%s'",
								  log_id(cell->type), log_id(m));
					}					
				}

				combinational.push_back(cell);
				continue;
			}
		}

		// since we're now taking reference into `aigs`, we can no longer modify it
		// and thus have to fill `cell_aigs` in a separate loop
		for (auto cell : combinational) {
			auto fingerprint = std::make_pair(cell->type, cell->parameters);
			cell_aigs.emplace(cell, &aigs.at(fingerprint));
		}

		// collect launch and sample points for memory cells
		for (auto &mem : Mem::get_all_memories(m)) {
			for (auto &rd : mem.rd_ports) {
				if (!rd.clk_enable) {
					log_error("Unsupported async memory port '%s'\n", log_id(rd.cell));
					continue;
				}
				if (sigmap(rd.clk) != clk)
					continue;
				add_seq(rd.cell, rd.data, {rd.addr, rd.srst, rd.en});
			}
			for (auto &wr : mem.wr_ports) {
				if (sigmap(wr.clk) != clk)
					continue;
				add_seq(wr.cell, {}, {wr.en, wr.addr, wr.data});
			}
		}

		// now we toposort the combinational logic

		// each toposort node is either a SigBit or a pair of Cell * / AigNode *
		TopoSort<std::tuple<SigBit, Cell *, AigNode *>> topo;

		auto desc_aig = [&](Cell *cell, AigNode &node) {
			return std::make_tuple(RTLIL::S0, cell, &node);
		};
		auto desc_sig = [&](SigBit bit) {
			return std::make_tuple(sigmap(bit), (Cell *) NULL, (AigNode *) NULL);
		};

		// collect edges of the AIG graph
		for (auto cell : combinational) {
			assert(cell_aigs.count(cell));
			Aig &aig = *cell_aigs.at(cell);
			for (auto &node : aig.nodes) {
				if (!node.portname.empty()) {
					topo.edge(
						desc_sig(cell->getPort(node.portname)[node.portbit]),
						desc_aig(cell, node)
					);
				} else if (node.left_parent < 0 && node.right_parent < 0) {
					// constant, nothing to do
				} else {
					topo.edge(
						desc_aig(cell, aig.nodes[node.left_parent]),
						desc_aig(cell, node)
					);
					topo.edge(
						desc_aig(cell, aig.nodes[node.right_parent]),
						desc_aig(cell, node)
					);
				}

				for (auto &oport : node.outports) {
					topo.edge(
						desc_aig(cell, node),
						desc_sig(cell->getPort(oport.first)[oport.second])
					);
				}
			}
		}

		if (!topo.sort())
			log_error("Module '%s' contains combinational loops", log_id(m));
		
		// now we determine how long it takes for signals to stabilize
		
		// `levels` records the time after a clock edge after which a signal is stable
		dict<std::tuple<SigBit, Cell *, AigNode *>, arrivalint> levels;

		for (auto node : topo.sorted)
			levels[node] = INF_PAST;

		// launch points are at 0 by definition
		for (auto pair : launchers)
			levels[desc_sig(pair.second)] = 0;

		for (auto node : topo.sorted) {
			AigNode *aig_node = std::get<2>(node);
			if (aig_node) {
				Cell *cell = std::get<1>(node);
				Aig &aig = *cell_aigs.at(cell);
				if (!aig_node->portname.empty()) {
					// for a cell port, copy `levels` value from port bit
					SigBit bit = cell->getPort(aig_node->portname)[aig_node->portbit];
					levels[node] = levels[desc_sig(bit)];
				} else if (aig_node->left_parent < 0 && aig_node->right_parent < 0) {
					// constant, nothing to do
				} else {
					// for each AIG node, find maximum of parents and add a cell-specific delay
					int left = levels[desc_aig(cell, aig.nodes[aig_node->left_parent])];
					int right = levels[desc_aig(cell, aig.nodes[aig_node->right_parent])];
					levels[node] = (std::max(left, right) + cell_type_factor(cell->type));
				}

				// copy `levels` value to any output ports
				for (auto &oport : aig_node->outports) {
					levels[desc_sig(cell->getPort(oport.first)[oport.second])] = levels[node];
				}
			}
		}

		// now find the length of the critical path (slowest path in the design)
		arrivalint crit = INF_PAST;
		for (auto pair : samplers)
			if (levels[desc_sig(pair.second)] > crit)
				crit = levels[desc_sig(pair.second)];

		if (crit < 0) {
			log("No paths found\n");
			return;
		}

		log("Critical path is %ld nodes long:\n\n", crit);

		// we use dict instead of pool because dict gives us
		// some compile-time errors related to hashing
		dict<std::tuple<SigBit, Cell *, AigNode *>, bool> critical;

		// actually find one critical path, or all such paths if requested
		for (auto pair : samplers) {
			if (levels[desc_sig(pair.second)] == crit) {
				critical[desc_sig(pair.second)] = true;
				if (!all_paths)
					break;
			}
		}

		// walk backwards through toposorted nodes and set critical flag on nodes in critical path
		for (auto it = topo.sorted.rbegin(); it != topo.sorted.rend(); it++) {
			auto node = *it;
			AigNode *aig_node = std::get<2>(node);
			if (aig_node) {
				Cell *cell = std::get<1>(node);
				Aig &aig = *cell_aigs.at(cell);

				for (auto &oport : aig_node->outports) {
					if (critical.count(desc_sig(cell->getPort(oport.first)[oport.second])))
						critical[node] = true;
				}

				if (!aig_node->portname.empty()) {
					SigBit bit = cell->getPort(aig_node->portname)[aig_node->portbit];
					if (critical.count(node))
						critical[desc_sig(bit)] = true;
				} else if (aig_node->left_parent < 0 && aig_node->right_parent < 0) {
					// constant, nothing to do
				} else {
					// figure out which parent is on the critical path
					auto left = desc_aig(cell, aig.nodes[aig_node->left_parent]);
					auto right = desc_aig(cell, aig.nodes[aig_node->right_parent]);
					int crit_input_lvl = levels[node] - cell_type_factor(cell->type);
					if (critical.count(node)) {
						bool left_critical = (levels[left] == crit_input_lvl);
						bool right_critical = (levels[right] == crit_input_lvl);
						if (all_paths) {
							if (left_critical)
								critical[left] = true;
							if (right_critical)
								critical[right] = true;
						} else {
							if (left_critical)
								critical[left] = true;
							else if (right_critical)
								critical[right] = true;
						}
					}
				}
			}
		}

		// finally print the path we found
		SigPool bits_to_select;
		pool<IdString> to_select;

		pool<Cell *> printed;
		for (auto node : topo.sorted) {
			if (!critical.count(node))
				continue;
			AigNode *aig_node = std::get<2>(node);
			if (aig_node) {
				Cell *cell = std::get<1>(node);
				if (!printed.count(cell)) {
					to_select.insert(cell->name);
					std::string cell_src;
					if (cell->has_attribute(ID::src)) {
						std::string src_attr = cell->get_src_attribute();
						cell_src = stringf(" source: %s", src_attr.c_str());
					}
					log("    cell %s (%s)%s\n", log_id(cell), log_id(cell->type), cell_src.c_str());
					printed.insert(cell);
				}
			} else {
				SigBit bit = std::get<0>(node);
				bits_to_select.add(bit);
				std::string wire_src;
				if (bit.wire && bit.wire->has_attribute(ID::src)) {
					std::string src_attr = bit.wire->get_src_attribute();
					wire_src = stringf(" source: %s", src_attr.c_str());
				}
				log("    wire %s%s (level %ld)\n", log_signal(bit), wire_src.c_str(), levels[node]);
			}
		}

		for (auto wire : m->wires()) {
			if (bits_to_select.check_any(sigmap(wire)))
				to_select.insert(wire->name);
		}

		if (select) {
			RTLIL::Selection sel(false);
			for (auto member : to_select)
				sel.selected_members[m->name].insert(member);
			m->design->selection_stack.back() = sel;
			m->design->selection_stack.back().optimize(m->design);
		}
	}
};

struct TimeestPass : Pass {
	TimeestPass() : Pass("timeest", "estimate timing") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    timeest [-clk <clk_signal>] [options] [selection]\n");
		log("\n");
		log("Estimate the critical path in clock domain <clk_signal> by counting AIG nodes.\n");
		log("\n");
		log("    -all_paths\n");
		log("        Print or select nodes from all critical paths instead of focusing on\n");
		log("        a single illustratory path.\n");
		log("\n");
		log("    -select\n");
		log("        Select the nodes of a critical path\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing TIMEEST pass. (estimate timing)\n");

		std::string clk;
		bool all_paths = false;
		bool select = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-all_paths") {
				all_paths = true;
				continue;
			}
			if (args[argidx] == "-select") {
				select = true;
				continue;
			}
			if (args[argidx] == "-clk" && argidx + 1 < args.size()) {
				clk = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, d);

		if (clk.empty())
			log_cmd_error("No -clk argument provided\n");

		if (select && d->selected_modules().size() > 1)
			log_cmd_error("The -select option operates on a single selected module\n");

		for (auto m : d->selected_modules()) {
			if (!m->wire(RTLIL::escape_id(clk))) {
				log_warning("No domain '%s' in module %s\n", clk.c_str(), log_id(m));
				continue;
			}

			EstimateSta sta(m, SigBit(m->wire(RTLIL::escape_id(clk)), 0));
			sta.all_paths = all_paths;
			sta.select = select;
			sta.run();
		}
	}
} TimeestPass;

PRIVATE_NAMESPACE_END
