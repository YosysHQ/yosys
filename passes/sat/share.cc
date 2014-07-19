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

#include "kernel/rtlil.h"
#include "kernel/satgen.h"
#include "kernel/sigtools.h"
#include "kernel/modwalker.h"
#include "kernel/register.h"
#include "kernel/log.h"
#include <algorithm>

struct ShareWorkerConfig
{
	bool opt_all;
};

struct ShareWorker
{
	ShareWorkerConfig config;
	RTLIL::Design *design;
	RTLIL::Module *module;

	CellTypes cone_ct;
	ModWalker modwalker;

	// ---------------------------------------------------
	// Find shareable cells and compatible groups of cells
	// ---------------------------------------------------

	std::set<RTLIL::Cell*> shareable_cells;

	void find_shareable_cells()
	{
		std::vector<RTLIL::Cell*> candidates;

		for (auto &it : module->cells)
		{
			RTLIL::Cell *cell = it.second;

			if (!design->selected(module, cell) || !modwalker.ct.cell_known(cell->type))
				continue;

			if (config.opt_all) {
				candidates.push_back(cell);
				continue;
			}

			if (cell->type == "$memrd") {
				if (!cell->parameters.at("\\CLK_ENABLE").as_bool())
					candidates.push_back(cell);
				continue;
			}

			if (cell->type == "$mul" || cell->type == "$div" || cell->type == "$mod") {
				if (cell->parameters.at("\\Y_WIDTH").as_int() > 4)
					candidates.push_back(cell);
				continue;
			}

			if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr") {
				if (cell->parameters.at("\\Y_WIDTH").as_int() > 8)
					candidates.push_back(cell);
				continue;
			}
		}

		for (auto cell : candidates)
		{
			std::set<ModWalker::PortBit> driven_bits;
			modwalker.get_consumers(driven_bits, modwalker.cell_outputs[cell]);
			for (auto bit : driven_bits) {
				if (bit.cell->type != "$mux" && bit.cell->type != "$pmux")
					goto skip_candidate;
				if (bit.port != "\\A" && bit.port != "\\B")
					goto skip_candidate;
			}
			if (!modwalker.has_outputs(modwalker.cell_outputs[cell]))
				shareable_cells.insert(cell);
		skip_candidate:;
		}
	}

	bool is_shareable_pair(RTLIL::Cell *c1, RTLIL::Cell *c2)
	{
		if (c1->type != c2->type)
			return false;

		if (c1->type == "$memrd")
		{
			if (c1->parameters.at("\\MEMID").decode_string() != c2->parameters.at("\\MEMID").decode_string())
				return false;

			return true;
		}

		if (c1->type == "$mul" || c1->type == "$div" || c1->type == "$mod" ||
				c1->type == "$shl" || c1->type == "$shr" || c1->type == "$sshl" || c1->type == "$sshr")
		{
			if (c1->parameters.at("\\A_SIGNED").as_bool() != c2->parameters.at("\\A_SIGNED").as_bool())
				return false;

			if (c1->parameters.at("\\B_SIGNED").as_bool() != c2->parameters.at("\\B_SIGNED").as_bool())
				return false;

			int a1_width = c1->parameters.at("\\A_WIDTH").as_int();
			int b1_width = c1->parameters.at("\\B_WIDTH").as_int();
			int y1_width = c1->parameters.at("\\Y_WIDTH").as_int();

			int a2_width = c2->parameters.at("\\A_WIDTH").as_int();
			int b2_width = c2->parameters.at("\\B_WIDTH").as_int();
			int y2_width = c2->parameters.at("\\Y_WIDTH").as_int();

			if (std::max(a1_width, a2_width) > 2 * std::min(a1_width, a2_width)) return false;
			if (std::max(b1_width, b2_width) > 2 * std::min(b1_width, b2_width)) return false;
			if (std::max(y1_width, y2_width) > 2 * std::min(y1_width, y2_width)) return false;

			return true;
		}

		for (auto &it : c1->parameters)
			if (c2->parameters.count(it.first) == 0 || c2->parameters.at(it.first) != it.second)
				return false;

		for (auto &it : c2->parameters)
			if (c1->parameters.count(it.first) == 0 || c1->parameters.at(it.first) != it.second)
				return false;

		return true;
	}

	void find_shareable_partners(std::vector<RTLIL::Cell*> &results, RTLIL::Cell *cell)
	{
		results.clear();
		for (auto c : shareable_cells)
			if (c != cell && is_shareable_pair(c, cell))
				results.push_back(c);
	}


	// --------------------------------------------------------
	// Finding control inputs and activation pattern for a cell
	// --------------------------------------------------------

	std::map<RTLIL::Cell*, std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>>> activation_patterns_cache;

	void follow_mux_data_cone(std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &patterns,
			std::set<std::pair<RTLIL::SigBit, RTLIL::State>> &state, RTLIL::SigSpec signal)
	{
		std::set<ModWalker::PortBit> consumers;
		std::map<RTLIL::Cell*, std::set<ModWalker::PortBit>> consumers_by_cell;

		if (modwalker.has_outputs(signal))
			goto signal_outside_mux_tree;

		modwalker.get_consumers(consumers, signal);
		for (auto &bit : consumers) {
			if ((bit.cell->type != "$mux" && bit.cell->type != "$pmux") || bit.port == "\\S")
				goto signal_outside_mux_tree;
			consumers_by_cell[bit.cell].insert(bit);
		}

		if (0) {
	signal_outside_mux_tree:;
			RTLIL::SigSpec pattern_first, pattern_second;
			for (auto &bit : state) {
				pattern_first.append_bit(bit.first);
				pattern_second.append_bit(bit.second);
			}
			patterns.insert(std::pair<RTLIL::SigSpec, RTLIL::Const>(pattern_first, pattern_second.as_const()));
			return;
		}

		for (auto &it : consumers_by_cell)
		{
			RTLIL::Cell *cell = it.first;
			log_assert(cell->type == "$mux" || cell->type == "$pmux");

			int width = cell->parameters.at("\\WIDTH").as_int();
			std::set<int> used_in_b_parts;
			bool used_in_a = false;

			for (auto &bit : it.second) {
				if (bit.port == "\\A")
					used_in_a = true;
				else if (bit.port == "\\B")
					used_in_b_parts.insert(bit.offset / width);
				else
					log_abort();
			}

			std::vector<RTLIL::SigBit> sig_s = modwalker.sigmap(cell->connections.at("\\S")).to_sigbit_vector();

			if (used_in_a) {
				std::set<std::pair<RTLIL::SigBit, RTLIL::State>> new_state = state;
				for (auto &bit : sig_s) {
					std::pair<RTLIL::SigBit, RTLIL::State> this_state(bit, RTLIL::State::S0);
					std::pair<RTLIL::SigBit, RTLIL::State> this_inv_state(bit, RTLIL::State::S1);
					if (new_state.count(this_inv_state))
						goto conflict_in_a_port;
					new_state.insert(this_state);
				}
				follow_mux_data_cone(patterns, new_state, modwalker.sigmap(cell->connections.at("\\Y")));
			conflict_in_a_port:;
			}

			for (int part_idx : used_in_b_parts) {
				std::set<std::pair<RTLIL::SigBit, RTLIL::State>> new_state = state;
				std::pair<RTLIL::SigBit, RTLIL::State> this_state(sig_s.at(part_idx), RTLIL::State::S1);
				std::pair<RTLIL::SigBit, RTLIL::State> this_inv_state(sig_s.at(part_idx), RTLIL::State::S0);
				if (new_state.count(this_inv_state))
					goto conflict_in_b_port;
				new_state.insert(this_state);
				follow_mux_data_cone(patterns, new_state, modwalker.sigmap(cell->connections.at("\\Y")));
			conflict_in_b_port:;
			}
		}
	}

	const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &find_cell_activation_patterns(RTLIL::Cell *cell)
	{
		if (activation_patterns_cache.count(cell))
			return activation_patterns_cache.at(cell);

		std::set<std::pair<RTLIL::SigBit, RTLIL::State>> state;
		RTLIL::SigSpec cell_output_signal;

		for (auto &bit : modwalker.cell_outputs[cell])
			cell_output_signal.append_bit(bit);

		follow_mux_data_cone(activation_patterns_cache[cell], state, cell_output_signal);
		return activation_patterns_cache.at(cell);
	}

	RTLIL::SigSpec bits_from_activation_patterns(const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &activation_patterns)
	{
		std::set<RTLIL::SigBit> all_bits;
		for (auto &it : activation_patterns) {
			std::vector<RTLIL::SigBit> bits = it.first;
			all_bits.insert(bits.begin(), bits.end());
		}

		RTLIL::SigSpec signal;
		for (auto &bit : all_bits)
			signal.append_bit(bit);

		return signal;
	}


	// -------------
	// Setup and run
	// -------------

	ShareWorker(ShareWorkerConfig config, RTLIL::Design *design, RTLIL::Module *module) :
			config(config), design(design), module(module)
	{
		cone_ct.setup_internals();
		cone_ct.cell_types.erase("$mul");
		cone_ct.cell_types.erase("$mod");
		cone_ct.cell_types.erase("$div");
		cone_ct.cell_types.erase("$pow");
		cone_ct.cell_types.erase("$shl");
		cone_ct.cell_types.erase("$shr");
		cone_ct.cell_types.erase("$sshl");
		cone_ct.cell_types.erase("$sshr");

		modwalker.setup(design, module);
		find_shareable_cells();

		if (shareable_cells.size() < 2)
			return;

		log("Found %d cells in module %s that may be considered for resource sharing.\n",
				int(shareable_cells.size()), log_id(module));

		while (!shareable_cells.empty())
		{
			RTLIL::Cell *cell = *shareable_cells.begin();
			shareable_cells.erase(cell);

			log("  Analyzing resource sharing options for %s:\n", log_id(cell));

			std::vector<RTLIL::Cell*> candidates;
			find_shareable_partners(candidates, cell);

			if (candidates.empty()) {
				log("    No candidates found.\n");
				continue;
			}

			log("    Found %d candidates:", int(candidates.size()));
			for (auto c : candidates)
				log(" %s", log_id(c));
			log("\n");

			const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &cell_activation_patterns = find_cell_activation_patterns(cell);
			RTLIL::SigSpec cell_activation_signals = bits_from_activation_patterns(cell_activation_patterns);

			log("    Found %d activation_patterns using ctrl signal %s.\n", int(cell_activation_patterns.size()), log_signal(cell_activation_signals));

			if (cell_activation_patterns.empty())
				continue;

			for (auto other_cell : candidates)
			{
				log("    Analyzing resource sharing with %s:\n", log_id(other_cell));

				const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &other_cell_activation_patterns = find_cell_activation_patterns(other_cell);
				RTLIL::SigSpec other_cell_activation_signals = bits_from_activation_patterns(other_cell_activation_patterns);

				log("      Found %d activation_patterns using ctrl signal %s.\n",
						int(other_cell_activation_patterns.size()), log_signal(other_cell_activation_signals));

				if (other_cell_activation_patterns.empty())
					continue;

				ezDefaultSAT ez;
				SatGen satgen(&ez, &modwalker.sigmap);

				std::set<RTLIL::Cell*> sat_cells;
				std::set<RTLIL::SigBit> bits_queue;

				std::vector<int> cell_active, other_cell_active;
				RTLIL::SigSpec all_ctrl_signals;

				for (auto &p : cell_activation_patterns) {
					log("      Activation pattern for cell %s: %s = %s\n", log_id(cell), log_signal(p.first), log_signal(p.second));
					cell_active.push_back(ez.vec_eq(satgen.importSigSpec(p.first), satgen.importSigSpec(p.second)));
					all_ctrl_signals.append(p.first);
				}

				for (auto &p : other_cell_activation_patterns) {
					log("      Activation pattern for cell %s: %s = %s\n", log_id(other_cell), log_signal(p.first), log_signal(p.second));
					other_cell_active.push_back(ez.vec_eq(satgen.importSigSpec(p.first), satgen.importSigSpec(p.second)));
					all_ctrl_signals.append(p.first);
				}

				for (auto &bit : cell_activation_signals.to_sigbit_vector())
					bits_queue.insert(bit);

				for (auto &bit : other_cell_activation_signals.to_sigbit_vector())
					bits_queue.insert(bit);

				while (!bits_queue.empty())
				{
					std::set<ModWalker::PortBit> portbits;
					modwalker.get_drivers(portbits, bits_queue);
					bits_queue.clear();

					for (auto &pbit : portbits)
						if (sat_cells.count(pbit.cell) == 0 && cone_ct.cell_known(pbit.cell->type)) {
							// log("      Adding cell %s (%s) to SAT problem.\n", log_id(pbit.cell), log_id(pbit.cell->type));
							satgen.importCell(pbit.cell);
							sat_cells.insert(pbit.cell);
						}
				}

				all_ctrl_signals.sort_and_unify();
				std::vector<int> sat_model = satgen.importSigSpec(all_ctrl_signals);
				std::vector<bool> sat_model_values;

				ez.assume(ez.AND(ez.expression(ez.OpOr, cell_active), ez.expression(ez.OpOr, other_cell_active)));

				log("      Size of SAT problem: %d cells, %d variables, %d clauses\n",
						int(sat_cells.size()), ez.numCnfVariables(), ez.numCnfClauses());

				if (ez.solve(sat_model, sat_model_values)) {
					log("      According to the SAT solver this pair of cells can not be shared.\n");
					log("      Model from SAT solver: %s = %d'", log_signal(all_ctrl_signals), int(sat_model_values.size()));
					for (int i = int(sat_model_values.size())-1; i >= 0; i--)
						log("%c", sat_model_values[i] ? '1' : '0');
					log("\n");
					continue;
				}

				log("      According to the SAT solver this pair of cells can be shared.\n");
				log("      WARNING: Actually sharing the cells is not implemented yet.\n");
				shareable_cells.erase(other_cell);
				break;
			}
		}
	}
};

struct SharePass : public Pass {
	SharePass() : Pass("share", "perform sat-based resource sharing") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    share [options] [selection]\n");
		log("\n");
		log("This pass merges shareable resources into a single resource. A SAT solver\n");
		log("is used to determine if two resources are share-able.\n");
		log("\n");
		log("  -all\n");
		log("    Per default the selection of cells that is considered for sharing is\n");
		log("    narrowed using some built-in heuristics. With this option all selected\n");
		log("    cells are considered for resource sharing.\n");
		log("\n");
		log("    IMPORTANT NOTE: If the -all option is used then no cells with internal\n");
		log("    state must be selected!\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		ShareWorkerConfig config;
		config.opt_all = false;

		log_header("Executing SHARE pass (SAT-based resource sharing).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-all") {
				config.opt_all = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules)
			if (design->selected(mod_it.second))
				ShareWorker(config, design, mod_it.second);
	}
} SharePass;

