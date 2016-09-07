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
#include "kernel/satgen.h"
#include "kernel/sigtools.h"
#include "kernel/modtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool memcells_cmp(RTLIL::Cell *a, RTLIL::Cell *b)
{
	if (a->type == "$memrd" && b->type == "$memrd")
		return a->name < b->name;
	if (a->type == "$memrd" || b->type == "$memrd")
		return (a->type == "$memrd") < (b->type == "$memrd");
	return a->parameters.at("\\PRIORITY").as_int() < b->parameters.at("\\PRIORITY").as_int();
}

struct MemoryShareWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap, sigmap_xmux;
	ModWalker modwalker;
	CellTypes cone_ct;

	std::map<RTLIL::SigBit, std::pair<RTLIL::Cell*, int>> sig_to_mux;
	std::map<pair<std::set<std::map<SigBit, bool>>, SigBit>, SigBit> conditions_logic_cache;


	// -----------------------------------------------------------------
	// Converting feedbacks to async read ports to proper enable signals
	// -----------------------------------------------------------------

	bool find_data_feedback(const std::set<RTLIL::SigBit> &async_rd_bits, RTLIL::SigBit sig,
			std::map<RTLIL::SigBit, bool> &state, std::set<std::map<RTLIL::SigBit, bool>> &conditions)
	{
		if (async_rd_bits.count(sig)) {
			conditions.insert(state);
			return true;
		}

		if (sig_to_mux.count(sig) == 0)
			return false;

		RTLIL::Cell *cell = sig_to_mux.at(sig).first;
		int bit_idx = sig_to_mux.at(sig).second;

		std::vector<RTLIL::SigBit> sig_a = sigmap(cell->getPort("\\A"));
		std::vector<RTLIL::SigBit> sig_b = sigmap(cell->getPort("\\B"));
		std::vector<RTLIL::SigBit> sig_s = sigmap(cell->getPort("\\S"));
		std::vector<RTLIL::SigBit> sig_y = sigmap(cell->getPort("\\Y"));
		log_assert(sig_y.at(bit_idx) == sig);

		for (int i = 0; i < int(sig_s.size()); i++)
			if (state.count(sig_s[i]) && state.at(sig_s[i]) == true) {
				if (find_data_feedback(async_rd_bits, sig_b.at(bit_idx + i*sig_y.size()), state, conditions)) {
					RTLIL::SigSpec new_b = cell->getPort("\\B");
					new_b.replace(bit_idx + i*sig_y.size(), RTLIL::State::Sx);
					cell->setPort("\\B", new_b);
				}
				return false;
			}


		for (int i = 0; i < int(sig_s.size()); i++)
		{
			if (state.count(sig_s[i]) && state.at(sig_s[i]) == false)
				continue;

			std::map<RTLIL::SigBit, bool> new_state = state;
			new_state[sig_s[i]] = true;

			if (find_data_feedback(async_rd_bits, sig_b.at(bit_idx + i*sig_y.size()), new_state, conditions)) {
				RTLIL::SigSpec new_b = cell->getPort("\\B");
				new_b.replace(bit_idx + i*sig_y.size(), RTLIL::State::Sx);
				cell->setPort("\\B", new_b);
			}
		}

		std::map<RTLIL::SigBit, bool> new_state = state;
		for (int i = 0; i < int(sig_s.size()); i++)
			new_state[sig_s[i]] = false;

		if (find_data_feedback(async_rd_bits, sig_a.at(bit_idx), new_state, conditions)) {
			RTLIL::SigSpec new_a = cell->getPort("\\A");
			new_a.replace(bit_idx, RTLIL::State::Sx);
			cell->setPort("\\A", new_a);
		}

		return false;
	}

	RTLIL::SigBit conditions_to_logic(std::set<std::map<RTLIL::SigBit, bool>> &conditions, SigBit olden, int &created_conditions)
	{
		auto key = make_pair(conditions, olden);

		if (conditions_logic_cache.count(key))
			return conditions_logic_cache.at(key);

		RTLIL::SigSpec terms;
		for (auto &cond : conditions) {
			RTLIL::SigSpec sig1, sig2;
			for (auto &it : cond) {
				sig1.append_bit(it.first);
				sig2.append_bit(it.second ? RTLIL::State::S1 : RTLIL::State::S0);
			}
			terms.append(module->Ne(NEW_ID, sig1, sig2));
			created_conditions++;
		}

		if (olden.wire != nullptr || olden != State::S1)
			terms.append(olden);

		if (GetSize(terms) == 0)
			terms = State::S1;

		if (GetSize(terms) > 1)
			terms = module->ReduceAnd(NEW_ID, terms);

		return conditions_logic_cache[key] = terms;
	}

	void translate_rd_feedback_to_en(std::string memid, std::vector<RTLIL::Cell*> &rd_ports, std::vector<RTLIL::Cell*> &wr_ports)
	{
		std::map<RTLIL::SigSpec, std::vector<std::set<RTLIL::SigBit>>> async_rd_bits;
		std::map<RTLIL::SigBit, std::set<RTLIL::SigBit>> muxtree_upstream_map;
		std::set<RTLIL::SigBit> non_feedback_nets;

		for (auto wire : module->wires())
			if (wire->port_output) {
				std::vector<RTLIL::SigBit> bits = sigmap(wire);
				non_feedback_nets.insert(bits.begin(), bits.end());
			}

		for (auto cell : module->cells())
		{
			bool ignore_data_port = false;

			if (cell->type == "$mux" || cell->type == "$pmux")
			{
				std::vector<RTLIL::SigBit> sig_a = sigmap(cell->getPort("\\A"));
				std::vector<RTLIL::SigBit> sig_b = sigmap(cell->getPort("\\B"));
				std::vector<RTLIL::SigBit> sig_s = sigmap(cell->getPort("\\S"));
				std::vector<RTLIL::SigBit> sig_y = sigmap(cell->getPort("\\Y"));

				non_feedback_nets.insert(sig_s.begin(), sig_s.end());

				for (int i = 0; i < int(sig_y.size()); i++) {
					muxtree_upstream_map[sig_y[i]].insert(sig_a[i]);
					for (int j = 0; j < int(sig_s.size()); j++)
						muxtree_upstream_map[sig_y[i]].insert(sig_b[i + j*sig_y.size()]);
				}

				continue;
			}

			if ((cell->type == "$memwr" || cell->type == "$memrd") &&
					cell->parameters.at("\\MEMID").decode_string() == memid)
				ignore_data_port = true;

			for (auto conn : cell->connections())
			{
				if (ignore_data_port && conn.first == "\\DATA")
					continue;
				std::vector<RTLIL::SigBit> bits = sigmap(conn.second);
				non_feedback_nets.insert(bits.begin(), bits.end());
			}
		}

		std::set<RTLIL::SigBit> expand_non_feedback_nets = non_feedback_nets;
		while (!expand_non_feedback_nets.empty())
		{
			std::set<RTLIL::SigBit> new_expand_non_feedback_nets;

			for (auto &bit : expand_non_feedback_nets)
				if (muxtree_upstream_map.count(bit))
					for (auto &new_bit : muxtree_upstream_map.at(bit))
						if (!non_feedback_nets.count(new_bit)) {
							non_feedback_nets.insert(new_bit);
							new_expand_non_feedback_nets.insert(new_bit);
						}

			expand_non_feedback_nets.swap(new_expand_non_feedback_nets);
		}

		for (auto cell : rd_ports)
		{
			if (cell->parameters.at("\\CLK_ENABLE").as_bool())
				continue;

			RTLIL::SigSpec sig_addr = sigmap(cell->getPort("\\ADDR"));
			std::vector<RTLIL::SigBit> sig_data = sigmap(cell->getPort("\\DATA"));

			for (int i = 0; i < int(sig_data.size()); i++)
				if (non_feedback_nets.count(sig_data[i]))
					goto not_pure_feedback_port;

			async_rd_bits[sig_addr].resize(max(async_rd_bits.size(), sig_data.size()));
			for (int i = 0; i < int(sig_data.size()); i++)
				async_rd_bits[sig_addr][i].insert(sig_data[i]);

		not_pure_feedback_port:;
		}

		if (async_rd_bits.empty())
			return;

		log("Populating enable bits on write ports of memory %s.%s with aync read feedback:\n", log_id(module), log_id(memid));

		for (auto cell : wr_ports)
		{
			RTLIL::SigSpec sig_addr = sigmap_xmux(cell->getPort("\\ADDR"));
			if (!async_rd_bits.count(sig_addr))
				continue;

			log("  Analyzing write port %s.\n", log_id(cell));

			std::vector<RTLIL::SigBit> cell_data = cell->getPort("\\DATA");
			std::vector<RTLIL::SigBit> cell_en = cell->getPort("\\EN");

			int created_conditions = 0;
			for (int i = 0; i < int(cell_data.size()); i++)
				if (cell_en[i] != RTLIL::SigBit(RTLIL::State::S0))
				{
					std::map<RTLIL::SigBit, bool> state;
					std::set<std::map<RTLIL::SigBit, bool>> conditions;

					find_data_feedback(async_rd_bits.at(sig_addr).at(i), cell_data[i], state, conditions);
					cell_en[i] = conditions_to_logic(conditions, cell_en[i], created_conditions);
				}

			if (created_conditions) {
				log("    Added enable logic for %d different cases.\n", created_conditions);
				cell->setPort("\\EN", cell_en);
			}
		}
	}


	// ------------------------------------------------------
	// Consolidate write ports that write to the same address
	// ------------------------------------------------------

	RTLIL::SigSpec mask_en_naive(RTLIL::SigSpec do_mask, RTLIL::SigSpec bits, RTLIL::SigSpec mask_bits)
	{
		// this is the naive version of the function that does not care about grouping the EN bits.

		RTLIL::SigSpec inv_mask_bits = module->Not(NEW_ID, mask_bits);
		RTLIL::SigSpec inv_mask_bits_filtered = module->Mux(NEW_ID, RTLIL::SigSpec(RTLIL::State::S1, bits.size()), inv_mask_bits, do_mask);
		RTLIL::SigSpec result = module->And(NEW_ID, inv_mask_bits_filtered, bits);
		return result;
	}

	RTLIL::SigSpec mask_en_grouped(RTLIL::SigSpec do_mask, RTLIL::SigSpec bits, RTLIL::SigSpec mask_bits)
	{
		// this version of the function preserves the bit grouping in the EN bits.

		std::vector<RTLIL::SigBit> v_bits = bits;
		std::vector<RTLIL::SigBit> v_mask_bits = mask_bits;

		std::map<std::pair<RTLIL::SigBit, RTLIL::SigBit>, std::pair<int, std::vector<int>>> groups;
		RTLIL::SigSpec grouped_bits, grouped_mask_bits;

		for (int i = 0; i < bits.size(); i++) {
			std::pair<RTLIL::SigBit, RTLIL::SigBit> key(v_bits[i], v_mask_bits[i]);
			if (groups.count(key) == 0) {
				groups[key].first = grouped_bits.size();
				grouped_bits.append_bit(v_bits[i]);
				grouped_mask_bits.append_bit(v_mask_bits[i]);
			}
			groups[key].second.push_back(i);
		}

		std::vector<RTLIL::SigBit> grouped_result = mask_en_naive(do_mask, grouped_bits, grouped_mask_bits);
		RTLIL::SigSpec result;

		for (int i = 0; i < bits.size(); i++) {
			std::pair<RTLIL::SigBit, RTLIL::SigBit> key(v_bits[i], v_mask_bits[i]);
			result.append_bit(grouped_result.at(groups.at(key).first));
		}

		return result;
	}

	void merge_en_data(RTLIL::SigSpec &merged_en, RTLIL::SigSpec &merged_data, RTLIL::SigSpec next_en, RTLIL::SigSpec next_data)
	{
		std::vector<RTLIL::SigBit> v_old_en = merged_en;
		std::vector<RTLIL::SigBit> v_next_en = next_en;

		// The new merged_en signal is just the old merged_en signal and next_en OR'ed together.
		// But of course we need to preserve the bit grouping..

		std::map<std::pair<RTLIL::SigBit, RTLIL::SigBit>, int> groups;
		std::vector<RTLIL::SigBit> grouped_old_en, grouped_next_en;
		RTLIL::SigSpec new_merged_en;

		for (int i = 0; i < int(v_old_en.size()); i++) {
			std::pair<RTLIL::SigBit, RTLIL::SigBit> key(v_old_en[i], v_next_en[i]);
			if (groups.count(key) == 0) {
				groups[key] = grouped_old_en.size();
				grouped_old_en.push_back(key.first);
				grouped_next_en.push_back(key.second);
			}
		}

		std::vector<RTLIL::SigBit> grouped_new_en = module->Or(NEW_ID, grouped_old_en, grouped_next_en);

		for (int i = 0; i < int(v_old_en.size()); i++) {
			std::pair<RTLIL::SigBit, RTLIL::SigBit> key(v_old_en[i], v_next_en[i]);
			new_merged_en.append_bit(grouped_new_en.at(groups.at(key)));
		}

		// Create the new merged_data signal.

		RTLIL::SigSpec new_merged_data(RTLIL::State::Sx, merged_data.size());

		RTLIL::SigSpec old_data_set = module->And(NEW_ID, merged_en, merged_data);
		RTLIL::SigSpec old_data_unset = module->And(NEW_ID, merged_en, module->Not(NEW_ID, merged_data));

		RTLIL::SigSpec new_data_set = module->And(NEW_ID, next_en, next_data);
		RTLIL::SigSpec new_data_unset = module->And(NEW_ID, next_en, module->Not(NEW_ID, next_data));

		new_merged_data = module->Or(NEW_ID, new_merged_data, old_data_set);
		new_merged_data = module->And(NEW_ID, new_merged_data, module->Not(NEW_ID, old_data_unset));

		new_merged_data = module->Or(NEW_ID, new_merged_data, new_data_set);
		new_merged_data = module->And(NEW_ID, new_merged_data, module->Not(NEW_ID, new_data_unset));

		// Update merged_* signals

		merged_en = new_merged_en;
		merged_data = new_merged_data;
	}

	void consolidate_wr_by_addr(std::string memid, std::vector<RTLIL::Cell*> &wr_ports)
	{
		if (wr_ports.size() <= 1)
			return;

		log("Consolidating write ports of memory %s.%s by address:\n", log_id(module), log_id(memid));

		std::map<RTLIL::SigSpec, int> last_port_by_addr;
		std::vector<std::vector<bool>> active_bits_on_port;

		bool cache_clk_enable = false;
		bool cache_clk_polarity = false;
		RTLIL::SigSpec cache_clk;

		for (int i = 0; i < int(wr_ports.size()); i++)
		{
			RTLIL::Cell *cell = wr_ports.at(i);
			RTLIL::SigSpec addr = sigmap_xmux(cell->getPort("\\ADDR"));

			if (cell->parameters.at("\\CLK_ENABLE").as_bool() != cache_clk_enable ||
					(cache_clk_enable && (sigmap(cell->getPort("\\CLK")) != cache_clk ||
					cell->parameters.at("\\CLK_POLARITY").as_bool() != cache_clk_polarity)))
			{
				cache_clk_enable = cell->parameters.at("\\CLK_ENABLE").as_bool();
				cache_clk_polarity = cell->parameters.at("\\CLK_POLARITY").as_bool();
				cache_clk = sigmap(cell->getPort("\\CLK"));
				last_port_by_addr.clear();

				if (cache_clk_enable)
					log("  New clock domain: %s %s\n", cache_clk_polarity ? "posedge" : "negedge", log_signal(cache_clk));
				else
					log("  New clock domain: unclocked\n");
			}

			log("    Port %d (%s) has addr %s.\n", i, log_id(cell), log_signal(addr));

			log("      Active bits: ");
			std::vector<RTLIL::SigBit> en_bits = sigmap(cell->getPort("\\EN"));
			active_bits_on_port.push_back(std::vector<bool>(en_bits.size()));
			for (int k = int(en_bits.size())-1; k >= 0; k--) {
				active_bits_on_port[i][k] = en_bits[k].wire != NULL || en_bits[k].data != RTLIL::State::S0;
				log("%c", active_bits_on_port[i][k] ? '1' : '0');
			}
			log("\n");

			if (last_port_by_addr.count(addr))
			{
				int last_i = last_port_by_addr.at(addr);
				log("      Merging port %d into this one.\n", last_i);

				bool found_overlapping_bits = false;
				for (int k = 0; k < int(en_bits.size()); k++) {
					if (active_bits_on_port[i][k] && active_bits_on_port[last_i][k])
						found_overlapping_bits = true;
					active_bits_on_port[i][k] = active_bits_on_port[i][k] || active_bits_on_port[last_i][k];
				}

				// Force this ports addr input to addr directly (skip don't care muxes)

				cell->setPort("\\ADDR", addr);

				// If any of the ports between `last_i' and `i' write to the same address, this
				// will have priority over whatever `last_i` wrote. So we need to revisit those
				// ports and mask the EN bits accordingly.

				RTLIL::SigSpec merged_en = sigmap(wr_ports[last_i]->getPort("\\EN"));

				for (int j = last_i+1; j < i; j++)
				{
					if (wr_ports[j] == NULL)
						continue;

					for (int k = 0; k < int(en_bits.size()); k++)
						if (active_bits_on_port[i][k] && active_bits_on_port[j][k])
							goto found_overlapping_bits_i_j;

					if (0) {
				found_overlapping_bits_i_j:
						log("      Creating collosion-detect logic for port %d.\n", j);
						RTLIL::SigSpec is_same_addr = module->addWire(NEW_ID);
						module->addEq(NEW_ID, addr, wr_ports[j]->getPort("\\ADDR"), is_same_addr);
						merged_en = mask_en_grouped(is_same_addr, merged_en, sigmap(wr_ports[j]->getPort("\\EN")));
					}
				}

				// Then we need to merge the (masked) EN and the DATA signals.

				RTLIL::SigSpec merged_data = wr_ports[last_i]->getPort("\\DATA");
				if (found_overlapping_bits) {
					log("      Creating logic for merging DATA and EN ports.\n");
					merge_en_data(merged_en, merged_data, sigmap(cell->getPort("\\EN")), sigmap(cell->getPort("\\DATA")));
				} else {
					RTLIL::SigSpec cell_en = sigmap(cell->getPort("\\EN"));
					RTLIL::SigSpec cell_data = sigmap(cell->getPort("\\DATA"));
					for (int k = 0; k < int(en_bits.size()); k++)
						if (!active_bits_on_port[last_i][k]) {
							merged_en.replace(k, cell_en.extract(k, 1));
							merged_data.replace(k, cell_data.extract(k, 1));
						}
				}

				// Connect the new EN and DATA signals and remove the old write port.

				cell->setPort("\\EN", merged_en);
				cell->setPort("\\DATA", merged_data);

				module->remove(wr_ports[last_i]);
				wr_ports[last_i] = NULL;

				log("      Active bits: ");
				std::vector<RTLIL::SigBit> en_bits = sigmap(cell->getPort("\\EN"));
				active_bits_on_port.push_back(std::vector<bool>(en_bits.size()));
				for (int k = int(en_bits.size())-1; k >= 0; k--)
					log("%c", active_bits_on_port[i][k] ? '1' : '0');
				log("\n");
			}

			last_port_by_addr[addr] = i;
		}

		// Clean up `wr_ports': remove all NULL entries

		std::vector<RTLIL::Cell*> wr_ports_with_nulls;
		wr_ports_with_nulls.swap(wr_ports);

		for (auto cell : wr_ports_with_nulls)
			if (cell != NULL)
				wr_ports.push_back(cell);
	}


	// --------------------------------------------------------
	// Consolidate write ports using sat-based resource sharing
	// --------------------------------------------------------

	void consolidate_wr_using_sat(std::string memid, std::vector<RTLIL::Cell*> &wr_ports)
	{
		if (wr_ports.size() <= 1)
			return;

		ezSatPtr ez;
		SatGen satgen(ez.get(), &modwalker.sigmap);

		// find list of considered ports and port pairs

		std::set<int> considered_ports;
		std::set<int> considered_port_pairs;

		for (int i = 0; i < int(wr_ports.size()); i++) {
			std::vector<RTLIL::SigBit> bits = modwalker.sigmap(wr_ports[i]->getPort("\\EN"));
			for (auto bit : bits)
				if (bit == RTLIL::State::S1)
					goto port_is_always_active;
			if (modwalker.has_drivers(bits))
				considered_ports.insert(i);
		port_is_always_active:;
		}

		log("Consolidating write ports of memory %s.%s using sat-based resource sharing:\n", log_id(module), log_id(memid));

		bool cache_clk_enable = false;
		bool cache_clk_polarity = false;
		RTLIL::SigSpec cache_clk;

		for (int i = 0; i < int(wr_ports.size()); i++)
		{
			RTLIL::Cell *cell = wr_ports.at(i);

			if (cell->parameters.at("\\CLK_ENABLE").as_bool() != cache_clk_enable ||
					(cache_clk_enable && (sigmap(cell->getPort("\\CLK")) != cache_clk ||
					cell->parameters.at("\\CLK_POLARITY").as_bool() != cache_clk_polarity)))
			{
				cache_clk_enable = cell->parameters.at("\\CLK_ENABLE").as_bool();
				cache_clk_polarity = cell->parameters.at("\\CLK_POLARITY").as_bool();
				cache_clk = sigmap(cell->getPort("\\CLK"));
			}
			else if (i > 0 && considered_ports.count(i-1) && considered_ports.count(i))
				considered_port_pairs.insert(i);

			if (cache_clk_enable)
				log("  Port %d (%s) on %s %s: %s\n", i, log_id(cell),
						cache_clk_polarity ? "posedge" : "negedge", log_signal(cache_clk),
						considered_ports.count(i) ? "considered" : "not considered");
			else
				log("  Port %d (%s) unclocked: %s\n", i, log_id(cell),
						considered_ports.count(i) ? "considered" : "not considered");
		}

		if (considered_port_pairs.size() < 1) {
			log("  No two subsequent ports in same clock domain considered -> nothing to consolidate.\n");
			return;
		}

		// create SAT representation of common input cone of all considered EN signals

		pool<Wire*> one_hot_wires;
		std::set<RTLIL::Cell*> sat_cells;
		std::set<RTLIL::SigBit> bits_queue;
		std::map<int, int> port_to_sat_variable;

		for (int i = 0; i < int(wr_ports.size()); i++)
			if (considered_port_pairs.count(i) || considered_port_pairs.count(i+1))
			{
				RTLIL::SigSpec sig = modwalker.sigmap(wr_ports[i]->getPort("\\EN"));
				port_to_sat_variable[i] = ez->expression(ez->OpOr, satgen.importSigSpec(sig));

				std::vector<RTLIL::SigBit> bits = sig;
				bits_queue.insert(bits.begin(), bits.end());
			}

		while (!bits_queue.empty())
		{
			for (auto bit : bits_queue)
				if (bit.wire && bit.wire->get_bool_attribute("\\onehot"))
					one_hot_wires.insert(bit.wire);

			pool<ModWalker::PortBit> portbits;
			modwalker.get_drivers(portbits, bits_queue);
			bits_queue.clear();

			for (auto &pbit : portbits)
				if (sat_cells.count(pbit.cell) == 0 && cone_ct.cell_known(pbit.cell->type)) {
					pool<RTLIL::SigBit> &cell_inputs = modwalker.cell_inputs[pbit.cell];
					bits_queue.insert(cell_inputs.begin(), cell_inputs.end());
					sat_cells.insert(pbit.cell);
				}
		}

		for (auto wire : one_hot_wires) {
			log("  Adding one-hot constraint for wire %s.\n", log_id(wire));
			vector<int> ez_wire_bits = satgen.importSigSpec(wire);
			for (int i : ez_wire_bits)
			for (int j : ez_wire_bits)
				if (i != j) ez->assume(ez->NOT(i), j);
		}

		log("  Common input cone for all EN signals: %d cells.\n", int(sat_cells.size()));

		for (auto cell : sat_cells)
			satgen.importCell(cell);

		log("  Size of unconstrained SAT problem: %d variables, %d clauses\n", ez->numCnfVariables(), ez->numCnfClauses());

		// merge subsequent ports if possible

		for (int i = 0; i < int(wr_ports.size()); i++)
		{
			if (!considered_port_pairs.count(i))
				continue;

			if (ez->solve(port_to_sat_variable.at(i-1), port_to_sat_variable.at(i))) {
				log("  According to SAT solver sharing of port %d with port %d is not possible.\n", i-1, i);
				continue;
			}

			log("  Merging port %d into port %d.\n", i-1, i);
			port_to_sat_variable.at(i) = ez->OR(port_to_sat_variable.at(i-1), port_to_sat_variable.at(i));

			RTLIL::SigSpec last_addr = wr_ports[i-1]->getPort("\\ADDR");
			RTLIL::SigSpec last_data = wr_ports[i-1]->getPort("\\DATA");
			std::vector<RTLIL::SigBit> last_en = modwalker.sigmap(wr_ports[i-1]->getPort("\\EN"));

			RTLIL::SigSpec this_addr = wr_ports[i]->getPort("\\ADDR");
			RTLIL::SigSpec this_data = wr_ports[i]->getPort("\\DATA");
			std::vector<RTLIL::SigBit> this_en = modwalker.sigmap(wr_ports[i]->getPort("\\EN"));

			RTLIL::SigBit this_en_active = module->ReduceOr(NEW_ID, this_en);

			if (GetSize(last_addr) < GetSize(this_addr))
				last_addr.extend_u0(GetSize(this_addr));
			else
				this_addr.extend_u0(GetSize(last_addr));

			wr_ports[i]->setParam("\\ABITS", GetSize(this_addr));
			wr_ports[i]->setPort("\\ADDR", module->Mux(NEW_ID, last_addr, this_addr, this_en_active));
			wr_ports[i]->setPort("\\DATA", module->Mux(NEW_ID, last_data, this_data, this_en_active));

			std::map<std::pair<RTLIL::SigBit, RTLIL::SigBit>, int> groups_en;
			RTLIL::SigSpec grouped_last_en, grouped_this_en, en;
			RTLIL::Wire *grouped_en = module->addWire(NEW_ID, 0);

			for (int j = 0; j < int(this_en.size()); j++) {
				std::pair<RTLIL::SigBit, RTLIL::SigBit> key(last_en[j], this_en[j]);
				if (!groups_en.count(key)) {
					grouped_last_en.append_bit(last_en[j]);
					grouped_this_en.append_bit(this_en[j]);
					groups_en[key] = grouped_en->width;
					grouped_en->width++;
				}
				en.append(RTLIL::SigSpec(grouped_en, groups_en[key]));
			}

			module->addMux(NEW_ID, grouped_last_en, grouped_this_en, this_en_active, grouped_en);
			wr_ports[i]->setPort("\\EN", en);

			module->remove(wr_ports[i-1]);
			wr_ports[i-1] = NULL;
		}

		// Clean up `wr_ports': remove all NULL entries

		std::vector<RTLIL::Cell*> wr_ports_with_nulls;
		wr_ports_with_nulls.swap(wr_ports);

		for (auto cell : wr_ports_with_nulls)
			if (cell != NULL)
				wr_ports.push_back(cell);
	}


	// -------------
	// Setup and run
	// -------------

	MemoryShareWorker(RTLIL::Design *design, RTLIL::Module *module) :
			design(design), module(module), sigmap(module)
	{
		std::map<std::string, std::pair<std::vector<RTLIL::Cell*>, std::vector<RTLIL::Cell*>>> memindex;

		sigmap_xmux = sigmap;
		for (auto cell : module->cells())
		{
			if (cell->type == "$memrd")
				memindex[cell->parameters.at("\\MEMID").decode_string()].first.push_back(cell);

			if (cell->type == "$memwr")
				memindex[cell->parameters.at("\\MEMID").decode_string()].second.push_back(cell);

			if (cell->type == "$mux")
			{
				RTLIL::SigSpec sig_a = sigmap_xmux(cell->getPort("\\A"));
				RTLIL::SigSpec sig_b = sigmap_xmux(cell->getPort("\\B"));

				if (sig_a.is_fully_undef())
					sigmap_xmux.add(cell->getPort("\\Y"), sig_b);
				else if (sig_b.is_fully_undef())
					sigmap_xmux.add(cell->getPort("\\Y"), sig_a);
			}

			if (cell->type == "$mux" || cell->type == "$pmux")
			{
				std::vector<RTLIL::SigBit> sig_y = sigmap(cell->getPort("\\Y"));
				for (int i = 0; i < int(sig_y.size()); i++)
					sig_to_mux[sig_y[i]] = std::pair<RTLIL::Cell*, int>(cell, i);
			}
		}

		for (auto &it : memindex) {
			std::sort(it.second.first.begin(), it.second.first.end(), memcells_cmp);
			std::sort(it.second.second.begin(), it.second.second.end(), memcells_cmp);
			translate_rd_feedback_to_en(it.first, it.second.first, it.second.second);
			consolidate_wr_by_addr(it.first, it.second.second);
		}

		cone_ct.setup_internals();
		cone_ct.cell_types.erase("$mul");
		cone_ct.cell_types.erase("$mod");
		cone_ct.cell_types.erase("$div");
		cone_ct.cell_types.erase("$pow");
		cone_ct.cell_types.erase("$shl");
		cone_ct.cell_types.erase("$shr");
		cone_ct.cell_types.erase("$sshl");
		cone_ct.cell_types.erase("$sshr");
		cone_ct.cell_types.erase("$shift");
		cone_ct.cell_types.erase("$shiftx");

		modwalker.setup(design, module, &cone_ct);

		for (auto &it : memindex)
			consolidate_wr_using_sat(it.first, it.second.second);
	}
};

struct MemorySharePass : public Pass {
	MemorySharePass() : Pass("memory_share", "consolidate memory ports") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_share [selection]\n");
		log("\n");
		log("This pass merges share-able memory ports into single memory ports.\n");
		log("\n");
		log("The following methods are used to consolidate the number of memory ports:\n");
		log("\n");
		log("  - When write ports are connected to async read ports accessing the same\n");
		log("    address, then this feedback path is converted to a write port with\n");
		log("    byte/part enable signals.\n");
		log("\n");
		log("  - When multiple write ports access the same address then this is converted\n");
		log("    to a single write port with a more complex data and/or enable logic path.\n");
		log("\n");
		log("  - When multiple write ports are never accessed at the same time (a SAT\n");
		log("    solver is used to determine this), then the ports are merged into a single\n");
		log("    write port.\n");
		log("\n");
		log("Note that in addition to the algorithms implemented in this pass, the $memrd\n");
		log("and $memwr cells are also subject to generic resource sharing passes (and other\n");
		log("optimizations) such as \"share\" and \"opt_merge\".\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		log_header(design, "Executing MEMORY_SHARE pass (consolidating $memrd/$memwr cells).\n");
		extra_args(args, 1, design);
		for (auto module : design->selected_modules())
			MemoryShareWorker(design, module);
	}
} MemorySharePass;

PRIVATE_NAMESPACE_END
