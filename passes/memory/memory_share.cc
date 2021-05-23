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
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryShareWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap, sigmap_xmux;
	ModWalker modwalker;
	CellTypes cone_ct;


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
				grouped_bits.append(v_bits[i]);
				grouped_mask_bits.append(v_mask_bits[i]);
			}
			groups[key].second.push_back(i);
		}

		std::vector<RTLIL::SigBit> grouped_result = mask_en_naive(do_mask, grouped_bits, grouped_mask_bits);
		RTLIL::SigSpec result;

		for (int i = 0; i < bits.size(); i++) {
			std::pair<RTLIL::SigBit, RTLIL::SigBit> key(v_bits[i], v_mask_bits[i]);
			result.append(grouped_result.at(groups.at(key).first));
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
			new_merged_en.append(grouped_new_en.at(groups.at(key)));
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

	void consolidate_wr_by_addr(Mem &mem)
	{
		if (GetSize(mem.wr_ports) <= 1)
			return;

		log("Consolidating write ports of memory %s.%s by address:\n", log_id(module), log_id(mem.memid));

		std::map<RTLIL::SigSpec, int> last_port_by_addr;
		std::vector<std::vector<bool>> active_bits_on_port;

		bool cache_clk_enable = false;
		bool cache_clk_polarity = false;
		RTLIL::SigSpec cache_clk;

		bool changed = false;

		for (int i = 0; i < GetSize(mem.wr_ports); i++)
		{
			auto &port = mem.wr_ports[i];
			RTLIL::SigSpec addr = sigmap_xmux(port.addr);

			if (port.clk_enable != cache_clk_enable ||
					(cache_clk_enable && (sigmap(port.clk) != cache_clk ||
					port.clk_polarity != cache_clk_polarity)))
			{
				cache_clk_enable = port.clk_enable;
				cache_clk_polarity = port.clk_polarity;
				cache_clk = sigmap(port.clk);
				last_port_by_addr.clear();

				if (cache_clk_enable)
					log("  New clock domain: %s %s\n", cache_clk_polarity ? "posedge" : "negedge", log_signal(cache_clk));
				else
					log("  New clock domain: unclocked\n");
			}

			log("    Port %d has addr %s.\n", i, log_signal(addr));

			log("      Active bits: ");
			std::vector<RTLIL::SigBit> en_bits = sigmap(port.en);
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

				port.addr = addr;

				// If any of the ports between `last_i' and `i' write to the same address, this
				// will have priority over whatever `last_i` wrote. So we need to revisit those
				// ports and mask the EN bits accordingly.

				RTLIL::SigSpec merged_en = sigmap(mem.wr_ports[last_i].en);

				for (int j = last_i+1; j < i; j++)
				{
					if (mem.wr_ports[j].removed)
						continue;

					for (int k = 0; k < int(en_bits.size()); k++)
						if (active_bits_on_port[i][k] && active_bits_on_port[j][k])
							goto found_overlapping_bits_i_j;

					if (0) {
				found_overlapping_bits_i_j:
						log("      Creating collosion-detect logic for port %d.\n", j);
						RTLIL::SigSpec is_same_addr = module->addWire(NEW_ID);
						module->addEq(NEW_ID, addr, mem.wr_ports[j].addr, is_same_addr);
						merged_en = mask_en_grouped(is_same_addr, merged_en, sigmap(mem.wr_ports[j].en));
					}
				}

				// Then we need to merge the (masked) EN and the DATA signals.

				RTLIL::SigSpec merged_data = mem.wr_ports[last_i].data;
				if (found_overlapping_bits) {
					log("      Creating logic for merging DATA and EN ports.\n");
					merge_en_data(merged_en, merged_data, sigmap(port.en), sigmap(port.data));
				} else {
					RTLIL::SigSpec cell_en = sigmap(port.en);
					RTLIL::SigSpec cell_data = sigmap(port.data);
					for (int k = 0; k < int(en_bits.size()); k++)
						if (!active_bits_on_port[last_i][k]) {
							merged_en.replace(k, cell_en.extract(k, 1));
							merged_data.replace(k, cell_data.extract(k, 1));
						}
				}

				// Connect the new EN and DATA signals and remove the old write port.

				port.en = merged_en;
				port.data = merged_data;

				mem.wr_ports[last_i].removed = true;
				changed = true;

				log("      Active bits: ");
				std::vector<RTLIL::SigBit> en_bits = sigmap(port.en);
				active_bits_on_port.push_back(std::vector<bool>(en_bits.size()));
				for (int k = int(en_bits.size())-1; k >= 0; k--)
					log("%c", active_bits_on_port[i][k] ? '1' : '0');
				log("\n");
			}

			last_port_by_addr[addr] = i;
		}

		if (changed)
			mem.emit();
	}


	// --------------------------------------------------------
	// Consolidate write ports using sat-based resource sharing
	// --------------------------------------------------------

	void consolidate_wr_using_sat(Mem &mem)
	{
		if (GetSize(mem.wr_ports) <= 1)
			return;

		ezSatPtr ez;
		SatGen satgen(ez.get(), &modwalker.sigmap);

		// find list of considered ports and port pairs

		std::set<int> considered_ports;
		std::set<int> considered_port_pairs;

		for (int i = 0; i < GetSize(mem.wr_ports); i++) {
			auto &port = mem.wr_ports[i];
			std::vector<RTLIL::SigBit> bits = modwalker.sigmap(port.en);
			for (auto bit : bits)
				if (bit == RTLIL::State::S1)
					goto port_is_always_active;
			if (modwalker.has_drivers(bits))
				considered_ports.insert(i);
		port_is_always_active:;
		}

		log("Consolidating write ports of memory %s.%s using sat-based resource sharing:\n", log_id(module), log_id(mem.memid));

		bool cache_clk_enable = false;
		bool cache_clk_polarity = false;
		RTLIL::SigSpec cache_clk;

		for (int i = 0; i < GetSize(mem.wr_ports); i++)
		{
			auto &port = mem.wr_ports[i];

			if (port.clk_enable != cache_clk_enable ||
					(cache_clk_enable && (sigmap(port.clk) != cache_clk ||
					port.clk_polarity != cache_clk_polarity)))
			{
				cache_clk_enable = port.clk_enable;
				cache_clk_polarity = port.clk_polarity;
				cache_clk = sigmap(port.clk);
			}
			else if (i > 0 && considered_ports.count(i-1) && considered_ports.count(i))
				considered_port_pairs.insert(i);

			if (cache_clk_enable)
				log("  Port %d on %s %s: %s\n", i,
						cache_clk_polarity ? "posedge" : "negedge", log_signal(cache_clk),
						considered_ports.count(i) ? "considered" : "not considered");
			else
				log("  Port %d unclocked: %s\n", i,
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

		for (int i = 0; i < GetSize(mem.wr_ports); i++)
			if (considered_port_pairs.count(i) || considered_port_pairs.count(i+1))
			{
				RTLIL::SigSpec sig = modwalker.sigmap(mem.wr_ports[i].en);
				port_to_sat_variable[i] = ez->expression(ez->OpOr, satgen.importSigSpec(sig));

				std::vector<RTLIL::SigBit> bits = sig;
				bits_queue.insert(bits.begin(), bits.end());
			}

		while (!bits_queue.empty())
		{
			for (auto bit : bits_queue)
				if (bit.wire && bit.wire->get_bool_attribute(ID::onehot))
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

		bool changed = false;
		for (int i = 0; i < GetSize(mem.wr_ports); i++)
		{
			if (!considered_port_pairs.count(i))
				continue;

			if (ez->solve(port_to_sat_variable.at(i-1), port_to_sat_variable.at(i))) {
				log("  According to SAT solver sharing of port %d with port %d is not possible.\n", i-1, i);
				continue;
			}

			log("  Merging port %d into port %d.\n", i-1, i);
			port_to_sat_variable.at(i) = ez->OR(port_to_sat_variable.at(i-1), port_to_sat_variable.at(i));

			RTLIL::SigSpec last_addr = mem.wr_ports[i-1].addr;
			RTLIL::SigSpec last_data = mem.wr_ports[i-1].data;
			std::vector<RTLIL::SigBit> last_en = modwalker.sigmap(mem.wr_ports[i-1].en);

			RTLIL::SigSpec this_addr = mem.wr_ports[i].addr;
			RTLIL::SigSpec this_data = mem.wr_ports[i].data;
			std::vector<RTLIL::SigBit> this_en = modwalker.sigmap(mem.wr_ports[i].en);

			RTLIL::SigBit this_en_active = module->ReduceOr(NEW_ID, this_en);

			if (GetSize(last_addr) < GetSize(this_addr))
				last_addr.extend_u0(GetSize(this_addr));
			else
				this_addr.extend_u0(GetSize(last_addr));

			mem.wr_ports[i].addr = module->Mux(NEW_ID, last_addr, this_addr, this_en_active);
			mem.wr_ports[i].data = module->Mux(NEW_ID, last_data, this_data, this_en_active);

			std::map<std::pair<RTLIL::SigBit, RTLIL::SigBit>, int> groups_en;
			RTLIL::SigSpec grouped_last_en, grouped_this_en, en;
			RTLIL::Wire *grouped_en = module->addWire(NEW_ID, 0);

			for (int j = 0; j < int(this_en.size()); j++) {
				std::pair<RTLIL::SigBit, RTLIL::SigBit> key(last_en[j], this_en[j]);
				if (!groups_en.count(key)) {
					grouped_last_en.append(last_en[j]);
					grouped_this_en.append(this_en[j]);
					groups_en[key] = grouped_en->width;
					grouped_en->width++;
				}
				en.append(RTLIL::SigSpec(grouped_en, groups_en[key]));
			}

			module->addMux(NEW_ID, grouped_last_en, grouped_this_en, this_en_active, grouped_en);
			mem.wr_ports[i].en = en;

			mem.wr_ports[i-1].removed = true;
			changed = true;
		}

		if (changed)
			mem.emit();
	}


	// -------------
	// Setup and run
	// -------------

	MemoryShareWorker(RTLIL::Design *design) : design(design), modwalker(design) {}

	void operator()(RTLIL::Module* module)
	{
		std::vector<Mem> memories = Mem::get_selected_memories(module);

		this->module = module;
		sigmap.set(module);

		sigmap_xmux = sigmap;
		for (auto cell : module->cells())
		{
			if (cell->type == ID($mux))
			{
				RTLIL::SigSpec sig_a = sigmap_xmux(cell->getPort(ID::A));
				RTLIL::SigSpec sig_b = sigmap_xmux(cell->getPort(ID::B));

				if (sig_a.is_fully_undef())
					sigmap_xmux.add(cell->getPort(ID::Y), sig_b);
				else if (sig_b.is_fully_undef())
					sigmap_xmux.add(cell->getPort(ID::Y), sig_a);
			}
		}

		for (auto &mem : memories)
			consolidate_wr_by_addr(mem);

		cone_ct.setup_internals();
		cone_ct.cell_types.erase(ID($mul));
		cone_ct.cell_types.erase(ID($mod));
		cone_ct.cell_types.erase(ID($div));
		cone_ct.cell_types.erase(ID($modfloor));
		cone_ct.cell_types.erase(ID($divfloor));
		cone_ct.cell_types.erase(ID($pow));
		cone_ct.cell_types.erase(ID($shl));
		cone_ct.cell_types.erase(ID($shr));
		cone_ct.cell_types.erase(ID($sshl));
		cone_ct.cell_types.erase(ID($sshr));
		cone_ct.cell_types.erase(ID($shift));
		cone_ct.cell_types.erase(ID($shiftx));

		modwalker.setup(module, &cone_ct);

		for (auto &mem : memories)
			consolidate_wr_using_sat(mem);
	}
};

struct MemorySharePass : public Pass {
	MemorySharePass() : Pass("memory_share", "consolidate memory ports") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_share [selection]\n");
		log("\n");
		log("This pass merges share-able memory ports into single memory ports.\n");
		log("\n");
		log("The following methods are used to consolidate the number of memory ports:\n");
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing MEMORY_SHARE pass (consolidating $memrd/$memwr cells).\n");
		extra_args(args, 1, design);
		MemoryShareWorker msw(design);

		for (auto module : design->selected_modules())
			msw(module);
	}
} MemorySharePass;

PRIVATE_NAMESPACE_END
