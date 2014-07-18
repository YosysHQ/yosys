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
#include "kernel/sigtools.h"
#include "kernel/register.h"
#include "kernel/log.h"
#include <algorithm>

static bool memcells_cmp(RTLIL::Cell *a, RTLIL::Cell *b)
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
	SigMap sigmap;

	RTLIL::SigSpec mask_en_naive(RTLIL::SigSpec do_mask, RTLIL::SigSpec bits, RTLIL::SigSpec mask_bits)
	{
		// this is the naive version of the function that does not care about grouping the EN bits.

		RTLIL::SigSpec inv_mask_bits = module->Not(NEW_ID, mask_bits);
		RTLIL::SigSpec inv_mask_bits_filtered = module->Mux(NEW_ID, RTLIL::SigSpec(RTLIL::State::S1, bits.width), inv_mask_bits, do_mask);
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

		for (int i = 0; i < bits.width; i++) {
			std::pair<RTLIL::SigBit, RTLIL::SigBit> key(v_bits[i], v_mask_bits[i]);
			if (groups.count(key) == 0) {
				groups[key].first = grouped_bits.width;
				grouped_bits.append_bit(v_bits[i]);
				grouped_mask_bits.append_bit(v_mask_bits[i]);
			}
			groups[key].second.push_back(i);
		}

		std::vector<RTLIL::SigBit> grouped_result = mask_en_naive(do_mask, grouped_bits, grouped_mask_bits);
		RTLIL::SigSpec result;

		for (int i = 0; i < bits.width; i++) {
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

		RTLIL::SigSpec new_merged_data(RTLIL::State::Sx, merged_data.width);

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
		log("Consolidating write ports of memory %s by address:\n", log_id(memid));

		std::map<RTLIL::SigSpec, int> last_port_by_addr;
		std::vector<std::vector<bool>> active_bits_on_port;

		bool cache_clk_enable = false;
		bool cache_clk_polarity = false;
		RTLIL::SigSpec cache_clk;

		for (int i = 0; i < int(wr_ports.size()); i++)
		{
			RTLIL::Cell *cell = wr_ports.at(i);
			RTLIL::SigSpec addr = sigmap(cell->connections.at("\\ADDR"));

			if (cell->parameters.at("\\CLK_ENABLE").as_bool() != cache_clk_enable ||
					(cache_clk_enable && (sigmap(cell->connections.at("\\CLK")) != cache_clk ||
					cell->parameters.at("\\CLK_POLARITY").as_bool() != cache_clk_polarity)))
			{
				cache_clk_enable = cell->parameters.at("\\CLK_ENABLE").as_bool();
				cache_clk_polarity = cell->parameters.at("\\CLK_POLARITY").as_bool();
				cache_clk = sigmap(cell->connections.at("\\CLK"));
				last_port_by_addr.clear();

				if (cache_clk_enable)
					log("  New clock domain: %s %s\n", cache_clk_polarity ? "posedge" : "negedge", log_signal(cache_clk));
				else
					log("  New clock domain: unclocked\n");
			}

			log("    Port %d (%s) has addr %s.\n", i, log_id(cell), log_signal(addr));

			log("      Active bits: ");
			std::vector<RTLIL::SigBit> en_bits = sigmap(cell->connections.at("\\EN"));
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

				cell->connections.at("\\ADDR") = addr;

				// If any of the ports between `last_i' and `i' write to the same address, this
				// will have priority over whatever `last_i` wrote. So we need to revisit those
				// ports and mask the EN bits accordingly.

				RTLIL::SigSpec merged_en = sigmap(wr_ports[last_i]->connections.at("\\EN"));

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
						RTLIL::SigSpec is_same_addr = module->new_wire(1, NEW_ID);
						module->addEq(NEW_ID, addr, wr_ports[j]->connections.at("\\ADDR"), is_same_addr);
						merged_en = mask_en_grouped(is_same_addr, merged_en, sigmap(wr_ports[j]->connections.at("\\EN")));
					}
				}

				// Then we need to merge the (masked) EN and the DATA signals.
				// Note that we intentionally do not use sigmap() on the DATA ports.

				RTLIL::SigSpec merged_data = wr_ports[last_i]->connections.at("\\DATA");
				if (found_overlapping_bits) {
					log("      Creating logic for merging DATA and EN ports.\n");
					merge_en_data(merged_en, merged_data, sigmap(cell->connections.at("\\EN")), cell->connections.at("\\DATA"));
				} else {
					for (int k = 0; k < int(en_bits.size()); k++)
						if (!active_bits_on_port[last_i][k]) {
							merged_en.replace(k, cell->connections.at("\\EN").extract(k, 1));
							merged_data.replace(k, cell->connections.at("\\DATA").extract(k, 1));
						}
					merged_en.optimize();
					merged_data.optimize();
				}

				// Connect the new EN and DATA signals and remove the old write port.

				cell->connections.at("\\EN") = merged_en;
				cell->connections.at("\\DATA") = merged_data;

				module->cells.erase(wr_ports[last_i]->name);
				delete wr_ports[last_i];
				wr_ports[last_i] = NULL;

				log("      Active bits: ");
				std::vector<RTLIL::SigBit> en_bits = sigmap(cell->connections.at("\\EN"));
				active_bits_on_port.push_back(std::vector<bool>(en_bits.size()));
				for (int k = int(en_bits.size())-1; k >= 0; k--)
					log("%c", active_bits_on_port[i][k] ? '1' : '0');
				log("\n");
			}

			last_port_by_addr[addr] = i;
		}
	}

	MemoryShareWorker(RTLIL::Design *design, RTLIL::Module *module) :
			design(design), module(module), sigmap(module)
	{
		std::map<std::string, std::pair<std::vector<RTLIL::Cell*>, std::vector<RTLIL::Cell*>>> memindex;

		for (auto &it : module->cells)
		{
			RTLIL::Cell *cell = it.second;

			if (cell->type == "$memrd")
				memindex[cell->parameters.at("\\MEMID").decode_string()].first.push_back(cell);

			if (cell->type == "$memwr")
				memindex[cell->parameters.at("\\MEMID").decode_string()].second.push_back(cell);

			if (cell->type == "$mux")
			{
				RTLIL::SigSpec sig_a = sigmap(cell->connections.at("\\A"));
				RTLIL::SigSpec sig_b = sigmap(cell->connections.at("\\B"));

				if (sig_a.is_fully_undef())
					sigmap.add(cell->connections.at("\\Y"), sig_b);
				else if (sig_b.is_fully_undef())
					sigmap.add(cell->connections.at("\\Y"), sig_a);
			}
		}

		for (auto &it : memindex) {
			std::sort(it.second.first.begin(), it.second.first.end(), memcells_cmp);
			std::sort(it.second.second.begin(), it.second.second.end(), memcells_cmp);
			consolidate_wr_by_addr(it.first, it.second.second);
		}
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
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		log_header("Executing MEMORY_SHARE pass (consolidating $memrc/$memwr cells).\n");
		extra_args(args, 1, design);
		for (auto &mod_it : design->modules)
			if (design->selected(mod_it.second))
				MemoryShareWorker(design, mod_it.second);
	}
} MemorySharePass;

