/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung <eddie@fpgeh.com>
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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ClkPartPass : public Pass {
	ClkPartPass() : Pass("clkpart", "partition design according to clock/enable domain") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clkpart [options] [selection]\n");
		log("\n");
		log("Partition the contents of selected modules according to the clock (and optionally\n");
		log("the enable) domains of its $_DFF* cells by extracting them into sub-modules,\n");
		log("using the `submod` command.\n");
		log("\n");
		log("    -set_attr <name> <value>\n");
		log("        set the specified attribute on all sub-modules created.\n");
		log("\n");
		log("    -unpart <name>\n");
		log("        undo this operation within the selected modules, by flattening those\n");
		log("        attached with an <name> attribute into those modules without this\n");
		log("        attribute.\n");
		log("\n");
		log("    -enable\n");
		log("        also consider enable domains.\n");
		log("\n");
	}

	bool unpart_mode, enable_mode;
	IdString attr_name;
	Const attr_value;

	void clear_flags() YS_OVERRIDE
	{
		unpart_mode = false;
		enable_mode = false;
		attr_name = IdString();
		attr_value = Const();
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing CLKPART pass (partition design according to clock/enable domain).\n");
		log_push();

		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-set_attr" && argidx+2 < args.size()) {
				attr_name = RTLIL::escape_id(args[argidx++]);
				attr_value = args[argidx++];
				continue;
			}
			if (args[argidx] == "-unpart" && argidx+1 < args.size()) {
				attr_name = RTLIL::escape_id(args[argidx++]);
				continue;
			}
			if (args[argidx] == "-enable") {
				enable_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (unpart_mode)
			unpart(design);
		else
			part(design);

		log_pop();
	}

	void part(RTLIL::Design *design)
	{
		CellTypes ct(design);
		SigMap assign_map;
		std::vector<std::string> new_submods;

		log_header(design, "Summary of detected clock domains:\n");
		for (auto mod : design->selected_modules())
		{
			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(mod));
				continue;
			}

			assign_map.set(mod);

			std::vector<RTLIL::Cell*> all_cells = mod->selected_cells();
			std::set<RTLIL::Cell*> unassigned_cells(all_cells.begin(), all_cells.end());

			std::set<RTLIL::Cell*> expand_queue, next_expand_queue;
			std::set<RTLIL::Cell*> expand_queue_up, next_expand_queue_up;
			std::set<RTLIL::Cell*> expand_queue_down, next_expand_queue_down;

			typedef tuple<bool, RTLIL::SigSpec, bool, RTLIL::SigSpec> clkdomain_t;
			std::map<clkdomain_t, vector<Cell*>> assigned_cells;
			std::map<RTLIL::Cell*, clkdomain_t> assigned_cells_reverse;

			std::map<RTLIL::Cell*, std::set<RTLIL::SigBit>> cell_to_bit, cell_to_bit_up, cell_to_bit_down;
			std::map<RTLIL::SigBit, std::set<RTLIL::Cell*>> bit_to_cell, bit_to_cell_up, bit_to_cell_down;

			for (auto cell : all_cells)
			{
				clkdomain_t key;

				for (auto &conn : cell->connections())
				for (auto bit : conn.second) {
					bit = assign_map(bit);
					if (bit.wire != nullptr) {
						cell_to_bit[cell].insert(bit);
						bit_to_cell[bit].insert(cell);
						if (ct.cell_input(cell->type, conn.first)) {
							cell_to_bit_up[cell].insert(bit);
							bit_to_cell_down[bit].insert(cell);
						}
						if (ct.cell_output(cell->type, conn.first)) {
							cell_to_bit_down[cell].insert(bit);
							bit_to_cell_up[bit].insert(cell);
						}
					}
				}

				if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_)))
				{
					key = clkdomain_t(cell->type == ID($_DFF_P_), assign_map(cell->getPort(ID(C))), true, RTLIL::SigSpec());
				}
				else
				if (cell->type.in(ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
				{
					bool this_clk_pol = cell->type.in(ID($_DFFE_PN_), ID($_DFFE_PP_));
					bool this_en_pol = !enable_mode || cell->type.in(ID($_DFFE_NP_), ID($_DFFE_PP_));
					key = clkdomain_t(this_clk_pol, assign_map(cell->getPort(ID(C))), this_en_pol, enable_mode ? assign_map(cell->getPort(ID(E))) : RTLIL::SigSpec());
				}
				else
					continue;

				unassigned_cells.erase(cell);
				expand_queue.insert(cell);
				expand_queue_up.insert(cell);
				expand_queue_down.insert(cell);

				assigned_cells[key].push_back(cell);
				assigned_cells_reverse[cell] = key;
			}

			while (!expand_queue_up.empty() || !expand_queue_down.empty())
			{
				if (!expand_queue_up.empty())
				{
					RTLIL::Cell *cell = *expand_queue_up.begin();
					clkdomain_t key = assigned_cells_reverse.at(cell);
					expand_queue_up.erase(cell);

					for (auto bit : cell_to_bit_up[cell])
					for (auto c : bit_to_cell_up[bit])
						if (unassigned_cells.count(c)) {
							unassigned_cells.erase(c);
							next_expand_queue_up.insert(c);
							assigned_cells[key].push_back(c);
							assigned_cells_reverse[c] = key;
							expand_queue.insert(c);
						}
				}

				if (!expand_queue_down.empty())
				{
					RTLIL::Cell *cell = *expand_queue_down.begin();
					clkdomain_t key = assigned_cells_reverse.at(cell);
					expand_queue_down.erase(cell);

					for (auto bit : cell_to_bit_down[cell])
					for (auto c : bit_to_cell_down[bit])
						if (unassigned_cells.count(c)) {
							unassigned_cells.erase(c);
							next_expand_queue_up.insert(c);
							assigned_cells[key].push_back(c);
							assigned_cells_reverse[c] = key;
							expand_queue.insert(c);
						}
				}

				if (expand_queue_up.empty() && expand_queue_down.empty()) {
					expand_queue_up.swap(next_expand_queue_up);
					expand_queue_down.swap(next_expand_queue_down);
				}
			}

			while (!expand_queue.empty())
			{
				RTLIL::Cell *cell = *expand_queue.begin();
				clkdomain_t key = assigned_cells_reverse.at(cell);
				expand_queue.erase(cell);

				for (auto bit : cell_to_bit.at(cell)) {
					for (auto c : bit_to_cell[bit])
						if (unassigned_cells.count(c)) {
							unassigned_cells.erase(c);
							next_expand_queue.insert(c);
							assigned_cells[key].push_back(c);
							assigned_cells_reverse[c] = key;
						}
					bit_to_cell[bit].clear();
				}

				if (expand_queue.empty())
					expand_queue.swap(next_expand_queue);
			}

			clkdomain_t key(true, RTLIL::SigSpec(), true, RTLIL::SigSpec());
			for (auto cell : unassigned_cells) {
				assigned_cells[key].push_back(cell);
				assigned_cells_reverse[cell] = key;
			}

			clkdomain_t largest_domain;
			int largest_domain_size = 0;
			log("  module %s\n", mod->name.c_str());
			for (auto &it : assigned_cells) {
				log("    %d cells in clk=%s%s, en=%s%s\n", GetSize(it.second),
						std::get<0>(it.first) ? "" : "!", log_signal(std::get<1>(it.first)),
						std::get<2>(it.first) ? "" : "!", log_signal(std::get<3>(it.first)));
				if (GetSize(it.second) > largest_domain_size) {
					largest_domain = it.first;
					largest_domain_size = GetSize(it.second);
				}
			}

			for (auto &it : assigned_cells) {
				if (it.first == largest_domain)
					continue;

				auto clk = std::get<1>(it.first);
				auto en = std::get<3>(it.first);
				std::string submod = stringf("clk=%s%s%s%s%s",
						std::get<0>(it.first) ? "" : "!", clk.empty() ? "" : log_signal(clk),
						std::get<2>(it.first) ? "" : "!", en.empty() ? ".en=" : "", en.empty() ? "" : log_signal(en));
				for (auto c : it.second)
					c->attributes[ID(submod)] = submod;
				new_submods.push_back(stringf("%s_%s", mod->name.c_str(), submod.c_str()));
			}
		}

		Pass::call(design, "submod");

		if (!attr_name.empty())
			for (auto m : new_submods)
				design->module(m)->attributes[attr_name] = attr_value;
	}

	void unpart(RTLIL::Design *design)
	{
		vector<Module*> keeped;
		for (auto mod : design->selected_modules()) {
			if (mod->get_bool_attribute(attr_name))
				continue;
			if (mod->get_bool_attribute(ID(keep_hierarchy)))
				continue;
			keeped.push_back(mod);
			mod->set_bool_attribute(ID(keep_hierarchy));
		}

		Pass::call(design, "flatten");

		for (auto mod : keeped)
			mod->set_bool_attribute(ID(keep_hierarchy), false);

	}
} ClkPartPass;

PRIVATE_NAMESPACE_END
