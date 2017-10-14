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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptReduceWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap assign_map;

	int total_count;
	bool did_something;

	void opt_reduce(pool<RTLIL::Cell*> &cells, SigSet<RTLIL::Cell*> &drivers, RTLIL::Cell *cell)
	{
		if (cells.count(cell) == 0)
			return;
		cells.erase(cell);

		RTLIL::SigSpec sig_a = assign_map(cell->getPort("\\A"));
		pool<RTLIL::SigBit> new_sig_a_bits;

		for (auto &bit : sig_a.to_sigbit_set())
		{
			if (bit == RTLIL::State::S0) {
				if (cell->type == "$reduce_and") {
					new_sig_a_bits.clear();
					new_sig_a_bits.insert(RTLIL::State::S0);
					break;
				}
				continue;
			}
			if (bit == RTLIL::State::S1) {
				if (cell->type == "$reduce_or") {
					new_sig_a_bits.clear();
					new_sig_a_bits.insert(RTLIL::State::S1);
					break;
				}
				continue;
			}
			if (bit.wire == NULL) {
				new_sig_a_bits.insert(bit);
				continue;
			}

			bool imported_children = false;
			for (auto child_cell : drivers.find(bit)) {
				if (child_cell->type == cell->type) {
					opt_reduce(cells, drivers, child_cell);
					if (child_cell->getPort("\\Y")[0] == bit) {
						pool<RTLIL::SigBit> child_sig_a_bits = assign_map(child_cell->getPort("\\A")).to_sigbit_pool();
						new_sig_a_bits.insert(child_sig_a_bits.begin(), child_sig_a_bits.end());
					} else
						new_sig_a_bits.insert(RTLIL::State::S0);
					imported_children = true;
				}
			}
			if (!imported_children)
				new_sig_a_bits.insert(bit);
		}

		RTLIL::SigSpec new_sig_a(new_sig_a_bits);

		if (new_sig_a != sig_a || sig_a.size() != cell->getPort("\\A").size()) {
			log("    New input vector for %s cell %s: %s\n", cell->type.c_str(), cell->name.c_str(), log_signal(new_sig_a));
			did_something = true;
			total_count++;
		}

		cell->setPort("\\A", new_sig_a);
		cell->parameters["\\A_WIDTH"] = RTLIL::Const(new_sig_a.size());
		return;
	}

	void opt_mux(RTLIL::Cell *cell)
	{
		RTLIL::SigSpec sig_a = assign_map(cell->getPort("\\A"));
		RTLIL::SigSpec sig_b = assign_map(cell->getPort("\\B"));
		RTLIL::SigSpec sig_s = assign_map(cell->getPort("\\S"));

		RTLIL::SigSpec new_sig_b, new_sig_s;
		pool<RTLIL::SigSpec> handled_sig;

		handled_sig.insert(sig_a);
		for (int i = 0; i < sig_s.size(); i++)
		{
			RTLIL::SigSpec this_b = sig_b.extract(i*sig_a.size(), sig_a.size());
			if (handled_sig.count(this_b) > 0)
				continue;

			RTLIL::SigSpec this_s = sig_s.extract(i, 1);
			for (int j = i+1; j < sig_s.size(); j++) {
				RTLIL::SigSpec that_b = sig_b.extract(j*sig_a.size(), sig_a.size());
				if (this_b == that_b)
					this_s.append(sig_s.extract(j, 1));
			}

			if (this_s.size() > 1)
			{
				RTLIL::Cell *reduce_or_cell = module->addCell(NEW_ID, "$reduce_or");
				reduce_or_cell->setPort("\\A", this_s);
				reduce_or_cell->parameters["\\A_SIGNED"] = RTLIL::Const(0);
				reduce_or_cell->parameters["\\A_WIDTH"] = RTLIL::Const(this_s.size());
				reduce_or_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);

				RTLIL::Wire *reduce_or_wire = module->addWire(NEW_ID);
				this_s = RTLIL::SigSpec(reduce_or_wire);
				reduce_or_cell->setPort("\\Y", this_s);
			}

			new_sig_b.append(this_b);
			new_sig_s.append(this_s);
			handled_sig.insert(this_b);
		}

		if (new_sig_s.size() != sig_s.size()) {
			log("    New ctrl vector for %s cell %s: %s\n", cell->type.c_str(), cell->name.c_str(), log_signal(new_sig_s));
			did_something = true;
			total_count++;
		}

		if (new_sig_s.size() == 0)
		{
			module->connect(RTLIL::SigSig(cell->getPort("\\Y"), cell->getPort("\\A")));
			assign_map.add(cell->getPort("\\Y"), cell->getPort("\\A"));
			module->remove(cell);
		}
		else
		{
			cell->setPort("\\B", new_sig_b);
			cell->setPort("\\S", new_sig_s);
			if (new_sig_s.size() > 1) {
				cell->parameters["\\S_WIDTH"] = RTLIL::Const(new_sig_s.size());
			} else {
				cell->type = "$mux";
				cell->parameters.erase("\\S_WIDTH");
			}
		}
	}

	void opt_mux_bits(RTLIL::Cell *cell)
	{
		std::vector<RTLIL::SigBit> sig_a = assign_map(cell->getPort("\\A")).to_sigbit_vector();
		std::vector<RTLIL::SigBit> sig_b = assign_map(cell->getPort("\\B")).to_sigbit_vector();
		std::vector<RTLIL::SigBit> sig_y = assign_map(cell->getPort("\\Y")).to_sigbit_vector();

		std::vector<RTLIL::SigBit> new_sig_y;
		RTLIL::SigSig old_sig_conn;

		std::vector<std::vector<RTLIL::SigBit>> consolidated_in_tuples;
		std::map<std::vector<RTLIL::SigBit>, RTLIL::SigBit> consolidated_in_tuples_map;

		for (int i = 0; i < int(sig_y.size()); i++)
		{
			std::vector<RTLIL::SigBit> in_tuple;
			bool all_tuple_bits_same = true;

			in_tuple.push_back(sig_a.at(i));
			for (int j = i; j < int(sig_b.size()); j += int(sig_a.size())) {
				if (sig_b.at(j) != sig_a.at(i))
					all_tuple_bits_same = false;
				in_tuple.push_back(sig_b.at(j));
			}

			if (all_tuple_bits_same)
			{
				old_sig_conn.first.append_bit(sig_y.at(i));
				old_sig_conn.second.append_bit(sig_a.at(i));
			}
			else if (consolidated_in_tuples_map.count(in_tuple))
			{
				old_sig_conn.first.append_bit(sig_y.at(i));
				old_sig_conn.second.append_bit(consolidated_in_tuples_map.at(in_tuple));
			}
			else
			{
				consolidated_in_tuples_map[in_tuple] = sig_y.at(i);
				consolidated_in_tuples.push_back(in_tuple);
				new_sig_y.push_back(sig_y.at(i));
			}
		}

		if (new_sig_y.size() != sig_y.size())
		{
			log("    Consolidated identical input bits for %s cell %s:\n", cell->type.c_str(), cell->name.c_str());
			log("      Old ports: A=%s, B=%s, Y=%s\n", log_signal(cell->getPort("\\A")),
					log_signal(cell->getPort("\\B")), log_signal(cell->getPort("\\Y")));

			cell->setPort("\\A", RTLIL::SigSpec());
			for (auto &in_tuple : consolidated_in_tuples) {
				RTLIL::SigSpec new_a = cell->getPort("\\A");
				new_a.append(in_tuple.at(0));
				cell->setPort("\\A", new_a);
			}

			cell->setPort("\\B", RTLIL::SigSpec());
			for (int i = 1; i <= cell->getPort("\\S").size(); i++)
				for (auto &in_tuple : consolidated_in_tuples) {
					RTLIL::SigSpec new_b = cell->getPort("\\B");
					new_b.append(in_tuple.at(i));
					cell->setPort("\\B", new_b);
				}

			cell->parameters["\\WIDTH"] = RTLIL::Const(new_sig_y.size());
			cell->setPort("\\Y", new_sig_y);

			log("      New ports: A=%s, B=%s, Y=%s\n", log_signal(cell->getPort("\\A")),
					log_signal(cell->getPort("\\B")), log_signal(cell->getPort("\\Y")));
			log("      New connections: %s = %s\n", log_signal(old_sig_conn.first), log_signal(old_sig_conn.second));

			module->connect(old_sig_conn);
			module->check();

			did_something = true;
			total_count++;
		}
	}

	OptReduceWorker(RTLIL::Design *design, RTLIL::Module *module, bool do_fine) :
			design(design), module(module), assign_map(module)
	{
		log("  Optimizing cells in module %s.\n", module->name.c_str());

		total_count = 0;
		did_something = true;

		SigPool mem_wren_sigs;
		for (auto &cell_it : module->cells_) {
			RTLIL::Cell *cell = cell_it.second;
			if (cell->type == "$mem")
				mem_wren_sigs.add(assign_map(cell->getPort("\\WR_EN")));
			if (cell->type == "$memwr")
				mem_wren_sigs.add(assign_map(cell->getPort("\\EN")));
		}
		for (auto &cell_it : module->cells_) {
			RTLIL::Cell *cell = cell_it.second;
			if (cell->type == "$dff" && mem_wren_sigs.check_any(assign_map(cell->getPort("\\Q"))))
				mem_wren_sigs.add(assign_map(cell->getPort("\\D")));
		}

		bool keep_expanding_mem_wren_sigs = true;
		while (keep_expanding_mem_wren_sigs) {
			keep_expanding_mem_wren_sigs = false;
			for (auto &cell_it : module->cells_) {
				RTLIL::Cell *cell = cell_it.second;
				if (cell->type == "$mux" && mem_wren_sigs.check_any(assign_map(cell->getPort("\\Y")))) {
					if (!mem_wren_sigs.check_all(assign_map(cell->getPort("\\A"))) ||
							!mem_wren_sigs.check_all(assign_map(cell->getPort("\\B"))))
						keep_expanding_mem_wren_sigs = true;
					mem_wren_sigs.add(assign_map(cell->getPort("\\A")));
					mem_wren_sigs.add(assign_map(cell->getPort("\\B")));
				}
			}
		}

		while (did_something)
		{
			did_something = false;

			// merge trees of reduce_* cells to one single cell and unify input vectors
			// (only handle reduce_and and reduce_or for various reasons)

			const char *type_list[] = { "$reduce_or", "$reduce_and" };
			for (auto type : type_list)
			{
				SigSet<RTLIL::Cell*> drivers;
				pool<RTLIL::Cell*> cells;

				for (auto &cell_it : module->cells_) {
					RTLIL::Cell *cell = cell_it.second;
					if (cell->type != type || !design->selected(module, cell))
						continue;
					drivers.insert(assign_map(cell->getPort("\\Y")), cell);
					cells.insert(cell);
				}

				while (cells.size() > 0) {
					RTLIL::Cell *cell = *cells.begin();
					opt_reduce(cells, drivers, cell);
				}
			}

			// merge identical inputs on $mux and $pmux cells

			std::vector<RTLIL::Cell*> cells;

			for (auto &it : module->cells_)
				if ((it.second->type == "$mux" || it.second->type == "$pmux") && design->selected(module, it.second))
					cells.push_back(it.second);

			for (auto cell : cells)
			{
				// this optimization is to aggressive for most coarse-grain applications.
				// but we always want it for multiplexers driving write enable ports.
				if (do_fine || mem_wren_sigs.check_any(assign_map(cell->getPort("\\Y"))))
					opt_mux_bits(cell);

				opt_mux(cell);
			}
		}
	}
};

struct OptReducePass : public Pass {
	OptReducePass() : Pass("opt_reduce", "simplify large MUXes and AND/OR gates") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_reduce [options] [selection]\n");
		log("\n");
		log("This pass performs two interlinked optimizations:\n");
		log("\n");
		log("1. it consolidates trees of large AND gates or OR gates and eliminates\n");
		log("duplicated inputs.\n");
		log("\n");
		log("2. it identifies duplicated inputs to MUXes and replaces them with a single\n");
		log("input with the original control signals OR'ed together.\n");
		log("\n");
		log("    -fine\n");
		log("      perform fine-grain optimizations\n");
		log("\n");
		log("    -full\n");
		log("      alias for -fine\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool do_fine = false;

		log_header(design, "Executing OPT_REDUCE pass (consolidate $*mux and $reduce_* inputs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-fine") {
				do_fine = true;
				continue;
			}
			if (args[argidx] == "-full") {
				do_fine = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules())
			while (1) {
				OptReduceWorker worker(design, module, do_fine);
				total_count += worker.total_count;
				if (worker.total_count == 0)
					break;
			}

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Performed a total of %d changes.\n", total_count);
	}
} OptReducePass;

PRIVATE_NAMESPACE_END
