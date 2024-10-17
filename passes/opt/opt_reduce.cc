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

		RTLIL::SigSpec sig_a = assign_map(cell->getPort(ID::A));
		sig_a.sort_and_unify();
		pool<RTLIL::SigBit> new_sig_a_bits;

		for (auto &bit : sig_a)
		{
			if (bit == RTLIL::State::S0) {
				if (cell->type == ID($reduce_and)) {
					new_sig_a_bits.clear();
					new_sig_a_bits.insert(RTLIL::State::S0);
					break;
				}
				continue;
			}
			if (bit == RTLIL::State::S1) {
				if (cell->type == ID($reduce_or)) {
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
					if (child_cell->getPort(ID::Y)[0] == bit) {
						pool<RTLIL::SigBit> child_sig_a_bits = assign_map(child_cell->getPort(ID::A)).to_sigbit_pool();
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
		new_sig_a.sort_and_unify();

		if (GetSize(new_sig_a) == 0)
			new_sig_a = (cell->type == ID($reduce_or)) ? State::S0 : State::S1;

		if (new_sig_a != sig_a || sig_a.size() != cell->getPort(ID::A).size()) {
			log("    New input vector for %s cell %s: %s\n", cell->type.c_str(), cell->name.c_str(), log_signal(new_sig_a));
			did_something = true;
			total_count++;
		}

		cell->setPort(ID::A, new_sig_a);
		cell->parameters[ID::A_WIDTH] = RTLIL::Const(new_sig_a.size());
		return;
	}

	void opt_pmux(RTLIL::Cell *cell)
	{
		RTLIL::SigSpec sig_a = assign_map(cell->getPort(ID::A));
		RTLIL::SigSpec sig_b = assign_map(cell->getPort(ID::B));
		RTLIL::SigSpec sig_s = assign_map(cell->getPort(ID::S));

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
				RTLIL::Cell *reduce_or_cell = module->addCell(NEW_ID, ID($reduce_or));
				reduce_or_cell->setPort(ID::A, this_s);
				reduce_or_cell->parameters[ID::A_SIGNED] = RTLIL::Const(0);
				reduce_or_cell->parameters[ID::A_WIDTH] = RTLIL::Const(this_s.size());
				reduce_or_cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);

				RTLIL::Wire *reduce_or_wire = module->addWire(NEW_ID);
				this_s = RTLIL::SigSpec(reduce_or_wire);
				reduce_or_cell->setPort(ID::Y, this_s);
			}

			new_sig_b.append(this_b);
			new_sig_s.append(this_s);
			handled_sig.insert(this_b);
		}

		if (new_sig_s.size() == 0)
		{
			module->connect(cell->getPort(ID::Y), cell->getPort(ID::A));
			assign_map.add(cell->getPort(ID::Y), cell->getPort(ID::A));
			module->remove(cell);
			did_something = true;
			total_count++;
			return;
		}

		if (new_sig_s.size() != sig_s.size() || (new_sig_s.size() == 1 && cell->type == ID($pmux))) {
			log("    New ctrl vector for %s cell %s: %s\n", cell->type.c_str(), cell->name.c_str(), log_signal(new_sig_s));
			did_something = true;
			total_count++;
			cell->setPort(ID::B, new_sig_b);
			cell->setPort(ID::S, new_sig_s);
			if (new_sig_s.size() > 1) {
				cell->parameters[ID::S_WIDTH] = RTLIL::Const(new_sig_s.size());
			} else {
				cell->type = ID($mux);
				cell->parameters.erase(ID::S_WIDTH);
			}
		}
	}

	void opt_bmux(RTLIL::Cell *cell)
	{
		RTLIL::SigSpec sig_a = assign_map(cell->getPort(ID::A));
		RTLIL::SigSpec sig_s = assign_map(cell->getPort(ID::S));
		int width = cell->getParam(ID::WIDTH).as_int();

		RTLIL::SigSpec new_sig_a, new_sig_s;
		dict<RTLIL::SigBit, int> handled_bits;

		// 0 and up: index of new_sig_s bit
		// -1: const 0
		// -2: const 1
		std::vector<int> swizzle;

		for (int i = 0; i < sig_s.size(); i++)
		{
			SigBit bit = sig_s[i];
			if (bit == State::S0) {
				swizzle.push_back(-1);
			} else if (bit == State::S1) {
				swizzle.push_back(-2);
			} else {
				auto it = handled_bits.find(bit);
				if (it == handled_bits.end()) {
					int new_idx = GetSize(new_sig_s);
					new_sig_s.append(bit);
					handled_bits[bit] = new_idx;
					swizzle.push_back(new_idx);
				} else {
					swizzle.push_back(it->second);
				}
			}
		}

		for (int i = 0; i < (1 << GetSize(new_sig_s)); i++) {
			int idx = 0;
			for (int j = 0; j < GetSize(sig_s); j++) {
				if (swizzle[j] == -1) {
					// const 0.
				} else if (swizzle[j] == -2) {
					// const 1.
					idx |= 1 << j;
				} else {
					if (i & 1 << swizzle[j])
						idx |= 1 << j;
				}
			}
			new_sig_a.append(sig_a.extract(idx * width, width));
		}

		if (new_sig_s.size() == 0)
		{
			module->connect(cell->getPort(ID::Y), new_sig_a);
			assign_map.add(cell->getPort(ID::Y), new_sig_a);
			module->remove(cell);
			did_something = true;
			total_count++;
			return;
		}

		if (new_sig_s.size() == 1)
		{
			cell->type = ID($mux);
			cell->setPort(ID::A, new_sig_a.extract(0, width));
			cell->setPort(ID::B, new_sig_a.extract(width, width));
			cell->setPort(ID::S, new_sig_s);
			cell->parameters.erase(ID::S_WIDTH);
			did_something = true;
			total_count++;
			return;
		}

		if (new_sig_s.size() != sig_s.size()) {
			log("    New ctrl vector for %s cell %s: %s\n", cell->type.c_str(), cell->name.c_str(), log_signal(new_sig_s));
			did_something = true;
			total_count++;
			cell->setPort(ID::A, new_sig_a);
			cell->setPort(ID::S, new_sig_s);
			cell->parameters[ID::S_WIDTH] = RTLIL::Const(new_sig_s.size());
		}
	}

	void opt_demux(RTLIL::Cell *cell)
	{
		RTLIL::SigSpec sig_y = assign_map(cell->getPort(ID::Y));
		RTLIL::SigSpec sig_s = assign_map(cell->getPort(ID::S));
		int width = cell->getParam(ID::WIDTH).as_int();

		RTLIL::SigSpec new_sig_y, new_sig_s;
		dict<RTLIL::SigBit, int> handled_bits;

		// 0 and up: index of new_sig_s bit
		// -1: const 0
		// -2: const 1
		std::vector<int> swizzle;

		for (int i = 0; i < sig_s.size(); i++)
		{
			SigBit bit = sig_s[i];
			if (bit == State::S0) {
				swizzle.push_back(-1);
			} else if (bit == State::S1) {
				swizzle.push_back(-2);
			} else {
				auto it = handled_bits.find(bit);
				if (it == handled_bits.end()) {
					int new_idx = GetSize(new_sig_s);
					new_sig_s.append(bit);
					handled_bits[bit] = new_idx;
					swizzle.push_back(new_idx);
				} else {
					swizzle.push_back(it->second);
				}
			}
		}

		pool<int> nonzero_idx;

		for (int i = 0; i < (1 << GetSize(new_sig_s)); i++) {
			int idx = 0;
			for (int j = 0; j < GetSize(sig_s); j++) {
				if (swizzle[j] == -1) {
					// const 0.
				} else if (swizzle[j] == -2) {
					// const 1.
					idx |= 1 << j;
				} else {
					if (i & 1 << swizzle[j])
						idx |= 1 << j;
				}
			}
			log_assert(!nonzero_idx.count(idx));
			nonzero_idx.insert(idx);
			new_sig_y.append(sig_y.extract(idx * width, width));
		}

		if (new_sig_s.size() == sig_s.size() && sig_s.size() > 0)
			return;

		log("    New ctrl vector for %s cell %s: %s\n", cell->type.c_str(), cell->name.c_str(), log_signal(new_sig_s));
		did_something = true;
		total_count++;

		for (int i = 0; i < (1 << GetSize(sig_s)); i++) {
			if (!nonzero_idx.count(i)) {
				SigSpec slice = sig_y.extract(i * width, width);
				module->connect(slice, Const(State::S0, width));
				assign_map.add(slice, Const(State::S0, width));
			}
		}

		if (new_sig_s.size() == 0)
		{
			module->connect(new_sig_y, cell->getPort(ID::A));
			assign_map.add(new_sig_y, cell->getPort(ID::A));
			module->remove(cell);
		}
		else
		{
			cell->setPort(ID::S, new_sig_s);
			cell->setPort(ID::Y, new_sig_y);
			cell->parameters[ID::S_WIDTH] = RTLIL::Const(new_sig_s.size());
		}
	}

	bool opt_mux_bits(RTLIL::Cell *cell)
	{
		SigSpec sig_a = assign_map(cell->getPort(ID::A));
		SigSpec sig_b;
		SigSpec sig_y = assign_map(cell->getPort(ID::Y));
		int width = GetSize(sig_y);

		if (cell->type != ID($bmux))
			sig_b = assign_map(cell->getPort(ID::B));

		RTLIL::SigSig old_sig_conn;

		dict<SigSpec, SigBit> consolidated_in_tuples;
		std::vector<int> swizzle;

		for (int i = 0; i < width; i++)
		{
			SigSpec in_tuple;
			bool all_tuple_bits_same = true;

			in_tuple.append(sig_a[i]);
			for (int j = i; j < GetSize(sig_a); j += width) {
				in_tuple.append(sig_a[j]);
				if (sig_a[j] != in_tuple[0])
					all_tuple_bits_same = false;
			}
			for (int j = i; j < GetSize(sig_b); j += width) {
				in_tuple.append(sig_b[j]);
				if (sig_b[j] != in_tuple[0])
					all_tuple_bits_same = false;
			}

			if (all_tuple_bits_same)
			{
				old_sig_conn.first.append(sig_y[i]);
				old_sig_conn.second.append(sig_a[i]);
				continue;
			}

			auto it = consolidated_in_tuples.find(in_tuple);
			if (it == consolidated_in_tuples.end())
			{
				consolidated_in_tuples[in_tuple] = sig_y[i];
				swizzle.push_back(i);
			}
			else
			{
				old_sig_conn.first.append(sig_y[i]);
				old_sig_conn.second.append(it->second);
			}
		}

		if (GetSize(swizzle) != width)
		{
			log("    Consolidated identical input bits for %s cell %s:\n", cell->type.c_str(), cell->name.c_str());
			if (cell->type != ID($bmux)) {
				log("      Old ports: A=%s, B=%s, Y=%s\n", log_signal(cell->getPort(ID::A)),
						log_signal(cell->getPort(ID::B)), log_signal(cell->getPort(ID::Y)));
			} else {
				log("      Old ports: A=%s, Y=%s\n", log_signal(cell->getPort(ID::A)),
						log_signal(cell->getPort(ID::Y)));
			}

			if (swizzle.empty()) {
				module->remove(cell);
			} else {
				SigSpec new_sig_a;
				for (int i = 0; i < GetSize(sig_a); i += width)
					for (int j: swizzle)
						new_sig_a.append(sig_a[i+j]);
				cell->setPort(ID::A, new_sig_a);

				if (cell->type != ID($bmux)) {
					SigSpec new_sig_b;
					for (int i = 0; i < GetSize(sig_b); i += width)
						for (int j: swizzle)
							new_sig_b.append(sig_b[i+j]);
					cell->setPort(ID::B, new_sig_b);
				}

				SigSpec new_sig_y;
				for (int j: swizzle)
					new_sig_y.append(sig_y[j]);
				cell->setPort(ID::Y, new_sig_y);

				cell->parameters[ID::WIDTH] = RTLIL::Const(GetSize(swizzle));

				if (cell->type != ID($bmux)) {
					log("      New ports: A=%s, B=%s, Y=%s\n", log_signal(cell->getPort(ID::A)),
							log_signal(cell->getPort(ID::B)), log_signal(cell->getPort(ID::Y)));
				} else {
					log("      New ports: A=%s, Y=%s\n", log_signal(cell->getPort(ID::A)),
							log_signal(cell->getPort(ID::Y)));
				}
			}

			log("      New connections: %s = %s\n", log_signal(old_sig_conn.first), log_signal(old_sig_conn.second));
			module->connect(old_sig_conn);

			did_something = true;
			total_count++;
		}
		return swizzle.empty();
	}

	bool opt_demux_bits(RTLIL::Cell *cell) {
		SigSpec sig_a = assign_map(cell->getPort(ID::A));
		SigSpec sig_y = assign_map(cell->getPort(ID::Y));
		int width = GetSize(sig_a);

		RTLIL::SigSig old_sig_conn;

		dict<SigBit, int> handled_bits;
		std::vector<int> swizzle;

		for (int i = 0; i < width; i++)
		{
			if (sig_a[i] == State::S0)
			{
				for (int j = i; j < GetSize(sig_y); j += width)
				{
					old_sig_conn.first.append(sig_y[j]);
					old_sig_conn.second.append(State::S0);
				}
				continue;
			}

			auto it = handled_bits.find(sig_a[i]);
			if (it == handled_bits.end())
			{
				handled_bits[sig_a[i]] = i;
				swizzle.push_back(i);
			}
			else
			{
				for (int j = 0; j < GetSize(sig_y); j += width)
				{
					old_sig_conn.first.append(sig_y[i+j]);
					old_sig_conn.second.append(sig_y[it->second+j]);
				}
			}
		}

		if (GetSize(swizzle) != width)
		{
			log("    Consolidated identical input bits for %s cell %s:\n", cell->type.c_str(), cell->name.c_str());
			log("      Old ports: A=%s, Y=%s\n", log_signal(cell->getPort(ID::A)),
					log_signal(cell->getPort(ID::Y)));

			if (swizzle.empty()) {
				module->remove(cell);
			} else {
				SigSpec new_sig_a;
				for (int j: swizzle)
					new_sig_a.append(sig_a[j]);
				cell->setPort(ID::A, new_sig_a);

				SigSpec new_sig_y;
				for (int i = 0; i < GetSize(sig_y); i += width)
					for (int j: swizzle)
						new_sig_y.append(sig_y[i+j]);
				cell->setPort(ID::Y, new_sig_y);

				cell->parameters[ID::WIDTH] = RTLIL::Const(GetSize(swizzle));

				log("      New ports: A=%s, Y=%s\n", log_signal(cell->getPort(ID::A)),
						log_signal(cell->getPort(ID::Y)));
			}

			log("      New connections: %s = %s\n", log_signal(old_sig_conn.first), log_signal(old_sig_conn.second));
			module->connect(old_sig_conn);

			did_something = true;
			total_count++;
		}
		return swizzle.empty();
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
			if (cell->type.in(ID($mem), ID($mem_v2)))
				mem_wren_sigs.add(assign_map(cell->getPort(ID::WR_EN)));
			if (cell->type.in(ID($memwr), ID($memwr_v2)))
				mem_wren_sigs.add(assign_map(cell->getPort(ID::EN)));
		}
		for (auto &cell_it : module->cells_) {
			RTLIL::Cell *cell = cell_it.second;
			if (cell->type == ID($dff) && mem_wren_sigs.check_any(assign_map(cell->getPort(ID::Q))))
				mem_wren_sigs.add(assign_map(cell->getPort(ID::D)));
		}

		bool keep_expanding_mem_wren_sigs = true;
		while (keep_expanding_mem_wren_sigs) {
			keep_expanding_mem_wren_sigs = false;
			for (auto &cell_it : module->cells_) {
				RTLIL::Cell *cell = cell_it.second;
				if (cell->type == ID($mux) && mem_wren_sigs.check_any(assign_map(cell->getPort(ID::Y)))) {
					if (!mem_wren_sigs.check_all(assign_map(cell->getPort(ID::A))) ||
							!mem_wren_sigs.check_all(assign_map(cell->getPort(ID::B))))
						keep_expanding_mem_wren_sigs = true;
					mem_wren_sigs.add(assign_map(cell->getPort(ID::A)));
					mem_wren_sigs.add(assign_map(cell->getPort(ID::B)));
				}
			}
		}

		while (did_something)
		{
			did_something = false;

			// merge trees of reduce_* cells to one single cell and unify input vectors
			// (only handle reduce_and and reduce_or for various reasons)

			const IdString type_list[] = { ID($reduce_or), ID($reduce_and) };
			for (auto type : type_list)
			{
				SigSet<RTLIL::Cell*> drivers;
				pool<RTLIL::Cell*> cells;

				for (auto &cell_it : module->cells_) {
					RTLIL::Cell *cell = cell_it.second;
					if (cell->type != type || !design->selected(module, cell))
						continue;
					drivers.insert(assign_map(cell->getPort(ID::Y)), cell);
					cells.insert(cell);
				}

				while (cells.size() > 0) {
					RTLIL::Cell *cell = *cells.begin();
					opt_reduce(cells, drivers, cell);
				}
			}

			// merge identical inputs on $mux and $pmux cells

			for (auto cell : module->selected_cells())
			{
				if (!cell->type.in(ID($mux), ID($pmux), ID($bmux), ID($demux)))
					continue;

				// this optimization is to aggressive for most coarse-grain applications.
				// but we always want it for multiplexers driving write enable ports.
				if (do_fine || mem_wren_sigs.check_any(assign_map(cell->getPort(ID::Y)))) {
					if (cell->type == ID($demux)) {
						if (opt_demux_bits(cell))
							continue;
					} else {
						if (opt_mux_bits(cell))
							continue;
					}
				}

				if (cell->type.in(ID($mux), ID($pmux)))
					opt_pmux(cell);
				else if (cell->type == ID($bmux))
					opt_bmux(cell);
				else if (cell->type == ID($demux))
					opt_demux(cell);
			}
		}

		module->check();
	}
};

struct OptReducePass : public Pass {
	OptReducePass() : Pass("opt_reduce", "simplify large MUXes and AND/OR gates") { }
	void help() override
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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
