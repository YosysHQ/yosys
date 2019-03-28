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
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EquivMiterWorker
{
	CellTypes ct;
	SigMap sigmap;

	bool mode_trigger;
	bool mode_cmp;
	bool mode_assert;
	bool mode_undef;

	IdString miter_name;
	Module *miter_module;
	Module *source_module;

	dict<SigBit, Cell*> bit_to_driver;
	pool<Cell*> seed_cells, miter_cells;
	pool<Wire*> miter_wires;

	void follow_cone(pool<Cell*> &cone, pool<Cell*> &leaves, Cell *c, bool gold_mode)
	{
		if (cone.count(c))
			return;

		if (c->type == "$equiv" && !seed_cells.count(c)) {
			leaves.insert(c);
			return;
		}

		cone.insert(c);

		for (auto &conn : c->connections()) {
			if (!ct.cell_input(c->type, conn.first))
				continue;
			if (c->type == "$equiv" && (conn.first == "\\A") != gold_mode)
				continue;
			for (auto bit : sigmap(conn.second))
				if (bit_to_driver.count(bit))
					follow_cone(cone, leaves, bit_to_driver.at(bit), gold_mode);
		}
	}

	void find_miter_cells_wires()
	{
		sigmap.set(source_module);

		// initialize bit_to_driver

		for (auto c : source_module->cells())
			for (auto &conn : c->connections())
				if (ct.cell_output(c->type, conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							bit_to_driver[bit] = c;

		// find seed cells

		for (auto c : source_module->selected_cells())
			if (c->type == "$equiv") {
				log("Seed $equiv cell: %s\n", log_id(c));
				seed_cells.insert(c);
			}

		// follow cone from seed cells to next $equiv

		while (1)
		{
			pool<Cell*> gold_cone, gold_leaves;
			pool<Cell*> gate_cone, gate_leaves;

			for (auto c : seed_cells) {
				follow_cone(gold_cone, gold_leaves, c, true);
				follow_cone(gate_cone, gate_leaves, c, false);
			}

			log("Gold cone: %d cells (%d leaves).\n", GetSize(gold_cone), GetSize(gold_leaves));
			log("Gate cone: %d cells (%d leaves).\n", GetSize(gate_cone), GetSize(gate_leaves));

			// done if all leaves are shared leaves

			if (gold_leaves == gate_leaves) {
				miter_cells = gold_cone;
				miter_cells.insert(gate_cone.begin(), gate_cone.end());
				log("Selected %d miter cells.\n", GetSize(miter_cells));
				break;
			}

			// remove shared leaves

			for (auto it = gold_leaves.begin(); it != gold_leaves.end(); ) {
				auto it2 = gate_leaves.find(*it);
				if (it2 != gate_leaves.end()) {
					it = gold_leaves.erase(it);
					gate_leaves.erase(it2);
				} else
					++it;
			}

			// add remaining leaves to seeds and re-run

			log("Adding %d gold and %d gate seed cells.\n", GetSize(gold_leaves), GetSize(gate_leaves));
			seed_cells.insert(gold_leaves.begin(), gold_leaves.end());
			seed_cells.insert(gate_leaves.begin(), gate_leaves.end());
		}

		for (auto c : miter_cells)
			for (auto &conn : c->connections())
				for (auto bit : sigmap(conn.second))
					if (bit.wire)
						miter_wires.insert(bit.wire);
		log("Selected %d miter wires.\n", GetSize(miter_wires));
	}

	void copy_to_miter()
	{
		// copy wires and cells

		for (auto w :  miter_wires)
			miter_module->addWire(w->name, w->width);
		for (auto c :  miter_cells) {
			miter_module->addCell(c->name, c);
			auto mc = miter_module->cell(c->name);
			for (auto &conn : mc->connections())
				mc->setPort(conn.first, sigmap(conn.second));
		}

		// fixup wire references in cells

		sigmap.clear();

		struct RewriteSigSpecWorker {
			RTLIL::Module * mod;
			void operator()(SigSpec &sig) {
				vector<SigChunk> chunks = sig.chunks();
				for (auto &c : chunks)
					if (c.wire != NULL)
						c.wire = mod->wires_.at(c.wire->name);
				sig = chunks;
			}
		};

		RewriteSigSpecWorker rewriteSigSpecWorker;
		rewriteSigSpecWorker.mod = miter_module;
		miter_module->rewrite_sigspecs(rewriteSigSpecWorker);

		// find undriven or unused wires

		pool<SigBit> driven_bits, used_bits;

		for (auto c : miter_module->cells())
		for (auto &conn : c->connections()) {
			if (ct.cell_input(c->type, conn.first))
				for (auto bit : conn.second)
					if (bit.wire)
						used_bits.insert(bit);
			if (ct.cell_output(c->type, conn.first))
				for (auto bit : conn.second)
					if (bit.wire)
						driven_bits.insert(bit);
		}

		// create ports

		for (auto w : miter_module->wires()) {
			for (auto bit : SigSpec(w)) {
				if (driven_bits.count(bit) && !used_bits.count(bit))
					w->port_output = true;
				if (!driven_bits.count(bit) && used_bits.count(bit))
					w->port_input = true;
			}
			if (w->port_output && w->port_input)
				log("Created miter inout port %s.\n", log_id(w));
			else if (w->port_output)
				log("Created miter output port %s.\n", log_id(w));
			else if (w->port_input)
				log("Created miter input port %s.\n", log_id(w));
		}

		miter_module->fixup_ports();
	}

	void make_stuff()
	{
		if (!mode_trigger && !mode_cmp && !mode_assert)
			return;

		SigSpec trigger_signals;
		vector<Cell*> equiv_cells;

		for (auto c : miter_module->cells())
			if (c->type == "$equiv" && c->getPort("\\A") != c->getPort("\\B"))
				equiv_cells.push_back(c);

		for (auto c : equiv_cells)
		{
			SigSpec cmp = mode_undef ?
					miter_module->LogicOr(NEW_ID, miter_module->Eqx(NEW_ID, c->getPort("\\A"), State::Sx),
							miter_module->Eqx(NEW_ID, c->getPort("\\A"), c->getPort("\\B"))) :
					miter_module->Eq(NEW_ID, c->getPort("\\A"), c->getPort("\\B"));

			if (mode_cmp) {
				string cmp_name = string("\\cmp") + log_signal(c->getPort("\\Y"));
				for (int i = 1; i < GetSize(cmp_name); i++)
					if (cmp_name[i] == '\\')
						cmp_name[i] = '_';
					else if (cmp_name[i] == ' ')
						cmp_name = cmp_name.substr(0, i) + cmp_name.substr(i+1);
				auto w = miter_module->addWire(cmp_name);
				w->port_output = true;
				miter_module->connect(w, cmp);
			}

			if (mode_assert)
				miter_module->addAssert(NEW_ID, cmp, State::S1);

			trigger_signals.append(miter_module->Not(NEW_ID, cmp));
		}

		if (mode_trigger) {
			auto w = miter_module->addWire("\\trigger");
			w->port_output = true;
			miter_module->addReduceOr(NEW_ID, trigger_signals, w);
		}

		miter_module->fixup_ports();
	}

	void run()
	{
		log("Creating miter %s from module %s.\n", log_id(miter_module), log_id(source_module));
		find_miter_cells_wires();
		copy_to_miter();
		make_stuff();
	}
};

struct EquivMiterPass : public Pass {
	EquivMiterPass() : Pass("equiv_miter", "extract miter from equiv circuit") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_miter [options] miter_module [selection]\n");
		log("\n");
		log("This creates a miter module for further analysis of the selected $equiv cells.\n");
		log("\n");
		log("    -trigger\n");
		log("        Create a trigger output\n");
		log("\n");
		log("    -cmp\n");
		log("        Create cmp_* outputs for individual unproven $equiv cells\n");
		log("\n");
		log("    -assert\n");
		log("        Create a $assert cell for each unproven $equiv cell\n");
		log("\n");
		log("    -undef\n");
		log("        Create compare logic that handles undefs correctly\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		EquivMiterWorker worker;
		worker.ct.setup(design);
		worker.mode_trigger = false;
		worker.mode_cmp = false;
		worker.mode_assert = false;
		worker.mode_undef = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-trigger") {
				worker.mode_trigger = true;
				continue;
			}
			if (args[argidx] == "-cmp") {
				worker.mode_cmp = true;
				continue;
			}
			if (args[argidx] == "-assert") {
				worker.mode_assert = true;
				continue;
			}
			if (args[argidx] == "-undef") {
				worker.mode_undef = true;
				continue;
			}
			break;
		}

		if (argidx >= args.size())
			log_cmd_error("Invalid number of arguments.\n");

		worker.miter_name = RTLIL::escape_id(args[argidx++]);
		extra_args(args, argidx, design);

		if (design->module(worker.miter_name))
			log_cmd_error("Miter module %s already exists.\n", log_id(worker.miter_name));

		worker.source_module = nullptr;
		for (auto m : design->selected_modules()) {
			if (worker.source_module != nullptr)
				goto found_two_modules;
			worker.source_module = m;
		}

		if (worker.source_module == nullptr)
	found_two_modules:
			log_cmd_error("Exactly one module must be selected for 'equiv_miter'!\n");

		log_header(design, "Executing EQUIV_MITER pass.\n");

		worker.miter_module = design->addModule(worker.miter_name);
		worker.run();
	}
} EquivMiterPass;

PRIVATE_NAMESPACE_END
