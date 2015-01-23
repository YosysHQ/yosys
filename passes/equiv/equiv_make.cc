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

struct EquivMakeWorker
{
	Module *gold_mod, *gate_mod, *equiv_mod;
	pool<IdString> wire_names, cell_names;
	CellTypes ct;
	bool inames;

	void copy_to_equiv()
	{
		Module *gold_clone = gold_mod->clone();
		Module *gate_clone = gate_mod->clone();

		for (auto it : gold_clone->wires().to_vector()) { if (it->name[0] == '\\' || inames) wire_names.insert(it->name); gold_clone->rename(it, it->name.str() + "_gold"); }
		for (auto it : gold_clone->cells().to_vector()) { if (it->name[0] == '\\' || inames) cell_names.insert(it->name); gold_clone->rename(it, it->name.str() + "_gold"); }
		for (auto it : gate_clone->wires().to_vector()) { if (it->name[0] == '\\' || inames) wire_names.insert(it->name); gate_clone->rename(it, it->name.str() + "_gate"); }
		for (auto it : gate_clone->cells().to_vector()) { if (it->name[0] == '\\' || inames) cell_names.insert(it->name); gate_clone->rename(it, it->name.str() + "_gate"); }

		gold_clone->cloneInto(equiv_mod);
		gate_clone->cloneInto(equiv_mod);
		delete gold_clone;
		delete gate_clone;
	}

	void find_same_wires()
	{
		SigMap assign_map(equiv_mod);
		SigMap rd_signal_map;

		// list of cells without added $equiv cells
		auto cells_list = equiv_mod->cells().to_vector();

		for (auto id : wire_names)
		{
			IdString gold_id = id.str() + "_gold";
			IdString gate_id = id.str() + "_gate";

			Wire *gold_wire = equiv_mod->wire(gold_id);
			Wire *gate_wire = equiv_mod->wire(gate_id);

			if (gold_wire == nullptr || gate_wire == nullptr || gold_wire->width != gate_wire->width) {
				if (gold_wire && gold_wire->port_id)
					log_error("Can't match gold port `%s' to a gate port.\n", log_id(gold_wire));
				if (gate_wire && gate_wire->port_id)
					log_error("Can't match gate port `%s' to a gold port.\n", log_id(gate_wire));
				continue;
			}

			log("Presumably equivalent wires: %s (%s), %s (%s) -> %s\n",
					log_id(gold_wire), log_signal(assign_map(gold_wire)),
					log_id(gate_wire), log_signal(assign_map(gate_wire)), log_id(id));

			if (gold_wire->port_output || gate_wire->port_output)
			{
				Wire *wire = equiv_mod->addWire(id, gold_wire->width);
				wire->port_output = true;
				gold_wire->port_input = false;
				gate_wire->port_input = false;
				gold_wire->port_output = false;
				gate_wire->port_output = false;

				for (int i = 0; i < wire->width; i++)
					equiv_mod->addEquiv(NEW_ID, SigSpec(gold_wire, i), SigSpec(gate_wire, i), SigSpec(wire, i));

				rd_signal_map.add(assign_map(gold_wire), wire);
				rd_signal_map.add(assign_map(gate_wire), wire);
			}
			else
			if (gold_wire->port_input || gate_wire->port_input)
			{
				Wire *wire = equiv_mod->addWire(id, gold_wire->width);
				wire->port_input = true;
				gold_wire->port_input = false;
				gate_wire->port_input = false;
				equiv_mod->connect(gold_wire, wire);
				equiv_mod->connect(gate_wire, wire);
			}
			else
			{
				Wire *wire = equiv_mod->addWire(id, gold_wire->width);

				for (int i = 0; i < wire->width; i++)
					equiv_mod->addEquiv(NEW_ID, SigSpec(gold_wire, i), SigSpec(gate_wire, i), SigSpec(wire, i));

				rd_signal_map.add(assign_map(gold_wire), wire);
				rd_signal_map.add(assign_map(gate_wire), wire);
			}
		}

		for (auto c : cells_list)
		for (auto &conn : c->connections())
			if (ct.cell_input(c->type, conn.first)) {
				SigSpec old_sig = assign_map(conn.second);
				SigSpec new_sig = rd_signal_map(old_sig);
				if (old_sig != new_sig) {
					log("Changing input %s of cell %s (%s): %s -> %s\n",
							log_id(conn.first), log_id(c), log_id(c->type),
							log_signal(old_sig), log_signal(new_sig));
					c->setPort(conn.first, new_sig);
				}
			}

		equiv_mod->fixup_ports();
	}

	void find_same_cells()
	{
		SigMap assign_map(equiv_mod);

		for (auto id : cell_names)
		{
			IdString gold_id = id.str() + "_gold";
			IdString gate_id = id.str() + "_gate";

			Cell *gold_cell = equiv_mod->cell(gold_id);
			Cell *gate_cell = equiv_mod->cell(gate_id);

			if (gold_cell == nullptr || gate_cell == nullptr || gold_cell->type != gate_cell->type || !ct.cell_known(gold_cell->type) ||
					gold_cell->parameters != gate_cell->parameters || GetSize(gold_cell->connections()) != GetSize(gate_cell->connections()))
		try_next_cell_name:
				continue;

			for (auto gold_conn : gold_cell->connections())
				if (!gate_cell->connections().count(gold_conn.first))
					goto try_next_cell_name;

			log("Presumably equivalent cells: %s %s (%s) -> %s\n",
					log_id(gold_cell), log_id(gate_cell), log_id(gold_cell->type), log_id(id));

			for (auto gold_conn : gold_cell->connections())
			{
				SigSpec gold_sig = assign_map(gold_conn.second);
				SigSpec gate_sig = assign_map(gate_cell->getPort(gold_conn.first));

				if (ct.cell_output(gold_cell->type, gold_conn.first)) {
					equiv_mod->connect(gate_sig, gold_sig);
					continue;
				}

				for (int i = 0; i < GetSize(gold_sig); i++)
					if (gold_sig[i] != gate_sig[i]) {
						Wire *w = equiv_mod->addWire(NEW_ID);
						equiv_mod->addEquiv(NEW_ID, gold_sig[i], gate_sig[i], w);
						gold_sig[i] = w;
					}

				gold_cell->setPort(gold_conn.first, gold_sig);
			}

			equiv_mod->remove(gate_cell);
			equiv_mod->rename(gold_cell, id);
		}
	}

	void find_undriven_nets()
	{
		pool<SigBit> undriven_bits;
		SigMap assign_map(equiv_mod);

		for (auto wire : equiv_mod->wires()) {
			for (auto bit : assign_map(wire))
				if (bit.wire)
					undriven_bits.insert(bit);
		}

		for (auto wire : equiv_mod->wires()) {
			if (wire->port_input)
				for (auto bit : assign_map(wire))
					undriven_bits.erase(bit);
		}

		for (auto cell : equiv_mod->cells()) {
			for (auto &conn : cell->connections())
				if (!ct.cell_known(cell->type) || ct.cell_output(cell->type, conn.first))
					for (auto bit : assign_map(conn.second))
						undriven_bits.erase(bit);
		}

		SigSpec undriven_sig(undriven_bits);
		undriven_sig.sort_and_unify();

		for (auto chunk : undriven_sig.chunks()) {
			log("Setting undriven nets to undef: %s\n", log_signal(chunk));
			equiv_mod->connect(chunk, SigSpec(State::Sx, chunk.width));
		}
	}

	void run()
	{
		copy_to_equiv();
		find_same_wires();
		find_same_cells();
		find_undriven_nets();
	}
};

struct EquivMakePass : public Pass {
	EquivMakePass() : Pass("equiv_make", "prepare a circuit for equivalence checking") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_make [options] gold_module gate_module equiv_module\n");
		log("\n");
		log("This creates a module annotated with $equiv cells from two presumably\n");
		log("equivalent modules. Use commands such as 'equiv_simple' and 'equiv_status'\n");
		log("to work with the created equivalent checking module.\n");
		log("\n");
		log("    -inames\n");
		log("        Also match cells and wires with $... names.\n");
		log("\n");
		log("Note: The circuit created by this command is not a miter (with something like\n");
		log("a trigger output), but instead uses $equiv cells to encode the equivalence\n");
		log("checking problem. Use 'miter -equiv' if you want to create a miter circuit.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		EquivMakeWorker worker;
		worker.ct.setup(design);
		worker.inames = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-inames") {
				worker.inames = true;
				continue;
			}
			break;
		}

		if (argidx+3 != args.size())
			log_cmd_error("Invalid number of arguments.\n");

		worker.gold_mod = design->module(RTLIL::escape_id(args[argidx]));
		worker.gate_mod = design->module(RTLIL::escape_id(args[argidx+1]));
		worker.equiv_mod = design->module(RTLIL::escape_id(args[argidx+2]));

		if (worker.gold_mod == nullptr)
			log_cmd_error("Can't find gold module %s.\n", args[argidx].c_str());

		if (worker.gate_mod == nullptr)
			log_cmd_error("Can't find gate module %s.\n", args[argidx+1].c_str());

		if (worker.equiv_mod != nullptr)
			log_cmd_error("Equiv module %s already exists.\n", args[argidx+2].c_str());

		if (worker.gold_mod->has_memories() || worker.gold_mod->has_processes())
			log_cmd_error("Gold module contains memories or procresses. Run 'memory' or 'proc' respectively.\n");

		if (worker.gate_mod->has_memories() || worker.gate_mod->has_processes())
			log_cmd_error("Gate module contains memories or procresses. Run 'memory' or 'proc' respectively.\n");

		log_header("Executing EQUIV_MAKE pass (creating equiv checking module).\n");

		worker.equiv_mod = design->addModule(RTLIL::escape_id(args[argidx+2]));
		worker.run();
	}
} EquivMakePass;

PRIVATE_NAMESPACE_END
