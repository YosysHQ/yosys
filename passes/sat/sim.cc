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

struct SimInstance
{
	Module *module;
	Cell *instance;

	SimInstance *parent;
	dict<Cell*, SimInstance*> children;

	SigMap sigmap;
	dict<SigBit, State> state_nets;
	dict<SigBit, pool<Cell*>> upd_cells;
	dict<SigBit, pool<Wire*>> upd_outports;

	pool<SigBit> dirty_bits;
	dict<SigBit, State> next_state_nets;

	dict<Wire*, int> vcd_netids;

	SimInstance(Module *module, Cell *instance = nullptr, SimInstance *parent = nullptr) :
			module(module), instance(instance), parent(parent), sigmap(module)
	{
		if (parent) {
			log_assert(parent->children.count(instance) == 0);
			parent->children[instance] = this;
		}

		for (auto wire : module->wires())
		{
			SigSpec sig = sigmap(wire);

			for (int i = 0; i < GetSize(sig); i++) {
				if (state_nets.count(sig[i]) == 0)
					state_nets[sig[i]] = State::Sx;
				if (wire->port_output) {
					upd_outports[sig[i]].insert(wire);
					dirty_bits.insert(sig[i]);
				}
			}

			if (wire->attributes.count("\\init")) {
				Const initval = wire->attributes.at("\\init");
				for (int i = 0; i < GetSize(sig) && i < GetSize(initval); i++)
					if (initval[i] == State::S0 || initval[i] == State::S1) {
						state_nets[sig[i]] = initval[i];
						dirty_bits.insert(sig[i]);
					}
			}
		}

		for (auto cell : module->cells())
		{
			Module *mod = module->design->module(cell->type);

			if (mod != nullptr) {
				new SimInstance(mod, cell, this);
			}

			for (auto &port : cell->connections()) {
				if (cell->input(port.first))
					for (auto bit : sigmap(port.second))
						upd_cells[bit].insert(cell);
			}
		}
	}

	IdString name() const
	{
		if (instance != nullptr)
			return instance->name;
		return module->name;
	}

	std::string hiername() const
	{
		if (instance != nullptr)
			return parent->hiername() + "." + log_id(instance->name);

		return log_id(module->name);
	}

	Const get_state(SigSpec sig)
	{
		Const value;

		for (auto bit : sigmap(sig))
			if (state_nets.count(bit))
				value.bits.push_back(state_nets.at(bit));
			else
				value.bits.push_back(State::Sz);

		// log("[%s] get %s: %s\n", hiername().c_str(), log_signal(sig), log_signal(value));
		return value;
	}

	void set_state(SigSpec sig, Const value)
	{
		sig = sigmap(sig);
		log_assert(GetSize(sig) == GetSize(value));

		for (int i = 0; i < GetSize(sig); i++)
			if (state_nets.at(sig[i]) != value[i]) {
				state_nets.at(sig[i]) = value[i];
				dirty_bits.insert(sig[i]);
			}

		// log("[%s] set %s: %s\n", hiername().c_str(), log_signal(sig), log_signal(value));
	}

	void update_cell(Cell *cell)
	{
		if (children.count(cell))
		{
			auto child = children.at(cell);
			for (auto &conn: cell->connections())
				if (cell->input(conn.first)) {
					Const value = get_state(conn.second);
					child->set_state(child->module->wire(conn.first), value);
				}
			return;
		}

		if (yosys_celltypes.cell_evaluable(cell->type))
		{
			// log("[%s] eval %s (%s)\n", hiername().c_str(), log_id(cell), log_id(cell->type));

			RTLIL::SigSpec sig_a, sig_b, sig_c, sig_d, sig_s, sig_y;
			bool has_a, has_b, has_c, has_d, has_s, has_y;

			has_a = cell->hasPort("\\A");
			has_b = cell->hasPort("\\B");
			has_c = cell->hasPort("\\C");
			has_d = cell->hasPort("\\D");
			has_s = cell->hasPort("\\S");
			has_y = cell->hasPort("\\Y");

			if (has_a) sig_a = cell->getPort("\\A");
			if (has_b) sig_b = cell->getPort("\\B");
			if (has_c) sig_c = cell->getPort("\\C");
			if (has_d) sig_d = cell->getPort("\\D");
			if (has_s) sig_s = cell->getPort("\\S");
			if (has_y) sig_y = cell->getPort("\\Y");

			// Simple (A -> Y) and (A,B -> Y) cells
			if (has_a && !has_c && !has_d && !has_s && has_y) {
				set_state(sig_y, CellTypes::eval(cell, get_state(sig_a), get_state(sig_b)));
				return;
			}

			// (A,B,C -> Y) cells
			if (has_a && has_b && has_c && !has_d && !has_s && has_y) {
				set_state(sig_y, CellTypes::eval(cell, get_state(sig_a), get_state(sig_b), get_state(sig_c)));
				return;
			}

			// (A,B,S -> Y) cells
			if (has_a && has_b && !has_c && !has_d && has_s && has_y) {
				set_state(sig_y, CellTypes::eval(cell, get_state(sig_a), get_state(sig_b), get_state(sig_s)));
				return;
			}

			log_warning("Unsupported evaluable cell type: %s (%s.%s)\n", log_id(cell->type), log_id(module), log_id(cell));
			return;
		}

		// FIXME

		log_warning("Unsupported cell type: %s (%s.%s)\n", log_id(cell->type), log_id(module), log_id(cell));
	}

	void update()
	{
		while (1)
		{
			while (!dirty_bits.empty())
			{
				SigBit bit = *dirty_bits.begin();
				dirty_bits.erase(bit);

				if (upd_cells.count(bit))
				{
					for (auto cell : upd_cells.at(bit))
						update_cell(cell);
				}

				if (upd_outports.count(bit) && parent != nullptr)
				{
					for (auto wire : upd_outports.at(bit))
						if (instance->hasPort(wire->name)) {
							Const value = get_state(wire);
							parent->set_state(instance->getPort(wire->name), value);
						}
				}
			}

			for (auto child : children)
				child.second->update();

			if (dirty_bits.empty())
				break;
		}
	}

	void write_vcd_header(std::ofstream &f, int &id)
	{
		f << stringf("$scope module %s $end\n", log_id(name()));

		for (auto wire : module->wires())
		{
			if (wire->name[0] == '$')
				continue;

			f << stringf("$var wire %d n%d %s $end\n", GetSize(wire), id, log_id(wire));
			vcd_netids[wire] = id++;
		}

		for (auto child : children)
			child.second->write_vcd_header(f, id);

		f << stringf("$upscope $end\n");
	}

	void write_vcd_step(std::ofstream &f)
	{
		for (auto it : vcd_netids)
		{
			Wire *wire = it.first;
			Const value = get_state(wire);
			int id = it.second;

			f << "b";
			for (int i = GetSize(value)-1; i >= 0; i--) {
				switch (value[i]) {
					case State::S0: f << "0"; break;
					case State::S1: f << "1"; break;
					case State::Sx: f << "x"; break;
					default: f << "z";
				}
			}

			f << stringf(" n%d\n", id);
		}

		for (auto child : children)
			child.second->write_vcd_step(f);
	}
};

struct SimWorker
{
	SimInstance *top = nullptr;
	std::ofstream vcdfile;

	void initialize(Module *topmod)
	{
		top = new SimInstance(topmod);
		top->update();
	}

	void step()
	{
		// FIXME
	}

	void write_vcd_header()
	{
		if (!vcdfile.is_open())
			return;

		int id = 1;
		top->write_vcd_header(vcdfile, id);

		vcdfile << stringf("$enddefinitions $end\n");
	}

	void write_vcd_step(int n)
	{
		if (!vcdfile.is_open())
			return;

		vcdfile << stringf("#%d\n", 10*n);
		top->write_vcd_step(vcdfile);
	}
};

struct SimPass : public Pass {
	SimPass() : Pass("sim", "simulate the circuit") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sim [options] [top-level]\n");
		log("\n");
		log("This command simulates the circuit using the given top-level module.\n");
		log("\n");
		log("    -vcd <filename>\n");
		log("        write the simulation results to the given VCD file\n");
		log("\n");
		log("    -n <integer>\n");
		log("        number of steps to simulate (default: 20)\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		SimWorker worker;
		int numsteps = 20;

		log_header(design, "Executing SIM pass (simulate the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-vcd" && argidx+1 < args.size()) {
				worker.vcdfile.open(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-n" && argidx+1 < args.size()) {
				numsteps = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		Module *top_mod = nullptr;

		if (design->full_selection()) {
			top_mod = design->top_module();
		} else {
			auto mods = design->selected_whole_modules();
			if (GetSize(mods) != 1)
				log_cmd_error("Only one top module must be selected.\n");
			top_mod = mods.front();
		}

		worker.initialize(top_mod);
		worker.write_vcd_header();
		worker.write_vcd_step(0);

		for (int i = 1; i < numsteps; i++) {
			worker.step();
			worker.write_vcd_step(i);
		}
	}
} SimPass;

PRIVATE_NAMESPACE_END
