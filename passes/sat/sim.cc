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

struct SimShared
{
	bool debug = false;
	bool hide_internal = true;
};

struct SimInstance
{
	SimShared *shared;

	Module *module;
	Cell *instance;

	SimInstance *parent;
	dict<Cell*, SimInstance*> children;

	SigMap sigmap;
	dict<SigBit, State> state_nets;
	dict<SigBit, pool<Cell*>> upd_cells;
	dict<SigBit, pool<Wire*>> upd_outports;

	pool<SigBit> dirty_bits;
	pool<SimInstance*, hash_ptr_ops> dirty_children;

	struct ff_state_t
	{
		State past_clock;
		Const past_d;
	};

	dict<Cell*, ff_state_t> ff_database;

	dict<Wire*, pair<int, Const>> vcd_database;

	SimInstance(SimShared *shared, Module *module, Cell *instance = nullptr, SimInstance *parent = nullptr) :
			shared(shared), module(module), instance(instance), parent(parent), sigmap(module)
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
				dirty_children.insert(new SimInstance(shared, mod, cell, this));
			}

			for (auto &port : cell->connections()) {
				if (cell->input(port.first))
					for (auto bit : sigmap(port.second))
						upd_cells[bit].insert(cell);
			}

			if (cell->type.in("$dff")) {
				ff_state_t ff;
				ff.past_clock = State::Sx;
				ff.past_d = Const(State::Sx, cell->getParam("\\WIDTH").as_int());
				ff_database[cell] = ff;
			}
		}
	}

	~SimInstance()
	{
		for (auto child : children)
			delete child.second;
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
			if (bit.wire == nullptr)
				value.bits.push_back(bit.data);
			else if (state_nets.count(bit))
				value.bits.push_back(state_nets.at(bit));
			else
				value.bits.push_back(State::Sz);

		if (shared->debug)
			log("[%s] get %s: %s\n", hiername().c_str(), log_signal(sig), log_signal(value));
		return value;
	}

	bool set_state(SigSpec sig, Const value)
	{
		bool did_something = false;

		sig = sigmap(sig);
		log_assert(GetSize(sig) == GetSize(value));

		for (int i = 0; i < GetSize(sig); i++)
			if (state_nets.at(sig[i]) != value[i]) {
				state_nets.at(sig[i]) = value[i];
				dirty_bits.insert(sig[i]);
				did_something = true;
			}

		if (shared->debug)
			log("[%s] set %s: %s\n", hiername().c_str(), log_signal(sig), log_signal(value));
		return did_something;
	}

	void update_cell(Cell *cell)
	{
		if (ff_database.count(cell))
			return;

		if (children.count(cell))
		{
			auto child = children.at(cell);
			for (auto &conn: cell->connections())
				if (cell->input(conn.first)) {
					Const value = get_state(conn.second);
					child->set_state(child->module->wire(conn.first), value);
				}
			dirty_children.insert(child);
			return;
		}

		if (yosys_celltypes.cell_evaluable(cell->type))
		{
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

			if (shared->debug)
				log("[%s] eval %s (%s)\n", hiername().c_str(), log_id(cell), log_id(cell->type));

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

	void update_ph1()
	{
		pool<Cell*> queue_cells;
		pool<Wire*> queue_outports;

		while (1)
		{
			for (auto bit : dirty_bits)
			{
				if (upd_cells.count(bit))
					for (auto cell : upd_cells.at(bit))
						queue_cells.insert(cell);

				if (upd_outports.count(bit) && parent != nullptr)
					for (auto wire : upd_outports.at(bit))
						queue_outports.insert(wire);
			}

			dirty_bits.clear();

			if (!queue_cells.empty())
			{
				for (auto cell : queue_cells)
					update_cell(cell);

				queue_cells.clear();
				continue;
			}

			for (auto wire : queue_outports)
				if (instance->hasPort(wire->name)) {
					Const value = get_state(wire);
					parent->set_state(instance->getPort(wire->name), value);
				}

			queue_outports.clear();

			for (auto child : dirty_children)
				child->update_ph1();

			dirty_children.clear();

			if (dirty_bits.empty())
				break;
		}
	}

	bool update_ph2()
	{
		bool did_something = false;

		for (auto &it : ff_database)
		{
			Cell *cell = it.first;
			ff_state_t &ff = it.second;

			if (cell->type.in("$dff"))
			{
				bool clkpol = cell->getParam("\\CLK_POLARITY").as_bool();
				State current_clock = get_state(cell->getPort("\\CLK"))[0];

				if (clkpol ? (ff.past_clock == State::S1 || current_clock != State::S1) :
						(ff.past_clock == State::S0 || current_clock != State::S0))
					continue;

				if (set_state(cell->getPort("\\Q"), ff.past_d))
					did_something = true;
			}
		}

		for (auto it : children)
			if (it.second->update_ph2()) {
				dirty_children.insert(it.second);
				did_something = true;
			}

		return did_something;
	}

	void update_ph3()
	{
		for (auto &it : ff_database)
		{
			Cell *cell = it.first;
			ff_state_t &ff = it.second;

			if (cell->type.in("$dff")) {
				ff.past_clock = get_state(cell->getPort("\\CLK"))[0];
				ff.past_d = get_state(cell->getPort("\\D"));
			}
		}

		for (auto it : children)
			it.second->update_ph3();
	}

	void write_vcd_header(std::ofstream &f, int &id)
	{
		f << stringf("$scope module %s $end\n", log_id(name()));

		for (auto wire : module->wires())
		{
			if (shared->hide_internal && wire->name[0] == '$')
				continue;

			f << stringf("$var wire %d n%d %s%s $end\n", GetSize(wire), id, wire->name[0] == '$' ? "\\" : "", log_id(wire));
			vcd_database[wire] = make_pair(id++, Const());
		}

		for (auto child : children)
			child.second->write_vcd_header(f, id);

		f << stringf("$upscope $end\n");
	}

	void write_vcd_step(std::ofstream &f)
	{
		for (auto &it : vcd_database)
		{
			Wire *wire = it.first;
			Const value = get_state(wire);
			int id = it.second.first;

			if (it.second.second == value)
				continue;

			it.second.second = value;

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

struct SimWorker : SimShared
{
	SimInstance *top = nullptr;
	std::ofstream vcdfile;
	pool<IdString> clock, clockn, reset, resetn;

	~SimWorker()
	{
		delete top;
	}

	void write_vcd_header()
	{
		if (!vcdfile.is_open())
			return;

		int id = 1;
		top->write_vcd_header(vcdfile, id);

		vcdfile << stringf("$enddefinitions $end\n");
	}

	void write_vcd_step(int t)
	{
		if (!vcdfile.is_open())
			return;

		vcdfile << stringf("#%d\n", t);
		top->write_vcd_step(vcdfile);
	}

	void update()
	{
		do
		{
			if (debug)
				log("\n-- ph1 --\n");

			top->update_ph1();

			if (debug)
				log("\n-- ph2 --\n");
		}
		while (top->update_ph2());

		if (debug)
			log("\n-- ph3 --\n");

		top->update_ph3();
	}

	void set_inports(pool<IdString> ports, State value)
	{
		for (auto portname : ports)
		{
			Wire *w = top->module->wire(portname);

			if (w == nullptr)
				log_error("Can't find port %s on module %s.\n", log_id(portname), log_id(top->module));

			top->set_state(w, value);
		}
	}

	void run(Module *topmod, int numcycles)
	{
		log_assert(top == nullptr);
		top = new SimInstance(this, topmod);

		if (debug)
			log("\n===== 0 =====\n");

		set_inports(reset, State::S1);
		set_inports(resetn, State::S0);

		update();

		write_vcd_header();
		write_vcd_step(0);

		for (int cycle = 0; cycle < numcycles; cycle++)
		{
			if (debug)
				log("\n===== %d =====\n", 10*cycle + 5);

			set_inports(clock, State::S0);
			set_inports(clockn, State::S1);

			update();
			write_vcd_step(10*cycle + 5);

			if (debug)
				log("\n===== %d =====\n", 10*cycle + 10);

			set_inports(clock, State::S1);
			set_inports(clockn, State::S0);

			if (cycle == 0) {
				set_inports(reset, State::S0);
				set_inports(resetn, State::S1);
			}

			update();
			write_vcd_step(10*cycle + 10);
		}

		write_vcd_step(10*numcycles + 2);
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
		log("    -clock <portname>\n");
		log("        name of top-level clock input\n");
		log("\n");
		log("    -clockn <portname>\n");
		log("        name of top-level clock input (inverse polarity)\n");
		log("\n");
		log("    -reset <portname>\n");
		log("        name of top-level reset input (active high)\n");
		log("\n");
		log("    -resetn <portname>\n");
		log("        name of top-level inverted reset input (active low)\n");
		log("\n");
		log("    -n <integer>\n");
		log("        number of cycles to simulate (default: 20)\n");
		log("\n");
		log("    -a\n");
		log("        include all nets in VCD output, nut just those with public names\n");
		log("\n");
		log("    -d\n");
		log("        enable debug output\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		SimWorker worker;
		int numcycles = 20;

		log_header(design, "Executing SIM pass (simulate the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-vcd" && argidx+1 < args.size()) {
				worker.vcdfile.open(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-n" && argidx+1 < args.size()) {
				numcycles = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-clock" && argidx+1 < args.size()) {
				worker.clock.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-clockn" && argidx+1 < args.size()) {
				worker.clockn.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-reset" && argidx+1 < args.size()) {
				worker.reset.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-resetn" && argidx+1 < args.size()) {
				worker.resetn.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-a") {
				worker.hide_internal = false;
				continue;
			}
			if (args[argidx] == "-d") {
				worker.debug = true;
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

		worker.run(top_mod, numcycles);
	}
} SimPass;

PRIVATE_NAMESPACE_END
