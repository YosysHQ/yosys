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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/mem.h"
#include "kernel/fstdata.h"

#include <ctime>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum class SimulationMode {
	cmp,
	gold,
	gate,
};

static const std::map<std::string, int> g_units =
{
	{ "",    -9 }, // default is ns
	{ "s",    0 },
	{ "ms",  -3 },
	{ "us",  -6 },
	{ "ns",  -9 },
	{ "ps", -12 },
	{ "fs", -15 },
	{ "as", -18 },
	{ "zs", -21 },
};

static double stringToTime(std::string str)
{
	if (str=="END") return -1;

	char *endptr;
	long value = strtol(str.c_str(), &endptr, 10);

	if (g_units.find(endptr)==g_units.end())
		log_error("Cannot parse '%s', bad unit '%s'\n", str.c_str(), endptr);

	if (value < 0)
		log_error("Time value '%s' must be positive\n", str.c_str());

	return value * pow(10.0, g_units.at(endptr));
}

struct SimShared
{
	bool debug = false;
	bool hide_internal = true;
	bool writeback = false;
	bool zinit = false;
	int rstlen = 1;
	FstData *fst = nullptr;
	double start_time = 0;
	double stop_time = -1;
	SimulationMode sim_mode = SimulationMode::cmp;
};

void zinit(State &v)
{
	if (v != State::S1)
		v = State::S0;
}

void zinit(Const &v)
{
	for (auto &bit : v.bits)
		zinit(bit);
}

struct SimInstance
{
	SimShared *shared;
	
	std::string scope;
	Module *module;
	Cell *instance;

	SimInstance *parent;
	dict<Cell*, SimInstance*> children;

	SigMap sigmap;
	dict<SigBit, State> state_nets;
	dict<SigBit, pool<Cell*>> upd_cells;
	dict<SigBit, pool<Wire*>> upd_outports;

	pool<SigBit> dirty_bits;
	pool<Cell*> dirty_cells;
	pool<IdString> dirty_memories;
	pool<SimInstance*, hash_ptr_ops> dirty_children;

	struct ff_state_t
	{
		State past_clock;
		Const past_d;
	};

	struct mem_state_t
	{
		Mem *mem;
		std::vector<Const> past_wr_clk;
		std::vector<Const> past_wr_en;
		std::vector<Const> past_wr_addr;
		std::vector<Const> past_wr_data;
		Const data;
	};

	dict<Cell*, ff_state_t> ff_database;
	dict<IdString, mem_state_t> mem_database;
	pool<Cell*> formal_database;
	dict<Cell*, IdString> mem_cells;

	std::vector<Mem> memories;

	dict<Wire*, pair<int, Const>> vcd_database;
	dict<Wire*, pair<fstHandle, Const>> fst_database;
	dict<Wire*, fstHandle> fst_handles;

	SimInstance(SimShared *shared, std::string scope, Module *module, Cell *instance = nullptr, SimInstance *parent = nullptr) :
			shared(shared), scope(scope), module(module), instance(instance), parent(parent), sigmap(module)
	{
		log_assert(module);

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

			if (shared->fst) {
				fstHandle id = shared->fst->getHandle(scope + "." + RTLIL::unescape_id(wire->name));
				if (id==0 && wire->name.isPublic())
					log_warning("Unable to found wire %s in input file.\n", (scope + "." + RTLIL::unescape_id(wire->name)).c_str());
				fst_handles[wire] = id;
			}

			if (wire->attributes.count(ID::init)) {
				Const initval = wire->attributes.at(ID::init);
				for (int i = 0; i < GetSize(sig) && i < GetSize(initval); i++)
					if (initval[i] == State::S0 || initval[i] == State::S1) {
						state_nets[sig[i]] = initval[i];
						dirty_bits.insert(sig[i]);
					}
			}
		}

		memories = Mem::get_all_memories(module);
		for (auto &mem : memories) {
			auto &mdb = mem_database[mem.memid];
			mdb.mem = &mem;
			for (auto &port : mem.wr_ports) {
				mdb.past_wr_clk.push_back(Const(State::Sx));
				mdb.past_wr_en.push_back(Const(State::Sx, GetSize(port.en)));
				mdb.past_wr_addr.push_back(Const(State::Sx, GetSize(port.addr)));
				mdb.past_wr_data.push_back(Const(State::Sx, GetSize(port.data)));
			}
			mdb.data = mem.get_init_data();
		}

		for (auto cell : module->cells())
		{
			Module *mod = module->design->module(cell->type);

			if (mod != nullptr) {
				dirty_children.insert(new SimInstance(shared, scope + "." + RTLIL::unescape_id(cell->name), mod, cell, this));
			}

			for (auto &port : cell->connections()) {
				if (cell->input(port.first))
					for (auto bit : sigmap(port.second)) {
						upd_cells[bit].insert(cell);
						// Make sure cell inputs connected to constants are updated in the first cycle
						if (bit.wire == nullptr)
							dirty_bits.insert(bit);
					}
			}

			if (cell->type.in(ID($dff))) {
				ff_state_t ff;
				ff.past_clock = State::Sx;
				ff.past_d = Const(State::Sx, cell->getParam(ID::WIDTH).as_int());
				ff_database[cell] = ff;
			}

			if (cell->is_mem_cell())
			{
				mem_cells[cell] = cell->parameters.at(ID::MEMID).decode_string();
			}
			if (cell->type.in(ID($assert), ID($cover), ID($assume))) {
				formal_database.insert(cell);
			}
		}

		if (shared->zinit)
		{
			for (auto &it : ff_database)
			{
				Cell *cell = it.first;
				ff_state_t &ff = it.second;
				zinit(ff.past_d);

				SigSpec qsig = cell->getPort(ID::Q);
				Const qdata = get_state(qsig);
				zinit(qdata);
				set_state(qsig, qdata);
			}

			for (auto &it : mem_database) {
				mem_state_t &mem = it.second;
				for (auto &val : mem.past_wr_en)
					zinit(val);
				zinit(mem.data);
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
		log_assert(GetSize(sig) <= GetSize(value));

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

		if (formal_database.count(cell))
			return;

		if (mem_cells.count(cell))
		{
			dirty_memories.insert(mem_cells[cell]);
			return;
		}

		if (children.count(cell))
		{
			auto child = children.at(cell);
			for (auto &conn: cell->connections())
				if (cell->input(conn.first) && GetSize(conn.second)) {
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

			has_a = cell->hasPort(ID::A);
			has_b = cell->hasPort(ID::B);
			has_c = cell->hasPort(ID::C);
			has_d = cell->hasPort(ID::D);
			has_s = cell->hasPort(ID::S);
			has_y = cell->hasPort(ID::Y);

			if (has_a) sig_a = cell->getPort(ID::A);
			if (has_b) sig_b = cell->getPort(ID::B);
			if (has_c) sig_c = cell->getPort(ID::C);
			if (has_d) sig_d = cell->getPort(ID::D);
			if (has_s) sig_s = cell->getPort(ID::S);
			if (has_y) sig_y = cell->getPort(ID::Y);

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

		log_error("Unsupported cell type: %s (%s.%s)\n", log_id(cell->type), log_id(module), log_id(cell));
	}

	void update_memory(IdString id) {
		auto &mdb = mem_database[id];
		auto &mem = *mdb.mem;

		for (int port_idx = 0; port_idx < GetSize(mem.rd_ports); port_idx++)
		{
			auto &port = mem.rd_ports[port_idx];
			Const addr = get_state(port.addr);
			Const data = Const(State::Sx, mem.width << port.wide_log2);

			if (port.clk_enable)
				log_error("Memory %s.%s has clocked read ports. Run 'memory' with -nordff.\n", log_id(module), log_id(mem.memid));

			if (addr.is_fully_def()) {
				int index = addr.as_int() - mem.start_offset;
				if (index >= 0 && index < mem.size)
					data = mdb.data.extract(index*mem.width, mem.width << port.wide_log2);
			}

			set_state(port.data, data);
		}
	}

	void update_ph1()
	{
		pool<Cell*> queue_cells;
		pool<Wire*> queue_outports;

		queue_cells.swap(dirty_cells);

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

			for (auto &memid : dirty_memories)
				update_memory(memid);
			dirty_memories.clear();

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

			if (cell->type.in(ID($dff)))
			{
				bool clkpol = cell->getParam(ID::CLK_POLARITY).as_bool();
				State current_clock = get_state(cell->getPort(ID::CLK))[0];

				if (clkpol ? (ff.past_clock == State::S1 || current_clock != State::S1) :
						(ff.past_clock == State::S0 || current_clock != State::S0))
					continue;

				if (set_state(cell->getPort(ID::Q), ff.past_d))
					did_something = true;
			}
		}

		for (auto &it : mem_database)
		{
			mem_state_t &mdb = it.second;
			auto &mem = *mdb.mem;

			for (int port_idx = 0; port_idx < GetSize(mem.wr_ports); port_idx++)
			{
				auto &port = mem.wr_ports[port_idx];
				Const addr, data, enable;

				if (!port.clk_enable)
				{
					addr = get_state(port.addr);
					data = get_state(port.data);
					enable = get_state(port.en);
				}
				else
				{
					if (port.clk_polarity ?
							(mdb.past_wr_clk[port_idx] == State::S1 || get_state(port.clk) != State::S1) :
							(mdb.past_wr_clk[port_idx] == State::S0 || get_state(port.clk) != State::S0))
						continue;

					addr = mdb.past_wr_addr[port_idx];
					data = mdb.past_wr_data[port_idx];
					enable = mdb.past_wr_en[port_idx];
				}

				if (addr.is_fully_def())
				{
					int index = addr.as_int() - mem.start_offset;
					if (index >= 0 && index < mem.size)
						for (int i = 0; i < (mem.width << port.wide_log2); i++)
							if (enable[i] == State::S1 && mdb.data.bits.at(index*mem.width+i) != data[i]) {
								mdb.data.bits.at(index*mem.width+i) = data[i];
								dirty_memories.insert(mem.memid);
								did_something = true;
							}
				}
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

			if (cell->type.in(ID($dff))) {
				ff.past_clock = get_state(cell->getPort(ID::CLK))[0];
				ff.past_d = get_state(cell->getPort(ID::D));
			}
		}

		for (auto &it : mem_database)
		{
			mem_state_t &mem = it.second;

			for (int i = 0; i < GetSize(mem.mem->wr_ports); i++) {
				auto &port = mem.mem->wr_ports[i];
				mem.past_wr_clk[i]  = get_state(port.clk);
				mem.past_wr_en[i]   = get_state(port.en);
				mem.past_wr_addr[i] = get_state(port.addr);
				mem.past_wr_data[i] = get_state(port.data);
			}
		}

		for (auto cell : formal_database)
		{
			string label = log_id(cell);
			if (cell->attributes.count(ID::src))
				label = cell->attributes.at(ID::src).decode_string();

			State a = get_state(cell->getPort(ID::A))[0];
			State en = get_state(cell->getPort(ID::EN))[0];

			if (cell->type == ID($cover) && en == State::S1 && a != State::S1)
				log("Cover %s.%s (%s) reached.\n", hiername().c_str(), log_id(cell), label.c_str());

			if (cell->type == ID($assume) && en == State::S1 && a != State::S1)
				log("Assumption %s.%s (%s) failed.\n", hiername().c_str(), log_id(cell), label.c_str());

			if (cell->type == ID($assert) && en == State::S1 && a != State::S1)
				log_warning("Assert %s.%s (%s) failed.\n", hiername().c_str(), log_id(cell), label.c_str());
		}

		for (auto it : children)
			it.second->update_ph3();
	}

	void writeback(pool<Module*> &wbmods)
	{
		if (wbmods.count(module))
			log_error("Instance %s of module %s is not unique: Writeback not possible. (Fix by running 'uniquify'.)\n", hiername().c_str(), log_id(module));

		wbmods.insert(module);

		for (auto wire : module->wires())
			wire->attributes.erase(ID::init);

		for (auto &it : ff_database)
		{
			Cell *cell = it.first;
			SigSpec sig_q = cell->getPort(ID::Q);
			Const initval = get_state(sig_q);

			for (int i = 0; i < GetSize(sig_q); i++)
			{
				Wire *w = sig_q[i].wire;

				if (w->attributes.count(ID::init) == 0)
					w->attributes[ID::init] = Const(State::Sx, GetSize(w));

				w->attributes[ID::init][sig_q[i].offset] = initval[i];
			}
		}

		for (auto &it : mem_database)
		{
			mem_state_t &mem = it.second;
			mem.mem->clear_inits();
			MemInit minit;
			minit.addr = mem.mem->start_offset;
			minit.data = mem.data;
			minit.en = Const(State::S1, mem.mem->width);
			mem.mem->inits.push_back(minit);
			mem.mem->emit();
		}

		for (auto it : children)
			it.second->writeback(wbmods);
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

	void write_fst_header(struct fstContext *f)
	{
		fstWriterSetScope(f, FST_ST_VCD_MODULE, stringf("%s",log_id(name())).c_str(), nullptr);
		for (auto wire : module->wires())
		{
			if (shared->hide_internal && wire->name[0] == '$')
				continue;

			fstHandle id = fstWriterCreateVar(f, FST_VT_VCD_WIRE, FST_VD_IMPLICIT, GetSize(wire),
												stringf("%s%s", wire->name[0] == '$' ? "\\" : "", log_id(wire)).c_str(), 0);
			fst_database[wire] = make_pair(id, Const());
		}

		for (auto child : children)
			child.second->write_fst_header(f);

		fstWriterSetUpscope(f);
	}

	void write_fst_step(struct fstContext *f)
	{
		for (auto &it : fst_database)
		{
			Wire *wire = it.first;
			Const value = get_state(wire);
			fstHandle id = it.second.first;

			if (it.second.second == value)
				continue;

			it.second.second = value;
			std::stringstream ss;
			for (int i = GetSize(value)-1; i >= 0; i--) {
				switch (value[i]) {
					case State::S0: ss << "0"; break;
					case State::S1: ss << "1"; break;
					case State::Sx: ss << "x"; break;
					default: ss << "z";
				}
			}
			fstWriterEmitValueChange(f, id, ss.str().c_str());
		}

		for (auto child : children)
			child.second->write_fst_step(f);
	}

	void setInitState(uint64_t time)
	{
		for (auto &it : ff_database)
		{
			Cell *cell = it.first;
			
			SigSpec qsig = cell->getPort(ID::Q);
			if (qsig.is_wire()) {
				IdString name = qsig.as_wire()->name;
				fstHandle id = shared->fst->getHandle(scope + "." + RTLIL::unescape_id(name));
				if (id==0 && name.isPublic())
					log_warning("Unable to found wire %s in input file.\n", (scope + "." + RTLIL::unescape_id(name)).c_str());
				if (id!=0) {
					Const fst_val = Const::from_string(shared->fst->valueAt(id, time));
					set_state(qsig, fst_val);
				}
			}
		}
		for (auto child : children)
			child.second->setInitState(time);
	}

	bool checkSignals(uint64_t time)
	{
		bool retVal = false;
		for(auto &item : fst_handles) {
			if (item.second==0) continue; // Ignore signals not found
			Const fst_val = Const::from_string(shared->fst->valueAt(item.second, time));
			Const sim_val = get_state(item.first);
			if (shared->sim_mode == SimulationMode::gate && !fst_val.is_fully_def()) { // FST data contains X
				// TODO: check bit by bit
			} else if (shared->sim_mode == SimulationMode::gold && !sim_val.is_fully_def()) { // sim data contains X
				// TODO: check bit by bit
			} else {
				if (fst_val!=sim_val) {
					retVal = true;
					log("signal: %s fst: %s  sim: %s\n", log_id(item.first), log_signal(fst_val), log_signal(sim_val));
				}
			}
			//log("signal: %s fst: %s  sim: %s\n", log_id(item.first), log_signal(fst_val), log_signal(sim_val));
		}
		for (auto child : children)
			retVal |= child.second->checkSignals(time);
		return retVal;
	}
};

struct SimWorker : SimShared
{
	SimInstance *top = nullptr;
	std::ofstream vcdfile;
	struct fstContext *fstfile = nullptr;
	pool<IdString> clock, clockn, reset, resetn;
	std::string timescale;
	std::string sim_filename;
	std::string scope;

	~SimWorker()
	{
		delete top;
	}

	void write_vcd_header()
	{
		vcdfile << stringf("$version %s $end\n", yosys_version_str);

		std::time_t t = std::time(nullptr);
		char mbstr[255];
		if (std::strftime(mbstr, sizeof(mbstr), "%c", std::localtime(&t))) {
			vcdfile << stringf("$date ") << mbstr << stringf(" $end\n");
		}

		if (!timescale.empty())
			vcdfile << stringf("$timescale %s $end\n", timescale.c_str());

		int id = 1;
		top->write_vcd_header(vcdfile, id);

		vcdfile << stringf("$enddefinitions $end\n");
	}

	void write_vcd_step(int t)
	{
		vcdfile << stringf("#%d\n", t);
		top->write_vcd_step(vcdfile);
	}

	void write_fst_header()
	{
		std::time_t t = std::time(nullptr);
		fstWriterSetDate(fstfile, asctime(std::localtime(&t)));
		fstWriterSetVersion(fstfile, yosys_version_str);
		if (!timescale.empty())
			fstWriterSetTimescaleFromString(fstfile, timescale.c_str());

		fstWriterSetPackType(fstfile, FST_WR_PT_FASTLZ);
		fstWriterSetRepackOnClose(fstfile, 1);
	   
		top->write_fst_header(fstfile);
	}

	void write_fst_step(int t)
	{
		fstWriterEmitTimeChange(fstfile, t);

		top->write_fst_step(fstfile);
	}

	void write_output_header()
	{
		if (vcdfile.is_open())
			write_vcd_header();
		if (fstfile)
			write_fst_header();
	}

	void write_output_step(int t)
	{
		if (vcdfile.is_open())
			write_vcd_step(t);
		if (fstfile)
			write_fst_step(t);
	}

	void write_output_end()
	{
		if (fstfile)
			fstWriterClose(fstfile);
	}

	void update()
	{
		while (1)
		{
			if (debug)
				log("\n-- ph1 --\n");

			top->update_ph1();

			if (debug)
				log("\n-- ph2 --\n");

			if (!top->update_ph2())
				break;
		}

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
		top = new SimInstance(this, scope, topmod);

		if (debug)
			log("\n===== 0 =====\n");
		else
			log("Simulating cycle 0.\n");

		set_inports(reset, State::S1);
		set_inports(resetn, State::S0);

		set_inports(clock, State::Sx);
		set_inports(clockn, State::Sx);

		update();

		write_output_header();
		write_output_step(0);

		for (int cycle = 0; cycle < numcycles; cycle++)
		{
			if (debug)
				log("\n===== %d =====\n", 10*cycle + 5);

			set_inports(clock, State::S0);
			set_inports(clockn, State::S1);

			update();
			write_output_step(10*cycle + 5);

			if (debug)
				log("\n===== %d =====\n", 10*cycle + 10);
			else
				log("Simulating cycle %d.\n", cycle+1);

			set_inports(clock, State::S1);
			set_inports(clockn, State::S0);

			if (cycle+1 == rstlen) {
				set_inports(reset, State::S0);
				set_inports(resetn, State::S1);
			}

			update();
			write_output_step(10*cycle + 10);
		}

		write_output_step(10*numcycles + 2);

		write_output_end();

		if (writeback) {
			pool<Module*> wbmods;
			top->writeback(wbmods);
		}
	}

	void run_cosim(Module *topmod, int numcycles)
	{
		log_assert(top == nullptr);
		fst = new FstData(sim_filename);

		top = new SimInstance(this, scope, topmod);

		std::vector<fstHandle> fst_clock;

		for (auto portname : clock)
		{
			Wire *w = topmod->wire(portname);
			if (!w)
				log_error("Can't find port %s on module %s.\n", log_id(portname), log_id(top->module));
			if (!w->port_input)
				log_error("Clock port %s on module %s is not input.\n", log_id(portname), log_id(top->module));
			fstHandle id = fst->getHandle(scope + "." + RTLIL::unescape_id(portname));
			if (id==0)
				log_error("Can't find port %s.%s in FST.\n", scope.c_str(), log_id(portname));
			fst_clock.push_back(id);
		}
		for (auto portname : clockn)
		{
			Wire *w = topmod->wire(portname);
			if (!w)
				log_error("Can't find port %s on module %s.\n", log_id(portname), log_id(top->module));
			if (!w->port_input)
				log_error("Clock port %s on module %s is not input.\n", log_id(portname), log_id(top->module));
			fstHandle id = fst->getHandle(scope + "." + RTLIL::unescape_id(portname));
			if (id==0)
				log_error("Can't find port %s.%s in FST.\n", scope.c_str(), log_id(portname));
			fst_clock.push_back(id);
		}
		if (fst_clock.size()==0)
			log_error("No clock signals defined for input file\n");

		SigMap sigmap(topmod);
		std::map<Wire*,fstHandle> inputs;

		for (auto wire : topmod->wires()) {
			if (wire->port_input) {
				fstHandle id = fst->getHandle(scope + "." + RTLIL::unescape_id(wire->name));
				inputs[wire] = id;
			}
		}

		uint64_t startCount = 0;
		uint64_t stopCount = 0;
		if (start_time==0) {
			if (start_time < fst->getStartTime())
				log_warning("Start time is before simulation file start time\n");
			startCount = fst->getStartTime();
		} else if (start_time==-1) 
			startCount = fst->getEndTime();
		else {
			startCount = start_time / fst->getTimescale();
			if (startCount > fst->getEndTime()) {
				startCount = fst->getEndTime();
				log_warning("Start time is after simulation file end time\n");
			}
		}
		if (stop_time==0) {
			if (stop_time < fst->getStartTime())
				log_warning("Stop time is before simulation file start time\n");
			stopCount = fst->getStartTime();
		} else if (stop_time==-1) 
			stopCount = fst->getEndTime();
		else {
			stopCount = stop_time / fst->getTimescale();
			if (stopCount > fst->getEndTime()) {
				stopCount = fst->getEndTime();
				log_warning("Stop time is after simulation file end time\n");
			}
		}
		if (stopCount<startCount) {
			log_error("Stop time is before start time\n");
		}
		auto edges = fst->getAllEdges(fst_clock, startCount, stopCount);
		
		if ((startCount == stopCount) && writeback) {
			log("Update initial state with values from %zu\n",startCount);
			if (edges.empty())
				edges.push_back(startCount);
			fst->reconstructAllAtTimes(edges);
			top->setInitState(startCount);
			pool<Module*> wbmods;
			top->writeback(wbmods);
		} else {
			if (edges.empty())
				log_error("No clock edges found in given time range\n");
			fst->reconstructAllAtTimes(edges);
			bool initial = false;
			for(auto &time : edges) {
				for(auto &item : inputs) {
					std::string v = fst->valueAt(item.second, time);
					top->set_state(item.first, Const::from_string(v));
				}
				if (!initial) {
					top->setInitState(time);
					initial = true;
				}
				update();

				bool status = top->checkSignals(time);
				if (status)
					log_error("Signal difference at %zu\n", time);
			}
		}
	}
};

struct SimPass : public Pass {
	SimPass() : Pass("sim", "simulate the circuit") { }
	void help() override
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
		log("    -fst <filename>\n");
		log("        write the simulation results to the given FST file\n");
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
		log("    -rstlen <integer>\n");
		log("        number of cycles reset should stay active (default: 1)\n");
		log("\n");
		log("    -zinit\n");
		log("        zero-initialize all uninitialized regs and memories\n");
		log("\n");
		log("    -timescale <string>\n");
		log("        include the specified timescale declaration in the vcd\n");
		log("\n");
		log("    -n <integer>\n");
		log("        number of cycles to simulate (default: 20)\n");
		log("\n");
		log("    -a\n");
		log("        include all nets in VCD output, not just those with public names\n");
		log("\n");
		log("    -w\n");
		log("        writeback mode: use final simulation state as new init state\n");
		log("\n");
		log("    -r\n");
		log("        read simulation results file (file formats supported: FST)\n");
		log("\n");
		log("    -scope\n");
		log("        scope of simulation top model\n");
		log("\n");
		log("    -start <time>\n");
		log("        start co-simulation in arbitary time (default 0)\n");
		log("\n");
		log("    -stop <time>\n");
		log("        stop co-simulation in arbitary time (default END)\n");
		log("\n");
		log("    -sim-cmp\n");
		log("        co-simulation expect exact match (default)\n");
		log("\n");
		log("    -sim-gold\n");
		log("        co-simulation, x in simulation can match any value in FST\n");
		log("\n");
		log("    -sim-gate\n");
		log("        co-simulation, x in FST can match any value in simulation\n");
		log("\n");
		log("    -d\n");
		log("        enable debug output\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		SimWorker worker;
		int numcycles = 20;

		log_header(design, "Executing SIM pass (simulate the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-vcd" && argidx+1 < args.size()) {
				std::string vcd_filename = args[++argidx];
				rewrite_filename(vcd_filename);
				worker.vcdfile.open(vcd_filename.c_str());
				continue;
			}
			if (args[argidx] == "-fst" && argidx+1 < args.size()) {
				std::string fst_filename = args[++argidx];
				rewrite_filename(fst_filename);
				worker.fstfile = (struct fstContext *)fstWriterCreate(fst_filename.c_str(),1);
				continue;
			}
			if (args[argidx] == "-n" && argidx+1 < args.size()) {
				numcycles = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-rstlen" && argidx+1 < args.size()) {
				worker.rstlen = atoi(args[++argidx].c_str());
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
			if (args[argidx] == "-timescale" && argidx+1 < args.size()) {
				worker.timescale = args[++argidx];
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
			if (args[argidx] == "-w") {
				worker.writeback = true;
				continue;
			}
			if (args[argidx] == "-zinit") {
				worker.zinit = true;
				continue;
			}
			if (args[argidx] == "-r" && argidx+1 < args.size()) {
				std::string sim_filename = args[++argidx];
				rewrite_filename(sim_filename);
				worker.sim_filename = sim_filename;
				continue;
			}
			if (args[argidx] == "-scope" && argidx+1 < args.size()) {
				worker.scope = args[++argidx];
				continue;
			}
			if (args[argidx] == "-start" && argidx+1 < args.size()) {
				worker.start_time = stringToTime(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-stop" && argidx+1 < args.size()) {
				worker.stop_time = stringToTime(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-sim-cmp") {
				worker.sim_mode = SimulationMode::cmp;
				continue;
			}
			if (args[argidx] == "-sim-gold") {
				worker.sim_mode = SimulationMode::gold;
				continue;
			}
			if (args[argidx] == "-sim-gate") {
				worker.sim_mode = SimulationMode::gate;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		Module *top_mod = nullptr;

		if (design->full_selection()) {
			top_mod = design->top_module();

			if (!top_mod)
				log_cmd_error("Design has no top module, use the 'hierarchy' command to specify one.\n");
		} else {
			auto mods = design->selected_whole_modules();
			if (GetSize(mods) != 1)
				log_cmd_error("Only one top module must be selected.\n");
			top_mod = mods.front();
		}

		if (worker.sim_filename.empty())
			worker.run(top_mod, numcycles);
		else
			worker.run_cosim(top_mod, numcycles);
	}
} SimPass;

PRIVATE_NAMESPACE_END
