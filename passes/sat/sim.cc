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
#include "kernel/ff.h"
#include "kernel/yw.h"
#include "kernel/json.h"
#include "kernel/fmt.h"

#include <ctime>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum class SimulationMode {
	sim,
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

struct SimWorker;
struct OutputWriter
{
	OutputWriter(SimWorker *w) { worker = w;};
	virtual ~OutputWriter() {};
	virtual void write(std::map<int, bool> &use_signal) = 0;
	SimWorker *worker;
};

struct SimInstance;
struct TriggeredAssertion {
	int step;
	SimInstance *instance;
	Cell *cell;

	TriggeredAssertion(int step, SimInstance *instance, Cell *cell) :
		step(step), instance(instance), cell(cell)
	{ }
};

struct DisplayOutput {
	int step;
	SimInstance *instance;
	Cell *cell;
	std::string output;

	DisplayOutput(int step, SimInstance *instance, Cell *cell, std::string output) :
		step(step), instance(instance), cell(cell), output(output)
	{ }
};

struct SimShared
{
	bool debug = false;
	bool verbose = true;
	bool hide_internal = true;
	bool writeback = false;
	bool zinit = false;
	bool hdlname = false;
	int rstlen = 1;
	FstData *fst = nullptr;
	double start_time = 0;
	double stop_time = -1;
	SimulationMode sim_mode = SimulationMode::sim;
	bool cycles_set = false;
	std::vector<std::unique_ptr<OutputWriter>> outputfiles;
	std::vector<std::pair<int,std::map<int,Const>>> output_data;
	bool ignore_x = false;
	bool date = false;
	bool multiclock = false;
	int next_output_id = 0;
	int step = 0;
	std::vector<TriggeredAssertion> triggered_assertions;
	std::vector<DisplayOutput> display_output;
	bool serious_asserts = false;
	bool initstate = true;
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

	dict<SigBit, SigBit> in_parent_drivers;
	dict<SigBit, SigBit> clk2fflogic_drivers;

	pool<SigBit> dirty_bits;
	pool<Cell*> dirty_cells;
	pool<IdString> dirty_memories;
	pool<SimInstance*, hash_ptr_ops> dirty_children;

	struct ff_state_t
	{
		Const past_d;
		Const past_ad;
		State past_clk;
		State past_ce;
		State past_srst;
		
		FfData data;
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

	struct print_state_t
	{
		bool initial_done;
		Const past_trg;
		Const past_en;
		Const past_args;

		Cell *cell;
		Fmt fmt;

		std::tuple<bool, SigSpec, Const, int, Cell*> _sort_label() const
		{
			return std::make_tuple(
				cell->getParam(ID::TRG_ENABLE).as_bool(), // Group by trigger
				cell->getPort(ID::TRG),
				cell->getParam(ID::TRG_POLARITY),
				-cell->getParam(ID::PRIORITY).as_int(), // Then sort by descending PRIORITY
				cell
			);
		}

		bool operator<(const print_state_t &other) const
		{
			return _sort_label() < other._sort_label();
		}
	};

	dict<Cell*, ff_state_t> ff_database;
	dict<IdString, mem_state_t> mem_database;
	pool<Cell*> formal_database;
	pool<Cell*> initstate_database;
	dict<Cell*, IdString> mem_cells;
	std::vector<print_state_t> print_database;

	std::vector<Mem> memories;

	dict<Wire*, pair<int, Const>> signal_database;
	dict<IdString, std::map<int, pair<int, Const>>> trace_mem_database;
	dict<std::pair<IdString, int>, Const> trace_mem_init_database;
	dict<Wire*, fstHandle> fst_handles;
	dict<Wire*, fstHandle> fst_inputs;
	dict<IdString, dict<int,fstHandle>> fst_memories;

	SimInstance(SimShared *shared, std::string scope, Module *module, Cell *instance = nullptr, SimInstance *parent = nullptr) :
			shared(shared), scope(scope), module(module), instance(instance), parent(parent), sigmap(module)
	{
		log_assert(module);

		if (module->get_blackbox_attribute(true))
			log_error("Cannot simulate blackbox module %s (instantiated at %s).\n",
					  log_id(module->name), hiername().c_str());

		if (module->has_processes())
			log_error("Found processes in simulation hierarchy (in module %s at %s). Run 'proc' first.\n",
					  log_id(module), hiername().c_str());

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

			if ((shared->fst) && !(shared->hide_internal && wire->name[0] == '$')) {
				fstHandle id = shared->fst->getHandle(scope + "." + RTLIL::unescape_id(wire->name));
				if (id==0 && wire->name.isPublic())
					log_warning("Unable to find wire %s in input file.\n", (scope + "." + RTLIL::unescape_id(wire->name)).c_str());
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

			if (wire->port_input && instance != nullptr && parent != nullptr) {
				for (int i = 0; i < GetSize(sig); i++) {
					if (instance->hasPort(wire->name))
						in_parent_drivers.emplace(sig[i], parent->sigmap(instance->getPort(wire->name)[i]));
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

			if (RTLIL::builtin_ff_cell_types().count(cell->type) || cell->type == ID($anyinit)) {
				FfData ff_data(nullptr, cell);
				ff_state_t ff;
				ff.past_d = Const(State::Sx, ff_data.width);
				ff.past_ad = Const(State::Sx, ff_data.width);
				ff.past_clk = State::Sx;
				ff.past_ce = State::Sx;
				ff.past_srst = State::Sx;
				ff.data = ff_data;
				ff_database[cell] = ff;

				if (cell->get_bool_attribute(ID(clk2fflogic))) {
					for (int i = 0; i < ff_data.width; i++)
						clk2fflogic_drivers.emplace(sigmap(ff_data.sig_d[i]), sigmap(ff_data.sig_q[i]));
				}
			}

			if (cell->is_mem_cell())
			{
				std::string name = cell->parameters.at(ID::MEMID).decode_string();
				mem_cells[cell] = name;
				if (shared->fst)
					fst_memories[name] = shared->fst->getMemoryHandles(scope + "." + RTLIL::unescape_id(name));
			}

			if (cell->type.in(ID($assert), ID($cover), ID($assume)))
				formal_database.insert(cell);

			if (cell->type == ID($initstate))
				initstate_database.insert(cell);

			if (cell->type == ID($print)) {
				print_database.emplace_back();
				auto &print = print_database.back();
				print.cell = cell;
				print.fmt.parse_rtlil(cell);
				print.past_trg = Const(State::Sx, cell->getPort(ID::TRG).size());
				print.past_args = Const(State::Sx, cell->getPort(ID::ARGS).size());
				print.past_en = State::Sx;
				print.initial_done = false;
			}
		}

		std::sort(print_database.begin(), print_database.end());

		if (shared->zinit)
		{
			for (auto &it : ff_database)
			{
				ff_state_t &ff = it.second;
				zinit(ff.past_d);
				zinit(ff.past_ad);

				SigSpec qsig = it.second.data.sig_q;
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

	vector<std::string> witness_full_path() const
	{
		if (instance != nullptr)
			return parent->witness_full_path(instance);
		return vector<std::string>();
	}

	vector<std::string> witness_full_path(Cell *cell) const
	{
		auto result = witness_full_path();
		auto cell_path = witness_path(cell);
		result.insert(result.end(), cell_path.begin(), cell_path.end());
		return result;
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
			if (value[i] != State::Sa && state_nets.at(sig[i]) != value[i]) {
				state_nets.at(sig[i]) = value[i];
				dirty_bits.insert(sig[i]);
				did_something = true;
			}

		if (shared->debug)
			log("[%s] set %s: %s\n", hiername().c_str(), log_signal(sig), log_signal(value));
		return did_something;
	}

	void set_state_parent_drivers(SigSpec sig, Const value)
	{
		sigmap.apply(sig);

		for (int i = 0; i < GetSize(sig); i++) {
			auto sigbit = sig[i];
			auto sigval = value[i];

			auto clk2fflogic_driver = clk2fflogic_drivers.find(sigbit);
			if (clk2fflogic_driver != clk2fflogic_drivers.end())
				sigbit = clk2fflogic_driver->second;

			auto in_parent_driver = in_parent_drivers.find(sigbit);
			if (in_parent_driver == in_parent_drivers.end())
				set_state(sigbit, sigval);
			else
				parent->set_state_parent_drivers(in_parent_driver->second, sigval);
		}
	}

	void set_memory_state(IdString memid, Const addr, Const data)
	{
		set_memory_state(memid, addr.as_int(), data);
	}

	void set_memory_state(IdString memid, int addr, Const data)
	{
		auto &state = mem_database[memid];

		bool dirty = false;

		int offset = (addr - state.mem->start_offset) * state.mem->width;
		for (int i = 0; i < GetSize(data); i++)
			if (0 <= i+offset && i+offset < state.mem->size * state.mem->width && data.bits[i] != State::Sa)
				if (state.data.bits[i+offset] != data.bits[i])
					dirty = true, state.data.bits[i+offset] = data.bits[i];

		if (dirty)
			dirty_memories.insert(memid);
	}

	void set_memory_state_bit(IdString memid, int offset, State data)
	{
		auto &state = mem_database[memid];
		if (offset >= state.mem->size * state.mem->width)
			log_error("Addressing out of bounds bit %d/%d of memory %s\n", offset, state.mem->size * state.mem->width, log_id(memid));
		if (state.data.bits[offset] != data) {
			state.data.bits[offset] = data;
			dirty_memories.insert(memid);
		}
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

			// (A,S -> Y) cells
			if (has_a && !has_b && !has_c && !has_d && has_s && has_y) {
				set_state(sig_y, CellTypes::eval(cell, get_state(sig_a), get_state(sig_s)));
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

		if (cell->type == ID($print))
			return;

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
				log_error("Memory %s.%s has clocked read ports. Run 'memory_nordff' to transform the circuit to remove those.\n", log_id(module), log_id(mem.memid));

			if (addr.is_fully_def()) {
				int addr_int = addr.as_int();
				int index = addr_int - mem.start_offset;
				if (index >= 0 && index < mem.size)
					data = mdb.data.extract(index*mem.width, mem.width << port.wide_log2);

				for (int offset = 0; offset < 1 << port.wide_log2; offset++) {
					register_memory_addr(id, addr_int + offset);
				}
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

	bool update_ph2(bool gclk, bool stable_past_update = false)
	{
		bool did_something = false;

		for (auto &it : ff_database)
		{
			ff_state_t &ff = it.second;
			FfData &ff_data = ff.data;

			Const current_q = get_state(ff.data.sig_q);

			if (ff_data.has_clk && !stable_past_update) {
				// flip-flops
				State current_clk = get_state(ff_data.sig_clk)[0];
				if (ff_data.pol_clk ? (ff.past_clk == State::S0 && current_clk != State::S0) :
							(ff.past_clk == State::S1 && current_clk != State::S1)) {
					bool ce = ff.past_ce == (ff_data.pol_ce ? State::S1 : State::S0);
					// set if no ce, or ce is enabled
					if (!ff_data.has_ce || (ff_data.has_ce && ce)) {
						current_q = ff.past_d;
					}
					// override if sync reset
					if ((ff_data.has_srst) && (ff.past_srst == (ff_data.pol_srst ? State::S1 : State::S0)) &&
						((!ff_data.ce_over_srst) || (ff_data.ce_over_srst && ce))) {
						current_q = ff_data.val_srst;
					}
				}
			}
			// async load
			if (ff_data.has_aload) {
				State current_aload = get_state(ff_data.sig_aload)[0];
				if (current_aload == (ff_data.pol_aload ? State::S1 : State::S0)) {
					current_q = ff_data.has_clk && !stable_past_update ? ff.past_ad : get_state(ff.data.sig_ad);
				}
			}
			// async reset
			if (ff_data.has_arst) {
				State current_arst = get_state(ff_data.sig_arst)[0];
				if (current_arst == (ff_data.pol_arst ? State::S1 : State::S0)) {
					current_q = ff_data.val_arst;
				}
			}
			// handle set/reset
			if (ff.data.has_sr) {
				Const current_clr = get_state(ff.data.sig_clr);
				Const current_set = get_state(ff.data.sig_set);

				for(int i=0;i<ff.past_d.size();i++) {
					if (current_clr[i] == (ff_data.pol_clr ? State::S1 : State::S0)) {
						current_q[i] = State::S0;
					}
					else if (current_set[i] == (ff_data.pol_set ? State::S1 : State::S0)) {
						current_q[i] = State::S1;
					}
				}
			}
			if (ff_data.has_gclk) {
				// $ff
				if (gclk)
					current_q = ff.past_d;
			}
			if (set_state(ff_data.sig_q, current_q))
				did_something = true;
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
					if (stable_past_update)
						continue;
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
					int addr_int = addr.as_int();
					int index = addr_int - mem.start_offset;
					if (index >= 0 && index < mem.size)
						for (int i = 0; i < (mem.width << port.wide_log2); i++)
							if (enable[i] == State::S1 && mdb.data.bits.at(index*mem.width+i) != data[i]) {
								mdb.data.bits.at(index*mem.width+i) = data[i];
								dirty_memories.insert(mem.memid);
								did_something = true;
							}

					for (int i = 0; i < 1 << port.wide_log2; i++)
						register_memory_addr(it.first, addr_int + i);
				}
			}
		}

		for (auto it : children)
			if (it.second->update_ph2(gclk, stable_past_update)) {
				dirty_children.insert(it.second);
				did_something = true;
			}

		return did_something;
	}

	static void log_source(RTLIL::AttrObject *src)
	{
		for (auto src : src->get_strpool_attribute(ID::src))
			log("    %s\n", src.c_str());
	}

	void log_cell_w_hierarchy(std::string opening_verbiage, RTLIL::Cell *cell)
	{
		log_assert(cell->module == module);
		bool has_src = cell->has_attribute(ID::src);
		log("%s %s%s\n", opening_verbiage.c_str(),
			log_id(cell), has_src ? " at" : "");
		log_source(cell);

		struct SimInstance *sim = this;
		while (sim->instance) {
			has_src = sim->instance->has_attribute(ID::src);
			log("  in instance %s of module %s%s\n", log_id(sim->instance),
				log_id(sim->instance->type), has_src ? " at" : "");
			log_source(sim->instance);
			sim = sim->parent;
		}
	}

	void update_ph3(bool gclk_trigger)
	{
		for (auto &it : ff_database)
		{
			ff_state_t &ff = it.second;

			if (ff.data.has_aload)
				ff.past_ad = get_state(ff.data.sig_ad);

			if (ff.data.has_clk || ff.data.has_gclk)
				ff.past_d = get_state(ff.data.sig_d);

			if (ff.data.has_clk)
				ff.past_clk = get_state(ff.data.sig_clk)[0];

			if (ff.data.has_ce)
				ff.past_ce = get_state(ff.data.sig_ce)[0];

			if (ff.data.has_srst)
				ff.past_srst = get_state(ff.data.sig_srst)[0];
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

		// Do prints *before* assertions
		for (auto &print : print_database) {
			Cell *cell = print.cell;
			bool triggered = false;

			Const trg = get_state(cell->getPort(ID::TRG));
			bool trg_en = cell->getParam(ID::TRG_ENABLE).as_bool();
			Const en = get_state(cell->getPort(ID::EN));
			Const args = get_state(cell->getPort(ID::ARGS));

			bool sampled = trg_en && trg.size() > 0;

			if (sampled ? print.past_en.as_bool() : en.as_bool()) {
				if (sampled) {
					sampled = true;
					Const trg_pol = cell->getParam(ID::TRG_POLARITY);
					for (int i = 0; i < trg.size(); i++) {
						bool pol = trg_pol[i] == State::S1;
						State curr = trg[i], past = print.past_trg[i];
						if (pol && curr == State::S1 && past == State::S0)
							triggered = true;
						if (!pol && curr == State::S0 && past == State::S1)
							triggered = true;
					}
				} else if (trg_en) {
					// initial $print (TRG width = 0, TRG_ENABLE = true)
					if (!print.initial_done && en != print.past_en)
						triggered = true;
				} else if (cell->get_bool_attribute(ID(trg_on_gclk))) {
					// unified $print for cycle based FV semantics
					triggered = gclk_trigger;
				} else {
					// always @(*) $print
					if (args != print.past_args || en != print.past_en)
						triggered = true;
				}

				if (triggered) {
					int pos = 0;
					for (auto &part : print.fmt.parts) {
						part.sig = (sampled ? print.past_args : args).extract(pos, part.sig.size());
						pos += part.sig.size();
					}

					std::string rendered = print.fmt.render();
					log("%s", rendered.c_str());
					shared->display_output.emplace_back(shared->step, this, cell, rendered);
				}
			}

			print.past_trg = trg;
			print.past_en = en;
			print.past_args = args;
			print.initial_done = true;
		}

		if (gclk_trigger)
		{
			for (auto cell : formal_database)
			{
				string label = log_id(cell);
				if (cell->attributes.count(ID::src))
					label = cell->attributes.at(ID::src).decode_string();

				State a = get_state(cell->getPort(ID::A))[0];
				State en = get_state(cell->getPort(ID::EN))[0];

				if (en == State::S1 && (cell->type == ID($cover) ? a == State::S1 : a != State::S1)) {
					shared->triggered_assertions.emplace_back(shared->step, this, cell);
				}

				if (cell->type == ID($cover) && en == State::S1 && a == State::S1)
					log("Cover %s.%s (%s) reached.\n", hiername().c_str(), log_id(cell), label.c_str());

				if (cell->type == ID($assume) && en == State::S1 && a != State::S1)
					log("Assumption %s.%s (%s) failed.\n", hiername().c_str(), log_id(cell), label.c_str());

				if (cell->type == ID($assert) && en == State::S1 && a != State::S1) {
					log_cell_w_hierarchy("Failed assertion", cell);
					if (shared->serious_asserts)
						log_error("Assertion %s.%s (%s) failed.\n", hiername().c_str(), log_id(cell), label.c_str());
					else
						log_warning("Assertion %s.%s (%s) failed.\n", hiername().c_str(), log_id(cell), label.c_str());
				}
			}
		}

		for (auto it : children)
			it.second->update_ph3(gclk_trigger);
	}

	void set_initstate_outputs(State state)
	{
		for (auto cell : initstate_database)
			set_state(cell->getPort(ID::Y), state);
		for (auto child : children)
			child.second->set_initstate_outputs(state);
	}

	void writeback(pool<Module*> &wbmods)
	{
		if (!ff_database.empty() || !mem_database.empty()) {
			if (wbmods.count(module))
				log_error("Instance %s of module %s is not unique: Writeback not possible. (Fix by running 'uniquify'.)\n", hiername().c_str(), log_id(module));
			wbmods.insert(module);
		}

		for (auto wire : module->wires())
			wire->attributes.erase(ID::init);

		for (auto &it : ff_database)
		{
			SigSpec sig_q = it.second.data.sig_q;
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

	void register_signals(int &id)
	{
		for (auto wire : module->wires())
		{
			if (shared->hide_internal && wire->name[0] == '$')
				continue;

			signal_database[wire] = make_pair(id, Const());
			id++;
		}

		for (auto child : children)
			child.second->register_signals(id);
	}

	void write_output_header(std::function<void(IdString)> enter_scope, std::function<void()> exit_scope, std::function<void(const char*, int, Wire*, int, bool)> register_signal)
	{
		int exit_scopes = 1;
		if (shared->hdlname && instance != nullptr && instance->name.isPublic() && instance->has_attribute(ID::hdlname)) {
			auto hdlname = instance->get_hdlname_attribute();
			log_assert(!hdlname.empty());
			for (auto name : hdlname)
				enter_scope("\\" + name);
			exit_scopes = hdlname.size();
		} else
			enter_scope(name());

		dict<Wire*,bool> registers;
		for (auto cell : module->cells())
		{
			if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
				FfData ff_data(nullptr, cell);
				SigSpec q = sigmap(ff_data.sig_q);
				if (q.is_wire() && signal_database.count(q.as_wire()) != 0) {
					registers[q.as_wire()] = true;
				}
			}
		}
		
		for (auto signal : signal_database)
		{
			if (shared->hdlname && signal.first->name.isPublic() && signal.first->has_attribute(ID::hdlname)) {
				auto hdlname = signal.first->get_hdlname_attribute();
				log_assert(!hdlname.empty());
				auto signal_name = std::move(hdlname.back());
				hdlname.pop_back();
				for (auto name : hdlname)
					enter_scope("\\" + name);
				register_signal(signal_name.c_str(), GetSize(signal.first), signal.first, signal.second.first, registers.count(signal.first)!=0);
				for (auto name : hdlname)
					exit_scope();
			} else
				register_signal(log_id(signal.first->name), GetSize(signal.first), signal.first, signal.second.first, registers.count(signal.first)!=0);
		}

		for (auto &trace_mem : trace_mem_database)
		{
			auto memid = trace_mem.first;
			auto &mdb = mem_database.at(memid);
			Cell *cell = mdb.mem->cell;

			std::vector<std::string> hdlname;
			std::string signal_name;
			bool has_hdlname = shared->hdlname && cell != nullptr && cell->name.isPublic() && cell->has_attribute(ID::hdlname);

			if (has_hdlname) {
				hdlname = cell->get_hdlname_attribute();
				log_assert(!hdlname.empty());
				signal_name = std::move(hdlname.back());
				hdlname.pop_back();
				for (auto name : hdlname)
					enter_scope("\\" + name);
			} else {
				signal_name = log_id(memid);
			}

			for (auto &trace_index : trace_mem.second) {
				int output_id = trace_index.second.first;
				int index = trace_index.first;
				register_signal(
						stringf("%s[%d]", signal_name.c_str(), (index + mdb.mem->start_offset)).c_str(),
						mdb.mem->width, nullptr, output_id, true);
			}

			if (has_hdlname)
				for (auto name : hdlname)
					exit_scope();
		}

		for (auto child : children)
			child.second->write_output_header(enter_scope, exit_scope, register_signal);

		for (int i = 0; i < exit_scopes; i++)
			exit_scope();
	}

	void register_memory_addr(IdString memid, int addr)
	{
		auto &mdb = mem_database.at(memid);
		auto &mem = *mdb.mem;
		int index = addr - mem.start_offset;
		if (index < 0 || index >= mem.size)
			return;
		auto it = trace_mem_database.find(memid);
		if (it != trace_mem_database.end() && it->second.count(index))
			return;
		int output_id = shared->next_output_id++;
		Const data;
		if (!shared->output_data.empty()) {
			auto init_it = trace_mem_init_database.find(std::make_pair(memid, addr));
			if (init_it != trace_mem_init_database.end())
				data = init_it->second;
			else
				data = mem.get_init_data().extract(index * mem.width, mem.width);
			shared->output_data.front().second.emplace(output_id, data);
		}
		trace_mem_database[memid].emplace(index, make_pair(output_id, data));

	}

	void register_output_step_values(std::map<int,Const> *data)
	{
		for (auto &it : signal_database)
		{
			Wire *wire = it.first;
			Const value = get_state(wire);
			int id = it.second.first;

			if (it.second.second == value)
				continue;

			it.second.second = value;
			data->emplace(id, value);
		}

		for (auto &trace_mem : trace_mem_database)
		{
			auto memid = trace_mem.first;
			auto &mdb = mem_database.at(memid);
			auto &mem = *mdb.mem;
			for (auto &trace_index : trace_mem.second)
			{
				int output_id = trace_index.second.first;
				int index = trace_index.first;

				auto value = mdb.data.extract(index * mem.width, mem.width);

				if (trace_index.second.second == value)
					continue;

				trace_index.second.second = value;
				data->emplace(output_id, value);
			}
		}

		for (auto child : children)
			child.second->register_output_step_values(data);
	}

	bool setInitState()
	{
		bool did_something = false;
		for(auto &item : fst_handles) {
			if (item.second==0) continue; // Ignore signals not found
			std::string v = shared->fst->valueOf(item.second);
			did_something |= set_state(item.first, Const::from_string(v));
		}
		for (auto cell : module->cells())
		{
			if (cell->is_mem_cell()) {
				std::string memid = cell->parameters.at(ID::MEMID).decode_string();
				for (auto &data : fst_memories[memid]) 
				{
					std::string v = shared->fst->valueOf(data.second);
					set_memory_state(memid, Const(data.first), Const::from_string(v));
				}
			}
		}

		for (auto child : children)
			did_something |= child.second->setInitState();
		return did_something;
	}

	void addAdditionalInputs()
	{
		for (auto cell : module->cells())
		{
			if (cell->type.in(ID($anyseq))) {
				SigSpec sig_y = sigmap(cell->getPort(ID::Y));
				if (sig_y.is_wire()) {
					bool found = false;
					for(auto &item : fst_handles) {
						if (item.second==0) continue; // Ignore signals not found
						if (sig_y == sigmap(item.first)) {
							fst_inputs[sig_y.as_wire()] = item.second;
							found = true;
							break;
						}
					}
					if (!found)
						log_error("Unable to find required '%s' signal in file\n",(scope + "." + RTLIL::unescape_id(sig_y.as_wire()->name)).c_str());
				}
			}
		}
		for (auto child : children)
			child.second->addAdditionalInputs();
	}

	bool setInputs()
	{
		bool did_something = false;
		for(auto &item : fst_inputs) {
			std::string v = shared->fst->valueOf(item.second);
			did_something |= set_state(item.first, Const::from_string(v));
		}

		for (auto child : children)
			did_something |= child.second->setInputs();

		return did_something;
	}

	void setState(dict<int, std::pair<SigBit,bool>> bits, std::string values)
	{
		for(auto bit : bits) {
			if (bit.first >= GetSize(values))
				log_error("Too few input data bits in file.\n");
			switch(values.at(bit.first)) {
				case '0': set_state(bit.second.first, bit.second.second ? State::S1 : State::S0); break;
				case '1': set_state(bit.second.first, bit.second.second ? State::S0 : State::S1); break;
				default: set_state(bit.second.first, State::Sx); break;
			}
		}
	}

	void setMemState(dict<int, std::pair<std::string,int>> bits, std::string values)
	{
		for(auto bit : bits) {
			if (bit.first >= GetSize(values))
				log_error("Too few input data bits in file.\n");
			switch(values.at(bit.first)) {
				case '0': set_memory_state_bit(bit.second.first, bit.second.second, State::S0); break;
				case '1': set_memory_state_bit(bit.second.first, bit.second.second, State::S1); break;
				default: set_memory_state_bit(bit.second.first, bit.second.second, State::Sx); break;
			}
		}
	}

	bool checkSignals()
	{
		bool retVal = false;
		for(auto &item : fst_handles) {
			if (item.second==0) continue; // Ignore signals not found
			Const fst_val = Const::from_string(shared->fst->valueOf(item.second));
			Const sim_val = get_state(item.first);
			if (sim_val.size()!=fst_val.size()) {
				log_warning("Signal '%s.%s' size is different in gold and gate.\n", scope.c_str(), log_id(item.first));
				continue;
			}
			if (shared->sim_mode == SimulationMode::sim) {
				// No checks performed when using stimulus
			} else if (shared->sim_mode == SimulationMode::gate && !fst_val.is_fully_def()) { // FST data contains X
				for(int i=0;i<fst_val.size();i++) {
					if (fst_val[i]!=State::Sx && fst_val[i]!=sim_val[i]) {
						log_warning("Signal '%s.%s' in file %s in simulation %s\n", scope.c_str(), log_id(item.first), log_signal(fst_val), log_signal(sim_val));
						retVal = true;
						break;
					}
				}
			} else if (shared->sim_mode == SimulationMode::gold && !sim_val.is_fully_def()) { // sim data contains X
				for(int i=0;i<sim_val.size();i++) {
					if (sim_val[i]!=State::Sx && fst_val[i]!=sim_val[i]) {
						log_warning("Signal '%s.%s' in file %s in simulation %s\n", scope.c_str(), log_id(item.first), log_signal(fst_val), log_signal(sim_val));
						retVal = true;
						break;
					}
				}
			} else {
				if (fst_val!=sim_val) {
					log_warning("Signal '%s.%s' in file %s in simulation '%s'\n", scope.c_str(), log_id(item.first), log_signal(fst_val), log_signal(sim_val));
					retVal = true;
				}
			}
		}
		for (auto child : children)
			retVal |= child.second->checkSignals();
		return retVal;
	}
};

struct SimWorker : SimShared
{
	SimInstance *top = nullptr;
	pool<IdString> clock, clockn, reset, resetn;
	std::string timescale;
	std::string sim_filename;
	std::string map_filename;
	std::string summary_filename;
	std::string scope;

	~SimWorker()
	{
		outputfiles.clear();
		delete top;
	}

	void register_signals()
	{
		next_output_id = 1;
		top->register_signals(top->shared->next_output_id);
	}

	void register_output_step(int t)
	{
		std::map<int,Const> data;
		top->register_output_step_values(&data);
		output_data.emplace_back(t, data);
	}

	void write_output_files()
	{
		std::map<int, bool> use_signal;
		bool first = ignore_x;
		for(auto& d : output_data)
		{
			if (first) {
				for (auto &data : d.second)
					use_signal[data.first] = !data.second.is_fully_undef();
				first = false;
			} else {
				for (auto &data : d.second)
					use_signal[data.first] = true;
			}
			if (!ignore_x) break;
		}
		for(auto& writer : outputfiles)
			writer->write(use_signal);
		
		if (writeback) {
			pool<Module*> wbmods;
			top->writeback(wbmods);
		}
	}

	void update(bool gclk)
	{
		if (gclk)
			step += 1;

		while (1)
		{
			if (debug)
				log("\n-- ph1 --\n");

			top->update_ph1();

			if (debug)
				log("\n-- ph2 --\n");

			if (!top->update_ph2(gclk))
				break;
		}

		if (debug)
			log("\n-- ph3 --\n");

		top->update_ph3(gclk);
	}

	void initialize_stable_past()
	{

		while (1)
		{
			if (debug)
				log("\n-- ph1 (initialize) --\n");

			top->update_ph1();

			if (debug)
				log("\n-- ph2 (initialize) --\n");

			if (!top->update_ph2(false, true))
				break;
		}

		if (debug)
			log("\n-- ph3 (initialize) --\n");
		top->update_ph3(true);
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
		register_signals();

		if (debug)
			log("\n===== 0 =====\n");
		else if (verbose)
			log("Simulating cycle 0.\n");

		set_inports(reset, State::S1);
		set_inports(resetn, State::S0);

		set_inports(clock, State::Sx);
		set_inports(clockn, State::Sx);

		top->set_initstate_outputs(initstate ? State::S1 : State::S0);

		update(false);

		register_output_step(0);

		for (int cycle = 0; cycle < numcycles; cycle++)
		{
			if (debug)
				log("\n===== %d =====\n", 10*cycle + 5);
			else if (verbose)
				log("Simulating cycle %d.\n", (cycle*2)+1);
			set_inports(clock, State::S0);
			set_inports(clockn, State::S1);

			update(true);
			register_output_step(10*cycle + 5);

			if (cycle == 0)
				top->set_initstate_outputs(State::S0);

			if (debug)
				log("\n===== %d =====\n", 10*cycle + 10);
			else if (verbose)
				log("Simulating cycle %d.\n", (cycle*2)+2);

			set_inports(clock, State::S1);
			set_inports(clockn, State::S0);

			if (cycle+1 == rstlen) {
				set_inports(reset, State::S0);
				set_inports(resetn, State::S1);
			}

			update(true);
			register_output_step(10*cycle + 10);
		}

		register_output_step(10*numcycles + 2);

		write_output_files();
	}

	void run_cosim_fst(Module *topmod, int numcycles)
	{
		log_assert(top == nullptr);
		fst = new FstData(sim_filename);

		if (scope.empty())
			log_error("Scope must be defined for co-simulation.\n");

		top = new SimInstance(this, scope, topmod);
		register_signals();

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

		SigMap sigmap(topmod);

		for (auto wire : topmod->wires()) {
			if (wire->port_input) {
				fstHandle id = fst->getHandle(scope + "." + RTLIL::unescape_id(wire->name));
				if (id==0)
					log_error("Unable to find required '%s' signal in file\n",(scope + "." + RTLIL::unescape_id(wire->name)).c_str());
				top->fst_inputs[wire] = id;
			}
		}

		top->addAdditionalInputs();

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

		bool initial = true;
		int cycle = 0;
		log("Co-simulation from %lu%s to %lu%s", (unsigned long)startCount, fst->getTimescaleString(), (unsigned long)stopCount, fst->getTimescaleString());
		if (cycles_set) 
			log(" for %d clock cycle(s)",numcycles);
		log("\n");
		bool all_samples = fst_clock.empty();

		try {
			fst->reconstructAllAtTimes(fst_clock, startCount, stopCount, [&](uint64_t time) {
				if (verbose)
					log("Co-simulating %s %d [%lu%s].\n", (all_samples ? "sample" : "cycle"), cycle, (unsigned long)time, fst->getTimescaleString());
				bool did_something = top->setInputs();

				if (initial) {
					did_something |= top->setInitState();
					initialize_stable_past();
					initial = false;
				}
				if (did_something)
					update(true);
				register_output_step(time);

				bool status = top->checkSignals();
				if (status)
					log_error("Signal difference\n");
				cycle++;

				// Limit to number of cycles if provided
				if (cycles_set && cycle > numcycles *2)
					throw fst_end_of_data_exception();
				if (time==stopCount)
					throw fst_end_of_data_exception();
			});
		} catch(fst_end_of_data_exception) {
			// end of data detected
		}

		write_output_files();
		delete fst;
	}

	std::string cell_name(std::string const & name)
	{
		size_t pos = name.find_last_of("[");
		if (pos!=std::string::npos)
			return name.substr(0, pos);
		return name;
	}

	int mem_cell_addr(std::string const & name)
	{
		size_t pos = name.find_last_of("[");
		return atoi(name.substr(pos+1).c_str());
	}

	void run_cosim_aiger_witness(Module *topmod)
	{
		log_assert(top == nullptr);
		if (!multiclock && (clock.size()+clockn.size())==0)
			log_error("Clock signal must be specified.\n");
		if (multiclock && (clock.size()+clockn.size())>0)
			log_error("For multiclock witness there should be no clock signal.\n");

		top = new SimInstance(this, scope, topmod);
		register_signals();

		std::ifstream mf(map_filename);
		std::string type, symbol;
		int variable, index;
		dict<int, std::pair<SigBit,bool>> inputs, inits, latches;
		dict<int, std::pair<std::string,int>> mem_inits, mem_latches;
		if (mf.fail())
			log_cmd_error("Not able to read AIGER witness map file.\n");
		while (mf >> type >> variable >> index >> symbol) {
			RTLIL::IdString escaped_s = RTLIL::escape_id(symbol);
			Wire *w = topmod->wire(escaped_s);
			if (!w) {
				escaped_s = RTLIL::escape_id(cell_name(symbol));
				Cell *c = topmod->cell(escaped_s);
				if (!c)
					log_warning("Wire/cell %s not present in module %s\n",symbol.c_str(),log_id(topmod));

				if (c->is_mem_cell()) {
					std::string memid = c->parameters.at(ID::MEMID).decode_string();
					auto &state = top->mem_database[memid];

					int offset = (mem_cell_addr(symbol) - state.mem->start_offset) * state.mem->width + index;
					if (type == "init")
						mem_inits[variable] = { memid, offset };
					else if (type == "latch")
						mem_latches[variable] = { memid, offset };
					else
						log_error("Map file addressing cell %s as type %s\n", symbol.c_str(), type.c_str());
				} else {
					log_error("Cell %s in map file is not memory cell\n", symbol.c_str());
				}
			} else {
				if (index < w->start_offset || index > w->start_offset + w->width)
					log_error("Index %d for wire %s is out of range\n", index, log_signal(w));
				if (type == "input") {
					inputs[variable] = {SigBit(w,index-w->start_offset), false};
				} else if (type == "init") {
					inits[variable] = {SigBit(w,index-w->start_offset), false};
				} else if (type == "latch") {
					latches[variable] = {SigBit(w,index-w->start_offset), false};
				} else if (type == "invlatch") {
					latches[variable] = {SigBit(w,index-w->start_offset), true};
				}
			}
		}

		std::ifstream f;
		f.open(sim_filename.c_str());
		if (f.fail() || GetSize(sim_filename) == 0)
			log_error("Can not open file `%s`\n", sim_filename.c_str());

		int state = 0;
		std::string status;
		int cycle = 0;

		while (!f.eof())
		{
			std::string line;
			std::getline(f, line);
			if (line.size()==0 || line[0]=='#' || line[0]=='c' || line[0]=='f' || line[0]=='u') continue;
			if (line[0]=='.') break;
			if (state==0 && line.size()!=1) {
				// old format detected, latch data
				state = 2;
			}
			if (state==1 && line[0]!='b' && line[0]!='j') {
				// was old format but with 1 bit latch
				top->setState(latches, status);
				state = 3;
			}

			switch(state)
			{
				case 0:
					status = line;
					state = 1;
					break;
				case 1:
					state = 2;
					break;
				case 2:
					top->setState(latches, line);
					top->setMemState(mem_latches, line);
					state = 3;
					break;
				default:
					if (verbose)
						log("Simulating cycle %d.\n", cycle);
					top->setState(inputs, line);
					if (cycle) {
						set_inports(clock, State::S1);
						set_inports(clockn, State::S0);
					} else {
						top->setState(inits, line);
						top->setMemState(mem_inits, line);
						set_inports(clock, State::S0);
						set_inports(clockn, State::S1);
					}
					update(true);
					register_output_step(10*cycle);
					if (!multiclock && cycle) {
						set_inports(clock, State::S0);
						set_inports(clockn, State::S1);
						update(true);
						register_output_step(10*cycle + 5);
					}
					cycle++;
					break;
			}
		}
		register_output_step(10*cycle);
		write_output_files();
	}

	std::vector<std::string> split(std::string text, const char *delim)
	{
		std::vector<std::string> list;
		char *p = strdup(text.c_str());
		char *t = strtok(p, delim);
		while (t != NULL) {
			list.push_back(t);
			t = strtok(NULL, delim);
		}
		free(p);
		return list;
	}

	std::string signal_name(std::string const & name)
	{
		size_t pos = name.find_first_of("@");
		if (pos==std::string::npos) {
			pos = name.find_first_of("#");
			if (pos==std::string::npos)
				log_error("Line does not contain proper signal name `%s`\n", name.c_str());
		}
		return name.substr(0, pos);
	}

	void run_cosim_btor2_witness(Module *topmod)
	{
		log_assert(top == nullptr);
		if (!multiclock && (clock.size()+clockn.size())==0)
			log_error("Clock signal must be specified.\n");
		if (multiclock && (clock.size()+clockn.size())>0)
			log_error("For multiclock witness there should be no clock signal.\n");
		std::ifstream f;
		f.open(sim_filename.c_str());
		if (f.fail() || GetSize(sim_filename) == 0)
			log_error("Can not open file `%s`\n", sim_filename.c_str());

		int state = 0;
		int cycle = 0;
		top = new SimInstance(this, scope, topmod);
		register_signals();
		int prev_cycle = 0;
		int curr_cycle = 0;
		std::vector<std::string> parts;
		size_t len = 0;
		while (!f.eof())
		{
			std::string line;
			std::getline(f, line);
			if (line.size()==0) continue;

			if (line[0]=='#' || line[0]=='@' || line[0]=='.') { 
				if (line[0]!='.')
					curr_cycle = atoi(line.c_str()+1); 
				else
					curr_cycle = -1; // force detect change

				if (curr_cycle != prev_cycle) {
					if (verbose)
						log("Simulating cycle %d.\n", cycle);
					set_inports(clock, State::S1);
					set_inports(clockn, State::S0);
					update(true);
					register_output_step(10*cycle+0);
					if (!multiclock) {
						set_inports(clock, State::S0);
						set_inports(clockn, State::S1);
						update(true);
						register_output_step(10*cycle+5);
					}
					cycle++;
					prev_cycle = curr_cycle;
				}
				if (line[0]=='.') break;
				continue;
			}

			switch(state)
			{
				case 0:
					if (line=="sat")
						state = 1;
					break;
				case 1:
					if (line[0]=='b' || line[0]=='j')
						state = 2;
					else
						log_error("Line does not contain property.\n");
					break;
				default: // set state or inputs
					parts = split(line, " ");
					len = parts.size();
					if (len<3 || len>4)
						log_error("Invalid set state line content.\n");

					RTLIL::IdString escaped_s = RTLIL::escape_id(signal_name(parts[len-1]));
					if (len==3) {
						Wire *w = topmod->wire(escaped_s);
						if (!w) {
							Cell *c = topmod->cell(escaped_s);
							if (!c)
								log_warning("Wire/cell %s not present in module %s\n",log_id(escaped_s),log_id(topmod));
							else if (c->type.in(ID($anyconst), ID($anyseq))) {
								SigSpec sig_y= c->getPort(ID::Y);
								if ((int)parts[1].size() != GetSize(sig_y))
									log_error("Size of wire %s is different than provided data.\n", log_signal(sig_y));
								top->set_state(sig_y, Const::from_string(parts[1]));
							}
						} else {
							if ((int)parts[1].size() != w->width)
								log_error("Size of wire %s is different than provided data.\n", log_signal(w));
							top->set_state(w, Const::from_string(parts[1]));
						}
					} else {
						Cell *c = topmod->cell(escaped_s);
						if (!c)
							log_error("Cell %s not present in module %s\n",log_id(escaped_s),log_id(topmod));
						if (!c->is_mem_cell())
							log_error("Cell %s is not memory cell in module %s\n",log_id(escaped_s),log_id(topmod));
						
						Const addr = Const::from_string(parts[1].substr(1,parts[1].size()-2));
						Const data = Const::from_string(parts[2]);
						top->set_memory_state(c->parameters.at(ID::MEMID).decode_string(), addr, data);
					}
					break;
			}
		}
		register_output_step(10*cycle);
		write_output_files();
	}

	struct FoundYWPath
	{
		SimInstance *instance;
		Wire *wire;
		IdString memid;
		int addr;
	};

	struct YwHierarchy {
		dict<IdPath, FoundYWPath> paths;
	};

	YwHierarchy prepare_yw_hierarchy(const ReadWitness &yw)
	{
		YwHierarchy hierarchy;
		pool<IdPath> paths;
		dict<IdPath, pool<IdString>> mem_paths;

		for (auto &signal : yw.signals)
			paths.insert(signal.path);

		for (auto &clock : yw.clocks)
			paths.insert(clock.path);

		for (auto &path : paths)
			if (path.has_address())
				mem_paths[path.prefix()].insert(path.back());

		witness_hierarchy(top->module, top, [&](IdPath const &path, WitnessHierarchyItem item, SimInstance *instance) {
			if (item.cell != nullptr)
				return instance->children.at(item.cell);
			if (item.wire != nullptr) {
				if (paths.count(path)) {
					if (debug)
						log("witness hierarchy: found wire %s\n", path.str().c_str());
					bool inserted = hierarchy.paths.emplace(path, {instance, item.wire, {}, INT_MIN}).second;
					if (!inserted)
						log_warning("Yosys witness path `%s` is ambiguous in this design\n", path.str().c_str());
				}
			} else if (item.mem) {
				auto it = mem_paths.find(path);
				if (it != mem_paths.end()) {
					if (debug)
						log("witness hierarchy: found mem %s\n", path.str().c_str());
					IdPath word_path = path;
					word_path.emplace_back();
					for (auto addr_part : it->second) {
						word_path.back() = addr_part;
						int addr;
						word_path.get_address(addr);
						if (addr < item.mem->start_offset || (addr - item.mem->start_offset) >= item.mem->size)
							continue;
						bool inserted = hierarchy.paths.emplace(word_path, {instance, nullptr, item.mem->memid, addr}).second;
						if (!inserted)
							log_warning("Yosys witness path `%s` is ambiguous in this design\n", path.str().c_str());
					}
				}
			}
			return instance;
		});

		for (auto &path : paths)
			if (!hierarchy.paths.count(path))
				log_warning("Yosys witness path `%s` was not found in this design, ignoring\n", path.str().c_str());

		dict<IdPath, dict<int, bool>> clock_inputs;

		for (auto &clock : yw.clocks) {
			if (clock.is_negedge == clock.is_posedge)
				continue;
			clock_inputs[clock.path].emplace(clock.offset, clock.is_posedge);
		}
		for (auto &signal : yw.signals) {
			auto it = clock_inputs.find(signal.path);
			if (it == clock_inputs.end())
				continue;

			for (auto &clock_input : it->second) {
				int offset = clock_input.first;
				if (offset >= signal.offset && (offset - signal.offset) < signal.width) {
					int clock_bits_offset = signal.bits_offset + (offset - signal.offset);

					State expected = clock_input.second ? State::S0 : State::S1;

					for (int t = 0; t < GetSize(yw.steps); t++) {
						if (yw.get_bits(t, clock_bits_offset, 1) != expected)
							log_warning("Yosys witness trace has an unexpected value for the clock input `%s` in step %d.\n", signal.path.str().c_str(), t);
					}
				}
			}
		}
		// TODO add checks and warnings for witness signals (toplevel inputs, $any*) not present in the witness file

		return hierarchy;
	}

	void set_yw_state(const ReadWitness &yw, const YwHierarchy &hierarchy, int t)
	{
		log_assert(t >= 0 && t < GetSize(yw.steps));

		for (auto &signal : yw.signals) {
			if (signal.init_only && t >= 1)
				continue;
			auto found_path_it = hierarchy.paths.find(signal.path);
			if (found_path_it == hierarchy.paths.end())
				continue;
			auto &found_path = found_path_it->second;

			Const value = yw.get_bits(t, signal.bits_offset, signal.width);

			if (debug)
				log("yw: set %s to %s\n", signal.path.str().c_str(), log_const(value));

			if (found_path.wire != nullptr) {
				found_path.instance->set_state_parent_drivers(
						SigChunk(found_path.wire, signal.offset, signal.width),
						value);
			} else if (!found_path.memid.empty()) {
				if (t >= 1)
					found_path.instance->register_memory_addr(found_path.memid, found_path.addr);
				else
					found_path.instance->trace_mem_init_database.emplace(make_pair(found_path.memid, found_path.addr), value);
				found_path.instance->set_memory_state(
						found_path.memid, found_path.addr,
						value);
			}
		}
	}

	void set_yw_clocks(const ReadWitness &yw, const YwHierarchy &hierarchy, bool active_edge)
	{
		for (auto &clock : yw.clocks) {
			if (clock.is_negedge == clock.is_posedge)
				continue;
			auto found_path_it = hierarchy.paths.find(clock.path);
			if (found_path_it == hierarchy.paths.end())
				continue;
			auto &found_path = found_path_it->second;

			if (found_path.wire != nullptr) {
				found_path.instance->set_state(
						SigChunk(found_path.wire, clock.offset, 1),
						active_edge == clock.is_posedge ? State::S1 : State::S0);
			}
		}
	}

	void run_cosim_yw_witness(Module *topmod, int append)
	{
		if (!clock.empty())
			log_cmd_error("The -clock option is not required nor supported when reading a Yosys witness file.\n");
		if (!reset.empty())
			log_cmd_error("The -reset option is not required nor supported when reading a Yosys witness file.\n");
		if (multiclock)
			log_warning("The -multiclock option is not required and ignored when reading a Yosys witness file.\n");

		ReadWitness yw(sim_filename);

		top = new SimInstance(this, scope, topmod);
		register_signals();

		YwHierarchy hierarchy = prepare_yw_hierarchy(yw);

		if (yw.steps.empty()) {
			log_warning("Yosys witness file `%s` contains no time steps\n", yw.filename.c_str());
		} else {
			top->set_initstate_outputs(initstate ? State::S1 : State::S0);
			set_yw_state(yw, hierarchy, 0);
			set_yw_clocks(yw, hierarchy, true);
			initialize_stable_past();
			register_output_step(0);

			if (!yw.clocks.empty()) {
				if (debug)
					log("Simulating non-active clock edge.\n");
				set_yw_clocks(yw, hierarchy, false);
				update(false);
				register_output_step(5);
			}
			top->set_initstate_outputs(State::S0);
		}

		for (int cycle = 1; cycle < GetSize(yw.steps) + append; cycle++)
		{
			if (verbose)
				log("Simulating cycle %d.\n", cycle);
			if (cycle < GetSize(yw.steps))
				set_yw_state(yw, hierarchy, cycle);
			set_yw_clocks(yw, hierarchy, true);
			update(true);
			register_output_step(10 * cycle);

			if (!yw.clocks.empty()) {
				if (debug)
					log("Simulating non-active clock edge.\n");
				set_yw_clocks(yw, hierarchy, false);
				update(false);
				register_output_step(5 + 10 * cycle);
			}
		}

		register_output_step(10 * (GetSize(yw.steps) + append));
		write_output_files();
	}

	void write_summary()
	{
		if (summary_filename.empty())
			return;

		PrettyJson json;
		if (!json.write_to_file(summary_filename))
			log_error("Can't open file `%s' for writing: %s\n", summary_filename.c_str(), strerror(errno));

		json.begin_object();
		json.entry("version", "Yosys sim summary");
		json.entry("generator", yosys_version_str);
		json.entry("steps", step);
		json.entry("top", log_id(top->module->name));
		json.name("assertions");
		json.begin_array();
		for (auto &assertion : triggered_assertions) {
			json.begin_object();
			json.entry("step", assertion.step);
			json.entry("type", log_id(assertion.cell->type));
			json.entry("path", assertion.instance->witness_full_path(assertion.cell));
			auto src = assertion.cell->get_string_attribute(ID::src);
			if (!src.empty()) {
				json.entry("src", src);
			}
			json.end_object();
		}
		json.end_array();
		json.name("display_output");
		json.begin_array();
		for (auto &output : display_output) {
			json.begin_object();
			json.entry("step", output.step);
			json.entry("path", output.instance->witness_full_path(output.cell));
			auto src = output.cell->get_string_attribute(ID::src);
			if (!src.empty()) {
				json.entry("src", src);
			}
			json.entry("output", output.output);
			json.end_object();
		}
		json.end_array();
		json.end_object();
	}

	std::string define_signal(Wire *wire)
	{
		std::stringstream f;

		if (wire->width==1)
			f << stringf("%s", RTLIL::unescape_id(wire->name).c_str());
		else
			if (wire->upto)
				f << stringf("[%d:%d] %s", wire->start_offset, wire->width - 1 + wire->start_offset, RTLIL::unescape_id(wire->name).c_str());
			else
				f << stringf("[%d:%d] %s", wire->width - 1 + wire->start_offset, wire->start_offset, RTLIL::unescape_id(wire->name).c_str());
		return f.str();
	}

	std::string signal_list(std::map<Wire*,fstHandle> &signals)
	{
		std::stringstream f;
		for(auto item=signals.begin();item!=signals.end();item++)
			f << stringf("%c%s", (item==signals.begin() ? ' ' : ','), RTLIL::unescape_id(item->first->name).c_str());
		return f.str();
	}

	void generate_tb(Module *topmod, std::string tb_filename, int numcycles)
	{
		fst = new FstData(sim_filename);

		if (scope.empty())
			log_error("Scope must be defined for co-simulation.\n");

		if ((clock.size()+clockn.size())==0)
			log_error("Clock signal must be specified.\n");

		std::vector<fstHandle> fst_clock;
		std::map<Wire*,fstHandle> clocks;

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
			clocks[w] = id;
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
			clocks[w] = id;
		}

		SigMap sigmap(topmod);
		std::map<Wire*,fstHandle> inputs;
		std::map<Wire*,fstHandle> outputs;

		for (auto wire : topmod->wires()) {
			fstHandle id = fst->getHandle(scope + "." + RTLIL::unescape_id(wire->name));
			if (id==0 && (wire->port_input || wire->port_output))
				log_error("Unable to find required '%s' signal in file\n",(scope + "." + RTLIL::unescape_id(wire->name)).c_str());
			if (wire->port_input)
				if (clocks.find(wire)==clocks.end())
					inputs[wire] = id;
			if (wire->port_output)
				outputs[wire] = id;
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

		int cycle = 0;
		log("Generate testbench data from %lu%s to %lu%s", (unsigned long)startCount, fst->getTimescaleString(), (unsigned long)stopCount, fst->getTimescaleString());
		if (cycles_set) 
			log(" for %d clock cycle(s)",numcycles);
		log("\n");

		std::stringstream f;
		f << stringf("`timescale 1%s/1%s\n", fst->getTimescaleString(),fst->getTimescaleString());
		f << stringf("module %s();\n",tb_filename.c_str());
		int clk_len = 0;
		int inputs_len = 0;
		int outputs_len = 0;
		for(auto &item : clocks) {
			clk_len += item.first->width;
			f << "\treg " << define_signal(item.first) << ";\n";
		}
		for(auto &item : inputs) {
			inputs_len += item.first->width;
			f << "\treg " << define_signal(item.first) << ";\n";
		}
		for(auto &item : outputs) {
			outputs_len += item.first->width;
			f << "\twire " << define_signal(item.first) << ";\n";
		}
		int data_len = clk_len + inputs_len + outputs_len + 32;
		f << "\n";
		f << stringf("\t%s uut(",RTLIL::unescape_id(topmod->name).c_str());
		for(auto item=clocks.begin();item!=clocks.end();item++)
			f << stringf("%c.%s(%s)", (item==clocks.begin() ? ' ' : ','), RTLIL::unescape_id(item->first->name).c_str(), RTLIL::unescape_id(item->first->name).c_str());
		for(auto &item : inputs)
			f << stringf(",.%s(%s)", RTLIL::unescape_id(item.first->name).c_str(), RTLIL::unescape_id(item.first->name).c_str());
		for(auto &item : outputs)
			f << stringf(",.%s(%s)", RTLIL::unescape_id(item.first->name).c_str(), RTLIL::unescape_id(item.first->name).c_str());
		f << ");\n";
		f << "\n";
		f << "\tinteger i;\n";
		uint64_t prev_time = startCount;
		log("Writing data to `%s`\n", (tb_filename+".txt").c_str());
		std::ofstream data_file(tb_filename+".txt");
		std::stringstream initstate;
		try {
			fst->reconstructAllAtTimes(fst_clock, startCount, stopCount, [&](uint64_t time) {
				for(auto &item : clocks)
					data_file << stringf("%s",fst->valueOf(item.second).c_str());
				for(auto &item : inputs)
					data_file << stringf("%s",fst->valueOf(item.second).c_str());
				for(auto &item : outputs)
					data_file << stringf("%s",fst->valueOf(item.second).c_str());
				data_file << stringf("%s\n",Const(time-prev_time).as_string().c_str());

				if (time==startCount) {
					// initial state
					for(auto var : fst->getVars()) {
						if (var.is_reg && !Const::from_string(fst->valueOf(var.id).c_str()).is_fully_undef()) {
							if (var.scope == scope) {
								initstate << stringf("\t\tuut.%s = %d'b%s;\n", var.name.c_str(), var.width, fst->valueOf(var.id).c_str());
							} else if (var.scope.find(scope+".")==0) {
								initstate << stringf("\t\tuut.%s.%s = %d'b%s;\n",var.scope.substr(scope.size()+1).c_str(), var.name.c_str(), var.width, fst->valueOf(var.id).c_str());
							}
						}
					}
				}
				cycle++;
				prev_time = time;

				// Limit to number of cycles if provided
				if (cycles_set && cycle > numcycles *2)
					throw fst_end_of_data_exception();
				if (time==stopCount)
					throw fst_end_of_data_exception();
			});
		} catch(fst_end_of_data_exception) {
			// end of data detected
		}

		f << stringf("\treg [0:%d] data [0:%d];\n", data_len-1, cycle-1);
		f << "\tinitial begin;\n";
		f << stringf("\t\t$dumpfile(\"%s\");\n",tb_filename.c_str());
		f << stringf("\t\t$dumpvars(0,%s);\n",tb_filename.c_str());
		f << initstate.str();
		f << stringf("\t\t$readmemb(\"%s.txt\", data);\n",tb_filename.c_str());

		f << stringf("\t\t#(data[0][%d:%d]);\n", data_len-32, data_len-1);	
		f << stringf("\t\t{%s } = data[0][%d:%d];\n", signal_list(clocks).c_str(), 0, clk_len-1);		
		f << stringf("\t\t{%s } <= data[0][%d:%d];\n", signal_list(inputs).c_str(), clk_len, clk_len+inputs_len-1);

		f << stringf("\t\tfor (i = 1; i < %d; i++) begin\n",cycle);

		f << stringf("\t\t\t#(data[i][%d:%d]);\n", data_len-32, data_len-1);	
		f << stringf("\t\t\t{%s } = data[i][%d:%d];\n", signal_list(clocks).c_str(), 0, clk_len-1);		
		f << stringf("\t\t\t{%s } <= data[i][%d:%d];\n", signal_list(inputs).c_str(), clk_len, clk_len+inputs_len-1);
		
		f << stringf("\t\t\tif ({%s } != data[i-1][%d:%d]) begin\n", signal_list(outputs).c_str(), clk_len+inputs_len, clk_len+inputs_len+outputs_len-1);
		f << "\t\t\t\t$error(\"Signal difference detected\\n\");\n";
		f << "\t\t\tend\n";
		
		f << "\t\tend\n";
		
		f << "\t\t$finish;\n";
		f << "\tend\n";
		f << "endmodule\n";

		log("Writing testbench to `%s`\n", (tb_filename+".v").c_str());
		std::ofstream tb_file(tb_filename+".v");
		tb_file << f.str();

		delete fst;
	}
};

struct VCDWriter : public OutputWriter
{
	VCDWriter(SimWorker *worker, std::string filename) : OutputWriter(worker) {
		vcdfile.open(filename.c_str());
	}

	void write(std::map<int, bool> &use_signal) override
	{
		if (!vcdfile.is_open()) return;
		vcdfile << stringf("$version %s $end\n", worker->date ? yosys_version_str : "Yosys");

		if (worker->date) {
			std::time_t t = std::time(nullptr);
			char mbstr[255];
			if (std::strftime(mbstr, sizeof(mbstr), "%c", std::localtime(&t))) {
				vcdfile << stringf("$date ") << mbstr << stringf(" $end\n");
			}
		}

		if (!worker->timescale.empty())
			vcdfile << stringf("$timescale %s $end\n", worker->timescale.c_str());

		worker->top->write_output_header(
			[this](IdString name) { vcdfile << stringf("$scope module %s $end\n", log_id(name)); },
			[this]() { vcdfile << stringf("$upscope $end\n");},
			[this,use_signal](const char *name, int size, Wire *, int id, bool is_reg) {
				if (use_signal.at(id)) {
					// Works around gtkwave trying to parse everything past the last [ in a signal
					// name. While the emitted range doesn't necessarily match the wire's range,
					// this is consistent with the range gtkwave makes up if it doesn't find a
					// range
					std::string range = strchr(name, '[') ? stringf("[%d:0]", size - 1) : std::string();
					vcdfile << stringf("$var %s %d n%d %s%s%s $end\n", is_reg ? "reg" : "wire", size, id, name[0] == '$' ? "\\" : "", name, range.c_str());

				}
			}
		);

		vcdfile << stringf("$enddefinitions $end\n");

		for(auto& d : worker->output_data)
		{
			vcdfile << stringf("#%d\n", d.first);
			for (auto &data : d.second)
			{
				if (!use_signal.at(data.first)) continue;
				Const value = data.second;
				vcdfile << "b";
				for (int i = GetSize(value)-1; i >= 0; i--) {
					switch (value[i]) {
						case State::S0: vcdfile << "0"; break;
						case State::S1: vcdfile << "1"; break;
						case State::Sx: vcdfile << "x"; break;
						default: vcdfile << "z";
					}
				}
				vcdfile << stringf(" n%d\n", data.first);
			}
		}
	}

	std::ofstream vcdfile;
};

struct FSTWriter : public OutputWriter
{
	FSTWriter(SimWorker *worker, std::string filename) : OutputWriter(worker) {
		fstfile = (struct fstContext *)fstWriterCreate(filename.c_str(),1);
	}

	virtual ~FSTWriter()
	{
		fstWriterClose(fstfile);
	}

	void write(std::map<int, bool> &use_signal) override
	{
		if (!fstfile) return;
		std::time_t t = std::time(nullptr);
		fstWriterSetVersion(fstfile, worker->date ? yosys_version_str : "Yosys");
		if (worker->date)
			fstWriterSetDate(fstfile, asctime(std::localtime(&t)));
		else
			fstWriterSetDate(fstfile, "");
		if (!worker->timescale.empty())
			fstWriterSetTimescaleFromString(fstfile, worker->timescale.c_str());

		fstWriterSetPackType(fstfile, FST_WR_PT_FASTLZ);
		fstWriterSetRepackOnClose(fstfile, 1);
	   
	   	worker->top->write_output_header(
			[this](IdString name) { fstWriterSetScope(fstfile, FST_ST_VCD_MODULE, stringf("%s",log_id(name)).c_str(), nullptr); },
			[this]() { fstWriterSetUpscope(fstfile); },
			[this,use_signal](const char *name, int size, Wire *, int id, bool is_reg) {
				if (!use_signal.at(id)) return;
				fstHandle fst_id = fstWriterCreateVar(fstfile, is_reg ? FST_VT_VCD_REG : FST_VT_VCD_WIRE, FST_VD_IMPLICIT, size,
												name, 0);
				mapping.emplace(id, fst_id);
			}
		);

		for(auto& d : worker->output_data)
		{
			fstWriterEmitTimeChange(fstfile, d.first);
			for (auto &data : d.second)
			{
				if (!use_signal.at(data.first)) continue;
				Const value = data.second;
				std::stringstream ss;
				for (int i = GetSize(value)-1; i >= 0; i--) {
					switch (value[i]) {
						case State::S0: ss << "0"; break;
						case State::S1: ss << "1"; break;
						case State::Sx: ss << "x"; break;
						default: ss << "z";
					}
				}
				fstWriterEmitValueChange(fstfile, mapping[data.first], ss.str().c_str());
			}
		}
	}

	struct fstContext *fstfile = nullptr;
	std::map<int,fstHandle> mapping;
};

struct AIWWriter : public OutputWriter
{
	AIWWriter(SimWorker *worker, std::string filename) : OutputWriter(worker) {
		aiwfile.open(filename.c_str());
	}

	virtual ~AIWWriter()
	{
		aiwfile << '.' << '\n';
	}

	void write(std::map<int, bool> &) override
	{
		if (!aiwfile.is_open()) return;
		if (worker->map_filename.empty())
			log_cmd_error("For AIGER witness file map parameter is mandatory.\n");

		std::ifstream mf(worker->map_filename);
		std::string type, symbol;
		int variable, index;
		int max_input = 0;
		if (mf.fail())
			log_cmd_error("Not able to read AIGER witness map file.\n");
		while (mf >> type >> variable >> index >> symbol) {
			RTLIL::IdString escaped_s = RTLIL::escape_id(symbol);
			Wire *w = worker->top->module->wire(escaped_s);
			if (!w)
				log_error("Wire %s not present in module %s\n",log_id(escaped_s),log_id(worker->top->module));
			if (index < w->start_offset || index > w->start_offset + w->width)
				log_error("Index %d for wire %s is out of range\n", index, log_signal(w));
			if (type == "input") {
				aiw_inputs[variable] = SigBit(w,index-w->start_offset);
				if (worker->clock.count(escaped_s)) {
					clocks[variable] = true;
				}
				if (worker->clockn.count(escaped_s)) {
					clocks[variable] = false;
				}
				max_input = max(max_input,variable);
			} else if (type == "init") {
				aiw_inits[variable] = SigBit(w,index-w->start_offset);
				max_input = max(max_input,variable);
			} else if (type == "latch") {
				aiw_latches[variable] = {SigBit(w,index-w->start_offset), false};
			} else if (type == "invlatch") {
				aiw_latches[variable] = {SigBit(w,index-w->start_offset), true};
			}
		}

		worker->top->write_output_header(
			[](IdString) {},
			[]() {},
			[this](const char */*name*/, int /*size*/, Wire *wire, int id, bool) { if (wire != nullptr) mapping[wire] = id; }
		);

		std::map<int, Yosys::RTLIL::Const> current;
		bool first = true;
		for (auto iter = worker->output_data.begin(); iter != std::prev(worker->output_data.end()); ++iter)
		{
			auto& d = *iter;
			for (auto &data : d.second)
			{
				current[data.first] = data.second;
			}
			if (first) {
				for (int i = 0;; i++)
				{
					if (aiw_latches.count(i)) {
						aiwfile << '0';
						continue;
					}
					aiwfile << '\n';
					break;
				}
				first = false;
			}

			bool skip = false;
			for (auto it : clocks)
			{
				auto val = it.second ? State::S1 : State::S0;
				SigBit bit = aiw_inputs.at(it.first);
				auto v = current[mapping[bit.wire]].bits.at(bit.offset);
				if (v == val)
					skip = true;
			}
			if (skip)
				continue;
			for (int i = 0; i <= max_input; i++)
			{
				if (aiw_inputs.count(i)) {
					SigBit bit = aiw_inputs.at(i);
					auto v = current[mapping[bit.wire]].bits.at(bit.offset);
					if (v == State::S1)
						aiwfile << '1';
					else
						aiwfile << '0';
					continue;
				}
				if (aiw_inits.count(i)) {
					SigBit bit = aiw_inits.at(i);
					auto v = current[mapping[bit.wire]].bits.at(bit.offset);
					if (v == State::S1)
						aiwfile << '1';
					else
						aiwfile << '0';
					continue;
				}
				aiwfile << '0';
			}
			aiwfile << '\n';
		} 
	}

	std::ofstream aiwfile;
	dict<int, std::pair<SigBit, bool>> aiw_latches;
	dict<int, SigBit> aiw_inputs, aiw_inits;
	dict<int, bool> clocks;
	std::map<Wire*,int> mapping;
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
		log("    -aiw <filename>\n");
		log("        write the simulation results to an AIGER witness file\n");
		log("        (requires a *.aim file via -map)\n");
		log("\n");
		log("    -hdlname\n");
		log("        use the hdlname attribute when writing simulation results\n");
		log("        (preserves hierarchy in a flattened design)\n");
		log("\n");
		log("    -x\n");
		log("        ignore constant x outputs in simulation file.\n");
		log("\n");
		log("    -date\n");
		log("        include date and full version info in output.\n");
		log("\n");
		log("    -clock <portname>\n");
		log("        name of top-level clock input\n");
		log("\n");
		log("    -clockn <portname>\n");
		log("        name of top-level clock input (inverse polarity)\n");
		log("\n");
		log("    -multiclock\n");
		log("        mark that witness file is multiclock.\n");
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
		log("        number of clock cycles to simulate (default: 20)\n");
		log("\n");
		log("    -noinitstate\n");
		log("        do not activate $initstate cells during the first cycle\n");
		log("\n");
		log("    -a\n");
		log("        use all nets in VCD/FST operations, not just those with public names\n");
		log("\n");
		log("    -w\n");
		log("        writeback mode: use final simulation state as new init state\n");
		log("\n");
		log("    -r <filename>\n");
		log("        read simulation or formal results file\n");
		log("            File formats supported: FST, VCD, AIW, WIT and .yw\n");
		log("            VCD support requires vcd2fst external tool to be present\n");
		log("\n");
		log("    -append <integer>\n");
		log("        number of extra clock cycles to simulate for a Yosys witness input\n");
		log("\n");
		log("    -summary <filename>\n");
		log("        write a JSON summary to the given file\n");
		log("\n");
		log("    -map <filename>\n");
		log("        read file with port and latch symbols, needed for AIGER witness input\n");
		log("\n");
		log("    -scope <name>\n");
		log("        scope of simulation top model\n");
		log("\n");
		log("    -at <time>\n");
		log("        sets start and stop time\n");
		log("\n");
		log("    -start <time>\n");
		log("        start co-simulation in arbitary time (default 0)\n");
		log("\n");
		log("    -stop <time>\n");
		log("        stop co-simulation in arbitary time (default END)\n");
		log("\n");
		log("    -sim\n");
		log("        simulation with stimulus from FST (default)\n");
		log("\n");
		log("    -sim-cmp\n");
		log("        co-simulation expect exact match\n");
		log("\n");
		log("    -sim-gold\n");
		log("        co-simulation, x in simulation can match any value in FST\n");
		log("\n");
		log("    -sim-gate\n");
		log("        co-simulation, x in FST can match any value in simulation\n");
		log("\n");
		log("    -assert\n");
		log("        fail the simulation command if, in the course of simulating,\n");
		log("        any of the asserts in the design fail\n");
		log("\n");
		log("    -q\n");
		log("        disable per-cycle/sample log message\n");
		log("\n");
		log("    -d\n");
		log("        enable debug output\n");
		log("\n");
	}


	static std::string file_base_name(std::string const & path)
	{
		return path.substr(path.find_last_of("/\\") + 1);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		SimWorker worker;
		int numcycles = 20;
		int append = 0;
		bool start_set = false, stop_set = false, at_set = false;

		log_header(design, "Executing SIM pass (simulate the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-vcd" && argidx+1 < args.size()) {
				std::string vcd_filename = args[++argidx];
				rewrite_filename(vcd_filename);
				worker.outputfiles.emplace_back(std::unique_ptr<VCDWriter>(new VCDWriter(&worker, vcd_filename.c_str())));
				continue;
			}
			if (args[argidx] == "-fst" && argidx+1 < args.size()) {
				std::string fst_filename = args[++argidx];
				rewrite_filename(fst_filename);
				worker.outputfiles.emplace_back(std::unique_ptr<FSTWriter>(new FSTWriter(&worker, fst_filename.c_str())));
				continue;
			}
			if (args[argidx] == "-aiw" && argidx+1 < args.size()) {
				std::string aiw_filename = args[++argidx];
				rewrite_filename(aiw_filename);
				worker.outputfiles.emplace_back(std::unique_ptr<AIWWriter>(new AIWWriter(&worker, aiw_filename.c_str())));
				continue;
			}
			if (args[argidx] == "-hdlname") {
				worker.hdlname = true;
				continue;
			}
			if (args[argidx] == "-n" && argidx+1 < args.size()) {
				numcycles = atoi(args[++argidx].c_str());
				worker.cycles_set = true;
				continue;
			}
			if (args[argidx] == "-noinitstate") {
				worker.initstate = false;
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
			if (args[argidx] == "-q") {
				worker.verbose = false;
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
			if (args[argidx] == "-append" && argidx+1 < args.size()) {
				append = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				std::string map_filename = args[++argidx];
				rewrite_filename(map_filename);
				worker.map_filename = map_filename;
				continue;
			}
			if (args[argidx] == "-summary" && argidx+1 < args.size()) {
				std::string summary_filename = args[++argidx];
				rewrite_filename(summary_filename);
				worker.summary_filename = summary_filename;
				continue;
			}
			if (args[argidx] == "-scope" && argidx+1 < args.size()) {
				worker.scope = args[++argidx];
				continue;
			}
			if (args[argidx] == "-start" && argidx+1 < args.size()) {
				worker.start_time = stringToTime(args[++argidx]);
				start_set = true;
				continue;
			}
			if (args[argidx] == "-stop" && argidx+1 < args.size()) {
				worker.stop_time = stringToTime(args[++argidx]);
				stop_set = true;
				continue;
			}
			if (args[argidx] == "-at" && argidx+1 < args.size()) {
				worker.start_time = stringToTime(args[++argidx]);
				worker.stop_time = worker.start_time;
				at_set = true;
				continue;
			}
			if (args[argidx] == "-sim") {
				worker.sim_mode = SimulationMode::sim;
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
			if (args[argidx] == "-assert") {
				worker.serious_asserts = true;
				continue;
			}
			if (args[argidx] == "-x") {
				worker.ignore_x = true;
				continue;
			}
			if (args[argidx] == "-date") {
				worker.date = true;
				continue;
			}
			if (args[argidx] == "-multiclock") {
				worker.multiclock = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		if (at_set && (start_set || stop_set || worker.cycles_set))
			log_error("'at' option can only be defined separate of 'start','stop' and 'n'\n");
		if (stop_set && worker.cycles_set)
			log_error("'stop' and 'n' can only be used exclusively'\n");

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
		else {
			std::string filename_trim = file_base_name(worker.sim_filename);
			if (filename_trim.size() > 4 && ((filename_trim.compare(filename_trim.size()-4, std::string::npos, ".fst") == 0) ||
				filename_trim.compare(filename_trim.size()-4, std::string::npos, ".vcd") == 0)) {
				worker.run_cosim_fst(top_mod, numcycles);
			} else if (filename_trim.size() > 4 && filename_trim.compare(filename_trim.size()-4, std::string::npos, ".aiw") == 0) {
				if (worker.map_filename.empty())
					log_cmd_error("For AIGER witness file map parameter is mandatory.\n");
				worker.run_cosim_aiger_witness(top_mod);
			} else if (filename_trim.size() > 4 && filename_trim.compare(filename_trim.size()-4, std::string::npos, ".wit") == 0) {
				worker.run_cosim_btor2_witness(top_mod);
			} else if (filename_trim.size() > 3 && filename_trim.compare(filename_trim.size()-3, std::string::npos, ".yw") == 0) {
				worker.run_cosim_yw_witness(top_mod, append);
			} else {
				log_cmd_error("Unhandled extension for simulation input file `%s`.\n", worker.sim_filename.c_str());
			}
		}

		worker.write_summary();
	}
} SimPass;

struct Fst2TbPass : public Pass {
	Fst2TbPass() : Pass("fst2tb", "generate testbench out of fst file") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fst2tb [options] [top-level]\n");
		log("\n");
		log("This command generates testbench for the circuit using the given top-level\n");
		log("module and simulus signal from FST file\n");
		log("\n");
		log("    -tb <name>\n");
		log("        generated testbench name.\n");
		log("        files <name>.v and <name>.txt are created as result.\n");
		log("\n");
		log("    -r <filename>\n");
		log("        read simulation FST file\n");
		log("\n");
		log("    -clock <portname>\n");
		log("        name of top-level clock input\n");
		log("\n");
		log("    -clockn <portname>\n");
		log("        name of top-level clock input (inverse polarity)\n");
		log("\n");
		log("    -scope <name>\n");
		log("        scope of simulation top model\n");
		log("\n");
		log("    -start <time>\n");
		log("        start co-simulation in arbitary time (default 0)\n");
		log("\n");
		log("    -stop <time>\n");
		log("        stop co-simulation in arbitary time (default END)\n");
		log("\n");
		log("    -n <integer>\n");
		log("        number of clock cycles to simulate (default: 20)\n");
		log("\n");		
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		SimWorker worker;
		int numcycles = 20;
		bool stop_set = false;
		std::string tb_filename;

		log_header(design, "Executing FST2FB pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-clock" && argidx+1 < args.size()) {
				worker.clock.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-clockn" && argidx+1 < args.size()) {
				worker.clockn.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-r" && argidx+1 < args.size()) {
				std::string sim_filename = args[++argidx];
				rewrite_filename(sim_filename);
				worker.sim_filename = sim_filename;
				continue;
			}
			if (args[argidx] == "-n" && argidx+1 < args.size()) {
				numcycles = atoi(args[++argidx].c_str());
				worker.cycles_set = true;
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
				stop_set = true;
				continue;
			}
			if (args[argidx] == "-tb" && argidx+1 < args.size()) {
				tb_filename = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		if (stop_set && worker.cycles_set)
			log_error("'stop' and 'n' can only be used exclusively'\n");

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

		if (tb_filename.empty())
			log_cmd_error("Testbench name must be defined.\n");

		if (worker.sim_filename.empty())
			log_cmd_error("Stimulus FST file must be defined.\n");

		worker.generate_tb(top_mod, tb_filename, numcycles);
	}
} Fst2TbPass;

PRIVATE_NAMESPACE_END
