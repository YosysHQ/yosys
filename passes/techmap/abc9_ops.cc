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
#include "kernel/utils.h"
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

int map_autoidx;

inline std::string remap_name(RTLIL::IdString abc9_name)
{
	return stringf("$abc$%d$%s", map_autoidx, abc9_name.c_str()+1);
}

void break_scc(RTLIL::Module *module)
{
	// For every unique SCC found, (arbitrarily) find the first
	//   cell in the component, and convert all wires driven by
	//   its output ports into a new PO, and drive its previous
	//   sinks with a new PI
	pool<RTLIL::Const> ids_seen;
	for (auto cell : module->selected_cells()) {
		auto it = cell->attributes.find(ID(abc9_scc_id));
		if (it == cell->attributes.end())
			continue;
		auto r = ids_seen.insert(it->second);
		cell->attributes.erase(it);
		if (!r.second)
			continue;
		for (auto &c : cell->connections_) {
			if (c.second.is_fully_const()) continue;
			if (cell->output(c.first)) {
				SigBit b = c.second.as_bit();
				Wire *w = b.wire;
				if (w->port_input) {
					// In this case, hopefully the loop break has been already created
					// Get the non-prefixed wire
					Wire *wo = module->wire(stringf("%s.abco", b.wire->name.c_str()));
					log_assert(wo != nullptr);
					log_assert(wo->port_output);
					log_assert(b.offset < GetSize(wo));
					c.second = RTLIL::SigBit(wo, b.offset);
				}
				else {
					// Create a new output/input loop break
					w->port_input = true;
					w = module->wire(stringf("%s.abco", w->name.c_str()));
					if (!w) {
						w = module->addWire(stringf("%s.abco", b.wire->name.c_str()), GetSize(b.wire));
						w->port_output = true;
					}
					else {
						log_assert(w->port_input);
						log_assert(b.offset < GetSize(w));
					}
					w->set_bool_attribute(ID(abc9_scc_break));
					c.second = RTLIL::SigBit(w, b.offset);
				}
			}
		}
	}

	module->fixup_ports();
}

void unbreak_scc(RTLIL::Module *module)
{
	// Now 'unexpose' those wires by undoing
	// the expose operation -- remove them from PO/PI
	// and re-connecting them back together
	for (auto wire : module->wires()) {
		auto it = wire->attributes.find(ID(abc9_scc_break));
		if (it != wire->attributes.end()) {
			wire->attributes.erase(it);
			log_assert(wire->port_output);
			wire->port_output = false;
			std::string name = wire->name.str();
			RTLIL::Wire *i_wire = module->wire(name.substr(0, GetSize(name) - 5));
			log_assert(i_wire);
			log_assert(i_wire->port_input);
			i_wire->port_input = false;
			module->connect(i_wire, wire);
		}
	}
	module->fixup_ports();
}

void prep_dff(RTLIL::Module *module)
{
	auto design = module->design;
	log_assert(design);

	SigMap assign_map(module);

	typedef SigSpec clkdomain_t;
	dict<clkdomain_t, int> clk_to_mergeability;

	for (auto cell : module->selected_cells()) {
		if (cell->type != "$__ABC9_FF_")
			continue;

		Wire *abc9_clock_wire = module->wire(stringf("%s.clock", cell->name.c_str()));
		if (abc9_clock_wire == NULL)
			log_error("'%s.clock' is not a wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
		SigSpec abc9_clock = assign_map(abc9_clock_wire);

		clkdomain_t key(abc9_clock);

		auto r = clk_to_mergeability.insert(std::make_pair(abc9_clock, clk_to_mergeability.size() + 1));
		auto r2 YS_ATTRIBUTE(unused) = cell->attributes.insert(std::make_pair(ID(abc9_mergeability), r.first->second));
		log_assert(r2.second);

		Wire *abc9_init_wire = module->wire(stringf("%s.init", cell->name.c_str()));
		if (abc9_init_wire == NULL)
			log_error("'%s.init' is not a wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
		log_assert(GetSize(abc9_init_wire) == 1);
		SigSpec abc9_init = assign_map(abc9_init_wire);
		if (!abc9_init.is_fully_const())
			log_error("'%s.init' is not a constant wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
		r2 = cell->attributes.insert(std::make_pair(ID(abc9_init), abc9_init.as_const()));
		log_assert(r2.second);
	}

	RTLIL::Module *holes_module = design->module(stringf("%s$holes", module->name.c_str()));
	if (holes_module) {
		dict<SigSig, SigSig> replace;
		for (auto it = holes_module->cells_.begin(); it != holes_module->cells_.end(); ) {
			auto cell = it->second;
			if (cell->type.in("$_DFF_N_", "$_DFF_NN0_", "$_DFF_NN1_", "$_DFF_NP0_", "$_DFF_NP1_",
						"$_DFF_P_", "$_DFF_PN0_", "$_DFF_PN1", "$_DFF_PP0_", "$_DFF_PP1_")) {
				SigBit D = cell->getPort("\\D");
				SigBit Q = cell->getPort("\\Q");
				// Remove the DFF cell from what needs to be a combinatorial box
				it = holes_module->cells_.erase(it);
				Wire *port;
				if (GetSize(Q.wire) == 1)
					port = holes_module->wire(stringf("$abc%s", Q.wire->name.c_str()));
				else
					port = holes_module->wire(stringf("$abc%s[%d]", Q.wire->name.c_str(), Q.offset));
				log_assert(port);
				// Prepare to replace "assign <port> = DFF.Q;" with "assign <port> = DFF.D;"
				//   in order to extract the combinatorial control logic that feeds the box
				//   (i.e. clock enable, synchronous reset, etc.)
				replace.insert(std::make_pair(SigSig(port,Q), SigSig(port,D)));
				// Since `flatten` above would have created wires named "<cell>.Q",
				//   extract the pre-techmap cell name
				auto pos = Q.wire->name.str().rfind(".");
				log_assert(pos != std::string::npos);
				IdString driver = Q.wire->name.substr(0, pos);
				// And drive the signal that was previously driven by "DFF.Q" (typically
				//   used to implement clock-enable functionality) with the "<cell>.$abc9_currQ"
				//   wire (which itself is driven an input port) we inserted above
				Wire *currQ = holes_module->wire(stringf("%s.abc9_ff.Q", driver.c_str()));
				log_assert(currQ);
				holes_module->connect(Q, currQ);
			}
			else
				++it;
		}

		for (auto &conn : holes_module->connections_) {
			auto it = replace.find(conn);
			if (it != replace.end())
				conn = it->second;
		}
	}
}

void prep_holes(RTLIL::Module *module, bool dff)
{
	auto design = module->design;
	log_assert(design);

	SigMap sigmap(module);

	dict<SigBit, pool<IdString>> bit_drivers, bit_users;
	TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
	bool abc9_box_seen = false;

	for (auto cell : module->selected_cells()) {
		if (cell->type == "$__ABC9_FF_")
			continue;

		auto inst_module = module->design->module(cell->type);
		bool abc9_box = inst_module && inst_module->attributes.count("\\abc9_box_id");
		bool abc9_flop = false;
		if (abc9_box) {
			abc9_flop = inst_module->get_bool_attribute("\\abc9_flop");
			if (abc9_flop && !dff)
				continue;
			abc9_box_seen = abc9_box;
		}
		else if (!yosys_celltypes.cell_known(cell->type))
			continue;

		for (auto conn : cell->connections()) {
			if (cell->input(conn.first))
				for (auto bit : sigmap(conn.second))
					bit_users[bit].insert(cell->name);

			if (cell->output(conn.first) && !abc9_flop)
				for (auto bit : sigmap(conn.second))
					bit_drivers[bit].insert(cell->name);
		}

		toposort.node(cell->name);
	}

	if (!abc9_box_seen)
		return;

	for (auto &it : bit_users)
		if (bit_drivers.count(it.first))
			for (auto driver_cell : bit_drivers.at(it.first))
			for (auto user_cell : it.second)
				toposort.edge(driver_cell, user_cell);

#if 0
	toposort.analyze_loops = true;
#endif
	bool no_loops YS_ATTRIBUTE(unused) = toposort.sort();
#if 0
	unsigned i = 0;
	for (auto &it : toposort.loops) {
		log("  loop %d\n", i++);
		for (auto cell_name : it) {
			auto cell = module->cell(cell_name);
			log_assert(cell);
			log("\t%s (%s @ %s)\n", log_id(cell), log_id(cell->type), cell->get_src_attribute().c_str());
		}
	}
#endif
	log_assert(no_loops);

	vector<Cell*> box_list;
	for (auto cell_name : toposort.sorted) {
		RTLIL::Cell *cell = module->cell(cell_name);
		log_assert(cell);

		RTLIL::Module* box_module = design->module(cell->type);
		if (!box_module || !box_module->attributes.count("\\abc9_box_id"))
			continue;

		bool blackbox = box_module->get_blackbox_attribute(true /* ignore_wb */);

		// Fully pad all unused input connections of this box cell with S0
		// Fully pad all undriven output connections of this box cell with anonymous wires
		for (const auto &port_name : box_module->ports) {
			RTLIL::Wire* w = box_module->wire(port_name);
			log_assert(w);
			auto it = cell->connections_.find(port_name);
			if (w->port_input) {
				RTLIL::SigSpec rhs;
				if (it != cell->connections_.end()) {
					if (GetSize(it->second) < GetSize(w))
						it->second.append(RTLIL::SigSpec(State::S0, GetSize(w)-GetSize(it->second)));
					rhs = it->second;
				}
				else {
					rhs = RTLIL::SigSpec(State::S0, GetSize(w));
					cell->setPort(port_name, rhs);
				}
			}
			if (w->port_output) {
				RTLIL::SigSpec rhs;
				auto it = cell->connections_.find(w->name);
				if (it != cell->connections_.end()) {
					if (GetSize(it->second) < GetSize(w))
						it->second.append(module->addWire(NEW_ID, GetSize(w)-GetSize(it->second)));
					rhs = it->second;
				}
				else {
					Wire *wire = module->addWire(NEW_ID, GetSize(w));
					if (blackbox)
						wire->set_bool_attribute(ID(abc9_padding));
					rhs = wire;
					cell->setPort(port_name, rhs);
				}
			}
		}

		cell->attributes["\\abc9_box_seq"] = box_list.size();
		box_list.emplace_back(cell);
	}
	log_assert(!box_list.empty());

	RTLIL::Module *holes_module = design->addModule(stringf("%s$holes", module->name.c_str()));
	log_assert(holes_module);
	holes_module->set_bool_attribute("\\abc9_holes");

	dict<IdString, Cell*> cell_cache;
	dict<IdString, std::vector<IdString>> box_ports;

	int port_id = 1;
	for (auto cell : box_list) {
		RTLIL::Module* orig_box_module = design->module(cell->type);
		log_assert(orig_box_module);
		IdString derived_name = orig_box_module->derive(design, cell->parameters);
		RTLIL::Module* box_module = design->module(derived_name);
		if (box_module->has_processes())
			Pass::call_on_module(design, box_module, "proc");

		int box_inputs = 0;
		auto r = cell_cache.insert(std::make_pair(derived_name, nullptr));
		Cell *holes_cell = r.first->second;
		if (r.second && box_module->get_bool_attribute("\\whitebox")) {
			holes_cell = holes_module->addCell(cell->name, cell->type);
			holes_cell->parameters = cell->parameters;
			r.first->second = holes_cell;
		}

		auto r2 = box_ports.insert(cell->type);
		if (r2.second) {
			// Make carry in the last PI, and carry out the last PO
			//   since ABC requires it this way
			IdString carry_in, carry_out;
			for (const auto &port_name : box_module->ports) {
				auto w = box_module->wire(port_name);
				log_assert(w);
				if (w->get_bool_attribute("\\abc9_carry")) {
					if (w->port_input) {
						if (carry_in != IdString())
							log_error("Module '%s' contains more than one 'abc9_carry' input port.\n", log_id(box_module));
						carry_in = port_name;
					}
					if (w->port_output) {
						if (carry_out != IdString())
							log_error("Module '%s' contains more than one 'abc9_carry' output port.\n", log_id(box_module));
						carry_out = port_name;
					}
				}
				else
					r2.first->second.push_back(port_name);
			}

			if (carry_in != IdString() && carry_out == IdString())
				log_error("Module '%s' contains an 'abc9_carry' input port but no output port.\n", log_id(box_module));
			if (carry_in == IdString() && carry_out != IdString())
				log_error("Module '%s' contains an 'abc9_carry' output port but no input port.\n", log_id(box_module));
			if (carry_in != IdString()) {
				r2.first->second.push_back(carry_in);
				r2.first->second.push_back(carry_out);
			}
		}

		for (const auto &port_name : box_ports.at(cell->type)) {
			RTLIL::Wire *w = box_module->wire(port_name);
			log_assert(w);
			RTLIL::Wire *holes_wire;
			RTLIL::SigSpec port_sig;
			if (w->port_input)
				for (int i = 0; i < GetSize(w); i++) {
					box_inputs++;
					holes_wire = holes_module->wire(stringf("\\i%d", box_inputs));
					if (!holes_wire) {
						holes_wire = holes_module->addWire(stringf("\\i%d", box_inputs));
						holes_wire->port_input = true;
						holes_wire->port_id = port_id++;
						holes_module->ports.push_back(holes_wire->name);
					}
					if (holes_cell)
						port_sig.append(holes_wire);
				}
			if (w->port_output)
				for (int i = 0; i < GetSize(w); i++) {
					if (GetSize(w) == 1)
						holes_wire = holes_module->addWire(stringf("$abc%s.%s", cell->name.c_str(), log_id(w->name)));
					else
						holes_wire = holes_module->addWire(stringf("$abc%s.%s[%d]", cell->name.c_str(), log_id(w->name), i));
					holes_wire->port_output = true;
					holes_wire->port_id = port_id++;
					holes_module->ports.push_back(holes_wire->name);
					if (holes_cell)
						port_sig.append(holes_wire);
					else
						holes_module->connect(holes_wire, State::S0);
				}
			if (!port_sig.empty()) {
				if (r.second)
					holes_cell->setPort(w->name, port_sig);
				else
					holes_module->connect(holes_cell->getPort(w->name), port_sig);
			}
		}

		// For flops only, create an extra 1-bit input that drives a new wire
		//   called "<cell>.$abc9_currQ" that is used below
		if (box_module->get_bool_attribute("\\abc9_flop")) {
			log_assert(holes_cell);

			box_inputs++;
			Wire *holes_wire = holes_module->wire(stringf("\\i%d", box_inputs));
			if (!holes_wire) {
				holes_wire = holes_module->addWire(stringf("\\i%d", box_inputs));
				holes_wire->port_input = true;
				holes_wire->port_id = port_id++;
				holes_module->ports.push_back(holes_wire->name);
			}
			Wire *w = holes_module->addWire(stringf("%s.abc9_ff.Q", cell->name.c_str()));
			holes_module->connect(w, holes_wire);
		}
	}
}

void reintegrate(RTLIL::Module *module)
{
	auto design = module->design;
	log_assert(design);

	map_autoidx = autoidx++;

	RTLIL::Module *mapped_mod = design->module(stringf("%s$abc9", module->name.c_str()));
	if (mapped_mod == NULL)
		log_error("ABC output file does not contain a module `%s$abc'.\n", log_id(module));

	for (auto w : mapped_mod->wires())
		module->addWire(remap_name(w->name), GetSize(w));

	for (auto it = module->cells_.begin(); it != module->cells_.end(); )
		if (it->second->type.in(ID($_AND_), ID($_NOT_), ID($__ABC9_FF_)))
			it = module->cells_.erase(it);
		else
			++it;

	dict<SigBit, pool<IdString>> bit_drivers, bit_users;
	TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
	dict<RTLIL::Cell*,RTLIL::Cell*> not2drivers;
	dict<SigBit, std::vector<RTLIL::Cell*>> bit2sinks;

	std::map<IdString, int> cell_stats;
	for (auto mapped_cell : mapped_mod->cells())
	{
		toposort.node(mapped_cell->name);

		RTLIL::Cell *cell = nullptr;
		if (mapped_cell->type == ID($_NOT_)) {
			RTLIL::SigBit a_bit = mapped_cell->getPort(ID::A);
			RTLIL::SigBit y_bit = mapped_cell->getPort(ID::Y);
			bit_users[a_bit].insert(mapped_cell->name);
			bit_drivers[y_bit].insert(mapped_cell->name);

			if (!a_bit.wire) {
				mapped_cell->setPort(ID::Y, module->addWire(NEW_ID));
				RTLIL::Wire *wire = module->wire(remap_name(y_bit.wire->name));
				log_assert(wire);
				module->connect(RTLIL::SigBit(wire, y_bit.offset), State::S1);
			}
			else {
				RTLIL::Cell* driver_lut = nullptr;
				// ABC can return NOT gates that drive POs
				if (!a_bit.wire->port_input) {
					// If it's not a NOT gate that that comes from a PI directly,
					// find the driver LUT and clone that to guarantee that we won't
					// increase the max logic depth
					// (TODO: Optimise by not cloning unless will increase depth)
					RTLIL::IdString driver_name;
					if (GetSize(a_bit.wire) == 1)
						driver_name = stringf("%s$lut", a_bit.wire->name.c_str());
					else
						driver_name = stringf("%s[%d]$lut", a_bit.wire->name.c_str(), a_bit.offset);
					driver_lut = mapped_mod->cell(driver_name);
				}

				if (!driver_lut) {
					// If a driver couldn't be found (could be from PI or box CI)
					// then implement using a LUT
					cell = module->addLut(remap_name(stringf("%s$lut", mapped_cell->name.c_str())),
							RTLIL::SigBit(module->wires_.at(remap_name(a_bit.wire->name)), a_bit.offset),
							RTLIL::SigBit(module->wires_.at(remap_name(y_bit.wire->name)), y_bit.offset),
							RTLIL::Const::from_string("01"));
					bit2sinks[cell->getPort(ID::A)].push_back(cell);
					cell_stats[ID($lut)]++;
				}
				else
					not2drivers[mapped_cell] = driver_lut;
			}
			continue;
		}
		cell_stats[mapped_cell->type]++;

		RTLIL::Cell *existing_cell = nullptr;
		if (mapped_cell->type.in(ID($lut), ID($__ABC9_FF_))) {
			if (mapped_cell->type == ID($lut) &&
					GetSize(mapped_cell->getPort(ID::A)) == 1 &&
					mapped_cell->getParam(ID(LUT)) == RTLIL::Const::from_string("01")) {
				SigSpec my_a = module->wires_.at(remap_name(mapped_cell->getPort(ID::A).as_wire()->name));
				SigSpec my_y = module->wires_.at(remap_name(mapped_cell->getPort(ID::Y).as_wire()->name));
				module->connect(my_y, my_a);
				log_abort();
				continue;
			}
			cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
		}
		else {
			existing_cell = module->cell(mapped_cell->name);
			log_assert(existing_cell);
			cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
		}

		RTLIL::Module* box_module = design->module(mapped_cell->type);
		auto abc9_flop = box_module && box_module->attributes.count("\\abc9_flop");
		for (auto &mapped_conn : mapped_cell->connections()) {
		    RTLIL::SigSpec newsig;
		    for (auto c : mapped_conn.second.chunks()) {
			if (c.width == 0)
			    continue;
			//log_assert(c.width == 1);
			if (c.wire)
			    c.wire = module->wires_.at(remap_name(c.wire->name));
			newsig.append(c);
		    }
		    if (existing_cell) {
			auto it = existing_cell->connections_.find(mapped_conn.first);
			if (it == existing_cell->connections_.end())
			    continue;
			log_assert(GetSize(newsig) >= GetSize(it->second));
			newsig = newsig.extract(0, GetSize(it->second));
		    }
		    cell->setPort(mapped_conn.first, newsig);

		    if (abc9_flop)
			continue;

		    if (cell->input(mapped_conn.first)) {
			for (auto i : newsig)
			    bit2sinks[i].push_back(cell);
			for (auto i : mapped_conn.second)
			    bit_users[i].insert(mapped_cell->name);
		    }
		    if (cell->output(mapped_conn.first))
			for (auto i : mapped_conn.second)
			    bit_drivers[i].insert(mapped_cell->name);
		}

		if (existing_cell) {
		    cell->parameters = existing_cell->parameters;
		    cell->attributes = existing_cell->attributes;
		    if (cell->attributes.erase("\\abc9_box_seq")) {
			module->swap_names(cell, existing_cell);
			module->remove(existing_cell);
		    }
		}
		else {
		    cell->parameters = mapped_cell->parameters;
		    cell->attributes = mapped_cell->attributes;
		}
	}

	// Copy connections (and rename) from mapped_mod to module
	for (auto conn : mapped_mod->connections()) {
		if (!conn.first.is_fully_const()) {
			auto chunks = conn.first.chunks();
			for (auto &c : chunks)
				c.wire = module->wires_.at(remap_name(c.wire->name));
			conn.first = std::move(chunks);
		}
		if (!conn.second.is_fully_const()) {
			auto chunks = conn.second.chunks();
			for (auto &c : chunks)
				if (c.wire)
					c.wire = module->wires_.at(remap_name(c.wire->name));
			conn.second = std::move(chunks);
		}
		module->connect(conn);
	}

	for (auto &it : cell_stats)
		log("ABC RESULTS:   %15s cells: %8d\n", it.first.c_str(), it.second);
	int in_wires = 0, out_wires = 0;

	// Stitch in mapped_mod's inputs/outputs into module
	for (auto port : mapped_mod->ports) {
		RTLIL::Wire *w = mapped_mod->wire(port);
		RTLIL::Wire *wire = module->wire(port);
		log_assert(wire);
		RTLIL::Wire *remap_wire = module->wire(remap_name(port));
		RTLIL::SigSpec signal = RTLIL::SigSpec(wire, 0, GetSize(remap_wire));
		log_assert(GetSize(signal) >= GetSize(remap_wire));

		RTLIL::SigSig conn;
		if (w->port_output) {
			conn.first = signal;
			conn.second = remap_wire;
			out_wires++;
			module->connect(conn);
		}
		else if (w->port_input) {
			conn.first = remap_wire;
			conn.second = signal;
			in_wires++;
			module->connect(conn);
		}
	}

	for (auto &it : bit_users)
		if (bit_drivers.count(it.first))
			for (auto driver_cell : bit_drivers.at(it.first))
			for (auto user_cell : it.second)
				toposort.edge(driver_cell, user_cell);
	bool no_loops YS_ATTRIBUTE(unused) = toposort.sort();
	log_assert(no_loops);

	for (auto ii = toposort.sorted.rbegin(); ii != toposort.sorted.rend(); ii++) {
		RTLIL::Cell *not_cell = mapped_mod->cell(*ii);
		log_assert(not_cell);
		if (not_cell->type != ID($_NOT_))
			continue;
		auto it = not2drivers.find(not_cell);
		if (it == not2drivers.end())
			continue;
		RTLIL::Cell *driver_lut = it->second;
		RTLIL::SigBit a_bit = not_cell->getPort(ID::A);
		RTLIL::SigBit y_bit = not_cell->getPort(ID::Y);
		RTLIL::Const driver_mask;

		a_bit.wire = module->wires_.at(remap_name(a_bit.wire->name));
		y_bit.wire = module->wires_.at(remap_name(y_bit.wire->name));

		auto jt = bit2sinks.find(a_bit);
		if (jt == bit2sinks.end())
			goto clone_lut;

		for (auto sink_cell : jt->second)
			if (sink_cell->type != ID($lut))
				goto clone_lut;

		// Push downstream LUTs past inverter
		for (auto sink_cell : jt->second) {
			SigSpec A = sink_cell->getPort(ID::A);
			RTLIL::Const mask = sink_cell->getParam(ID(LUT));
			int index = 0;
			for (; index < GetSize(A); index++)
				if (A[index] == a_bit)
					break;
			log_assert(index < GetSize(A));
			int i = 0;
			while (i < GetSize(mask)) {
				for (int j = 0; j < (1 << index); j++)
					std::swap(mask[i+j], mask[i+j+(1 << index)]);
				i += 1 << (index+1);
			}
			A[index] = y_bit;
			sink_cell->setPort(ID::A, A);
			sink_cell->setParam(ID(LUT), mask);
		}

		// Since we have rewritten all sinks (which we know
		// to be only LUTs) to be after the inverter, we can
		// go ahead and clone the LUT with the expectation
		// that the original driving LUT will become dangling
		// and get cleaned away
clone_lut:
		driver_mask = driver_lut->getParam(ID(LUT));
		for (auto &b : driver_mask.bits) {
			if (b == RTLIL::State::S0) b = RTLIL::State::S1;
			else if (b == RTLIL::State::S1) b = RTLIL::State::S0;
		}
		auto cell = module->addLut(NEW_ID,
				driver_lut->getPort(ID::A),
				y_bit,
				driver_mask);
		for (auto &bit : cell->connections_.at(ID::A)) {
			bit.wire = module->wires_.at(remap_name(bit.wire->name));
			bit2sinks[bit].push_back(cell);
		}
	}

	//log("ABC RESULTS:        internal signals: %8d\n", int(signal_list.size()) - in_wires - out_wires);
	log("ABC RESULTS:           input signals: %8d\n", in_wires);
	log("ABC RESULTS:          output signals: %8d\n", out_wires);

	design->remove(mapped_mod);
}

struct Abc9OpsPass : public Pass {
	Abc9OpsPass() : Pass("abc9_ops", "helper functions for ABC9") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc9_ops [options] [selection]\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ABC9_OPS pass (helper functions for ABC9).\n");

		bool break_scc_mode = false;
		bool unbreak_scc_mode = false;
		bool prep_dff_mode = false;
		bool prep_holes_mode = false;
		bool reintegrate_mode = false;
		bool dff_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-break_scc") {
				break_scc_mode = true;
				continue;
			}
			if (arg == "-unbreak_scc") {
				unbreak_scc_mode = true;
				continue;
			}
			if (arg == "-prep_dff") {
				prep_dff_mode = true;
				continue;
			}
			if (arg == "-prep_holes") {
				prep_holes_mode = true;
				continue;
			}
			if (arg == "-reintegrate") {
				reintegrate_mode = true;
				continue;
			}
			if (arg == "-dff") {
				dff_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			if (mod->get_bool_attribute("\\abc9_holes"))
				continue;

			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(mod));
				continue;
			}

			if (break_scc_mode)
				break_scc(mod);
			if (unbreak_scc_mode)
				unbreak_scc(mod);
			if (prep_dff_mode)
				prep_dff(mod);
			if (prep_holes_mode)
				prep_holes(mod, dff_mode);
			if (reintegrate_mode)
				reintegrate(mod);
		}
	}
} Abc9OpsPass;

PRIVATE_NAMESPACE_END
