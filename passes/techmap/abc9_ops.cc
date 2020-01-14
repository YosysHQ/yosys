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

void mark_scc(RTLIL::Module *module)
{
	// For every unique SCC found, (arbitrarily) find the first
	//   cell in the component, and convert all wires driven by
	//   its output ports into a new PO, and drive its previous
	//   sinks with a new PI
	pool<RTLIL::Const> ids_seen;
	for (auto cell : module->cells()) {
		auto it = cell->attributes.find(ID(abc9_scc_id));
		if (it == cell->attributes.end())
			continue;
		auto id = it->second;
		auto r = ids_seen.insert(id);
		cell->attributes.erase(it);
		if (!r.second)
			continue;
		for (auto &c : cell->connections_) {
			if (c.second.is_fully_const()) continue;
			if (cell->output(c.first)) {
				SigBit b = c.second.as_bit();
				Wire *w = b.wire;
				w->set_bool_attribute(ID::keep);
				w->attributes[ID(abc9_scc_id)] = id.as_int();
			}
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

	for (auto cell : module->cells()) {
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
		SigMap sigmap(holes_module);

		dict<SigSpec, SigSpec> replace;
		for (auto it = holes_module->cells_.begin(); it != holes_module->cells_.end(); ) {
			auto cell = it->second;
			if (cell->type.in("$_DFF_N_", "$_DFF_NN0_", "$_DFF_NN1_", "$_DFF_NP0_", "$_DFF_NP1_",
						"$_DFF_P_", "$_DFF_PN0_", "$_DFF_PN1", "$_DFF_PP0_", "$_DFF_PP1_")) {
				SigBit D = cell->getPort("\\D");
				SigBit Q = cell->getPort("\\Q");
				// Remove the $_DFF_* cell from what needs to be a combinatorial box
				it = holes_module->cells_.erase(it);
				Wire *port;
				if (GetSize(Q.wire) == 1)
					port = holes_module->wire(stringf("$abc%s", Q.wire->name.c_str()));
				else
					port = holes_module->wire(stringf("$abc%s[%d]", Q.wire->name.c_str(), Q.offset));
				log_assert(port);
				// Prepare to replace "assign <port> = $_DFF_*.Q;" with "assign <port> = $_DFF_*.D;"
				//   in order to extract just the combinatorial control logic that feeds the box
				//   (i.e. clock enable, synchronous reset, etc.)
				replace.insert(std::make_pair(Q,D));
				// Since `flatten` above would have created wires named "<cell>.Q",
				//   extract the pre-techmap cell name
				auto pos = Q.wire->name.str().rfind(".");
				log_assert(pos != std::string::npos);
				IdString driver = Q.wire->name.substr(0, pos);
				// And drive the signal that was previously driven by "DFF.Q" (typically
				//   used to implement clock-enable functionality) with the "<cell>.$abc9_currQ"
				//   wire (which itself is driven an by input port) we inserted above
				Wire *currQ = holes_module->wire(stringf("%s.abc9_ff.Q", driver.c_str()));
				log_assert(currQ);
				holes_module->connect(Q, currQ);
			}
			else
				++it;
		}

		for (auto &conn : holes_module->connections_)
			conn.second = replace.at(sigmap(conn.second), conn.second);
	}
}

void prep_xaiger(RTLIL::Module *module, bool dff)
{
	auto design = module->design;
	log_assert(design);

	SigMap sigmap(module);

	dict<SigBit, pool<IdString>> bit_drivers, bit_users;
	TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
	dict<IdString, std::vector<IdString>> box_ports;

	for (auto cell : module->cells()) {
		if (cell->type == "$__ABC9_FF_")
			continue;

		auto inst_module = module->design->module(cell->type);
		bool abc9_box = inst_module && inst_module->attributes.count("\\abc9_box_id");
		bool abc9_flop = false;
		if (abc9_box) {
			abc9_flop = inst_module->get_bool_attribute("\\abc9_flop");
			if (abc9_flop && !dff)
				continue;

			auto r = box_ports.insert(cell->type);
			if (r.second) {
				// Make carry in the last PI, and carry out the last PO
				//   since ABC requires it this way
				IdString carry_in, carry_out;
				for (const auto &port_name : inst_module->ports) {
					auto w = inst_module->wire(port_name);
					log_assert(w);
					if (w->get_bool_attribute("\\abc9_carry")) {
						if (w->port_input) {
							if (carry_in != IdString())
								log_error("Module '%s' contains more than one 'abc9_carry' input port.\n", log_id(inst_module));
							carry_in = port_name;
						}
						if (w->port_output) {
							if (carry_out != IdString())
								log_error("Module '%s' contains more than one 'abc9_carry' output port.\n", log_id(inst_module));
							carry_out = port_name;
						}
					}
					else
						r.first->second.push_back(port_name);
				}

				if (carry_in != IdString() && carry_out == IdString())
					log_error("Module '%s' contains an 'abc9_carry' input port but no output port.\n", log_id(inst_module));
				if (carry_in == IdString() && carry_out != IdString())
					log_error("Module '%s' contains an 'abc9_carry' output port but no input port.\n", log_id(inst_module));
				if (carry_in != IdString()) {
					r.first->second.push_back(carry_in);
					r.first->second.push_back(carry_out);
				}
			}
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

	if (box_ports.empty())
		return;

	for (auto &it : bit_users)
		if (bit_drivers.count(it.first))
			for (auto driver_cell : bit_drivers.at(it.first))
			for (auto user_cell : it.second)
				toposort.edge(driver_cell, user_cell);

	if (ys_debug(1))
		toposort.analyze_loops = true;

	bool no_loops YS_ATTRIBUTE(unused) = toposort.sort();

	if (ys_debug(1)) {
		unsigned i = 0;
		for (auto &it : toposort.loops) {
			log("  loop %d\n", i++);
			for (auto cell_name : it) {
				auto cell = module->cell(cell_name);
				log_assert(cell);
				log("\t%s (%s @ %s)\n", log_id(cell), log_id(cell->type), cell->get_src_attribute().c_str());
			}
		}
	}

	log_assert(no_loops);

	RTLIL::Module *holes_module = design->addModule(stringf("%s$holes", module->name.c_str()));
	log_assert(holes_module);
	holes_module->set_bool_attribute("\\abc9_holes");

	dict<IdString, Cell*> cell_cache;

	int port_id = 1, box_count = 0;
	for (auto cell_name : toposort.sorted) {
		RTLIL::Cell *cell = module->cell(cell_name);
		log_assert(cell);

		RTLIL::Module* box_module = design->module(cell->type);
		if (!box_module || !box_module->attributes.count("\\abc9_box_id"))
			continue;

		cell->attributes["\\abc9_box_seq"] = box_count++;

		IdString derived_name = box_module->derive(design, cell->parameters);
		box_module = design->module(derived_name);

		auto r = cell_cache.insert(derived_name);
		auto &holes_cell = r.first->second;
		if (r.second) {
			if (box_module->has_processes())
				Pass::call_on_module(design, box_module, "proc");

			if (box_module->get_bool_attribute("\\whitebox")) {
				holes_cell = holes_module->addCell(cell->name, derived_name);

				int box_inputs = 0;
				for (auto port_name : box_ports.at(cell->type)) {
					RTLIL::Wire *w = box_module->wire(port_name);
					log_assert(w);
					log_assert(!w->port_input || !w->port_output);
					auto &conn = holes_cell->connections_[port_name];
					if (w->port_input) {
						for (int i = 0; i < GetSize(w); i++) {
							box_inputs++;
							RTLIL::Wire *holes_wire = holes_module->wire(stringf("\\i%d", box_inputs));
							if (!holes_wire) {
								holes_wire = holes_module->addWire(stringf("\\i%d", box_inputs));
								holes_wire->port_input = true;
								holes_wire->port_id = port_id++;
								holes_module->ports.push_back(holes_wire->name);
							}
							conn.append(holes_wire);
						}
					}
					else if (w->port_output)
						conn = holes_module->addWire(stringf("%s.%s", derived_name.c_str(), log_id(port_name)), GetSize(w));
				}

				// For flops only, create an extra 1-bit input that drives a new wire
				//   called "<cell>.abc9_ff.Q" that is used below
				if (box_module->get_bool_attribute("\\abc9_flop")) {
					box_inputs++;
					Wire *holes_wire = holes_module->wire(stringf("\\i%d", box_inputs));
					if (!holes_wire) {
						holes_wire = holes_module->addWire(stringf("\\i%d", box_inputs));
						holes_wire->port_input = true;
						holes_wire->port_id = port_id++;
						holes_module->ports.push_back(holes_wire->name);
					}
					Wire *Q = holes_module->addWire(stringf("%s.abc9_ff.Q", cell->name.c_str()));
					holes_module->connect(Q, holes_wire);
				}
			}
			else // box_module is a blackbox
				log_assert(holes_cell == nullptr);
		}

		for (auto port_name : box_ports.at(cell->type)) {
			RTLIL::Wire *w = box_module->wire(port_name);
			log_assert(w);
			if (!w->port_output)
				continue;
			Wire *holes_wire = holes_module->addWire(stringf("$abc%s.%s", cell->name.c_str(), log_id(port_name)), GetSize(w));
			holes_wire->port_output = true;
			holes_wire->port_id = port_id++;
			holes_module->ports.push_back(holes_wire->name);
			if (holes_cell) // whitebox
				holes_module->connect(holes_wire, holes_cell->getPort(port_name));
			else // blackbox
				holes_module->connect(holes_wire, Const(State::S0, GetSize(w)));
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

	dict<IdString,IdString> box_lookup;
	dict<IdString,std::vector<IdString>> box_ports;

	for (auto m : design->modules()) {
		auto it = m->attributes.find(ID(abc9_box_id));
		if (it == m->attributes.end())
			continue;
		if (m->name.begins_with("$paramod"))
			continue;
		auto id = it->second.as_int();
		auto r = box_lookup.insert(std::make_pair(stringf("$__boxid%d", id), m->name));
		if (!r.second)
			log_error("Module '%s' has the same abc9_box_id = %d value as '%s'.\n",
					log_id(m), id, log_id(r.first->second));
		log_assert(r.second);

		auto r2 = box_ports.insert(m->name);
		if (r2.second) {
			// Make carry in the last PI, and carry out the last PO
			//   since ABC requires it this way
			IdString carry_in, carry_out;
			for (const auto &port_name : m->ports) {
				auto w = m->wire(port_name);
				log_assert(w);
				if (w->get_bool_attribute("\\abc9_carry")) {
					if (w->port_input) {
						if (carry_in != IdString())
							log_error("Module '%s' contains more than one 'abc9_carry' input port.\n", log_id(m));
						carry_in = port_name;
					}
					if (w->port_output) {
						if (carry_out != IdString())
							log_error("Module '%s' contains more than one 'abc9_carry' output port.\n", log_id(m));
						carry_out = port_name;
					}
				}
				else
					r2.first->second.push_back(port_name);
			}

			if (carry_in != IdString() && carry_out == IdString())
				log_error("Module '%s' contains an 'abc9_carry' input port but no output port.\n", log_id(m));
			if (carry_in == IdString() && carry_out != IdString())
				log_error("Module '%s' contains an 'abc9_carry' output port but no input port.\n", log_id(m));
			if (carry_in != IdString()) {
				r2.first->second.push_back(carry_in);
				r2.first->second.push_back(carry_out);
			}
		}
	}

	std::vector<Cell*> boxes;
	for (auto cell : module->cells().to_vector()) {
		if (cell->has_keep_attr())
			continue;
		if (cell->type.in(ID($_AND_), ID($_NOT_), ID($__ABC9_FF_)))
			module->remove(cell);
		else if (cell->attributes.erase("\\abc9_box_seq"))
			boxes.emplace_back(cell);
	}

	dict<SigBit, pool<IdString>> bit_drivers, bit_users;
	TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
	dict<RTLIL::Cell*,RTLIL::Cell*> not2drivers;
	dict<SigBit, std::vector<RTLIL::Cell*>> bit2sinks;

	std::map<IdString, int> cell_stats;
	for (auto mapped_cell : mapped_mod->cells())
	{
		toposort.node(mapped_cell->name);

		if (mapped_cell->type == ID($_NOT_)) {
			RTLIL::SigBit a_bit = mapped_cell->getPort(ID::A);
			RTLIL::SigBit y_bit = mapped_cell->getPort(ID::Y);
			bit_users[a_bit].insert(mapped_cell->name);
			// Ignore inouts for topo ordering
			if (y_bit.wire && !(y_bit.wire->port_input && y_bit.wire->port_output))
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
						driver_name = stringf("$lut%s", a_bit.wire->name.c_str());
					else
						driver_name = stringf("$lut%s[%d]", a_bit.wire->name.c_str(), a_bit.offset);
					driver_lut = mapped_mod->cell(driver_name);
				}

				if (!driver_lut) {
					// If a driver couldn't be found (could be from PI or box CI)
					// then implement using a LUT
					RTLIL::Cell *cell = module->addLut(remap_name(stringf("$lut%s", mapped_cell->name.c_str())),
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

		if (mapped_cell->type.in(ID($lut), ID($__ABC9_FF_))) {
			// Convert buffer into direct connection
			if (mapped_cell->type == ID($lut) &&
					GetSize(mapped_cell->getPort(ID::A)) == 1 &&
					mapped_cell->getParam(ID(LUT)) == RTLIL::Const::from_string("01")) {
				SigSpec my_a = module->wires_.at(remap_name(mapped_cell->getPort(ID::A).as_wire()->name));
				SigSpec my_y = module->wires_.at(remap_name(mapped_cell->getPort(ID::Y).as_wire()->name));
				module->connect(my_y, my_a);
				log_abort();
				continue;
			}
			RTLIL::Cell *cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
			cell->parameters = mapped_cell->parameters;
			cell->attributes = mapped_cell->attributes;

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
				cell->setPort(mapped_conn.first, newsig);

				if (cell->input(mapped_conn.first)) {
					for (auto i : newsig)
						bit2sinks[i].push_back(cell);
					for (auto i : mapped_conn.second)
						bit_users[i].insert(mapped_cell->name);
				}
				if (cell->output(mapped_conn.first))
					for (auto i : mapped_conn.second)
						// Ignore inouts for topo ordering
						if (i.wire && !(i.wire->port_input && i.wire->port_output))
							bit_drivers[i].insert(mapped_cell->name);
			}
		}
		else {
			RTLIL::Cell *existing_cell = module->cell(mapped_cell->name);
			log_assert(existing_cell);
			log_assert(mapped_cell->type.begins_with("$__boxid"));

			auto type = box_lookup.at(mapped_cell->type, IdString());
			if (type == IdString())
				log_error("No module with abc9_box_id = %s found.\n", mapped_cell->type.c_str() + strlen("$__boxid"));
			mapped_cell->type = type;

			RTLIL::Cell *cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
			cell->parameters = existing_cell->parameters;
			cell->attributes = existing_cell->attributes;
			module->swap_names(cell, existing_cell);

			auto it = mapped_cell->connections_.find("\\i");
			log_assert(it != mapped_cell->connections_.end());
			SigSpec inputs = std::move(it->second);
			mapped_cell->connections_.erase(it);
			it = mapped_cell->connections_.find("\\o");
			log_assert(it != mapped_cell->connections_.end());
			SigSpec outputs = std::move(it->second);
			mapped_cell->connections_.erase(it);

			RTLIL::Module* box_module = design->module(mapped_cell->type);
			auto abc9_flop = box_module->attributes.count("\\abc9_flop");
			if (!abc9_flop) {
				for (const auto &i : inputs)
					bit_users[i].insert(mapped_cell->name);
				for (const auto &i : outputs)
					// Ignore inouts for topo ordering
					if (i.wire && !(i.wire->port_input && i.wire->port_output))
						bit_drivers[i].insert(mapped_cell->name);
			}

			int input_count = 0, output_count = 0;
			for (const auto &port_name : box_ports.at(cell->type)) {
				RTLIL::Wire *w = box_module->wire(port_name);
				log_assert(w);

				SigSpec sig;
				if (w->port_input) {
					sig = inputs.extract(input_count, GetSize(w));
					input_count += GetSize(w);
				}
				if (w->port_output) {
					sig = outputs.extract(output_count, GetSize(w));
					output_count += GetSize(w);
				}

				SigSpec newsig;
				for (auto c : sig.chunks()) {
					if (c.width == 0)
						continue;
					//log_assert(c.width == 1);
					if (c.wire)
						c.wire = module->wires_.at(remap_name(c.wire->name));
					newsig.append(c);
				}

				auto it = existing_cell->connections_.find(port_name);
				if (it == existing_cell->connections_.end())
					continue;
				if (GetSize(newsig) > GetSize(it->second))
					newsig = newsig.extract(0, GetSize(it->second));
				else
					log_assert(GetSize(newsig) == GetSize(it->second));

				cell->setPort(port_name, newsig);

				if (w->port_input && !abc9_flop)
					for (const auto &i : newsig)
						bit2sinks[i].push_back(cell);
			}
		}

		cell_stats[mapped_cell->type]++;
	}

	for (auto cell : boxes)
		module->remove(cell);

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
		RTLIL::Wire *mapped_wire = mapped_mod->wire(port);
		RTLIL::Wire *wire = module->wire(port);
		log_assert(wire);
		if (wire->attributes.erase(ID(abc9_scc_id))) {
			auto r YS_ATTRIBUTE(unused) = wire->attributes.erase(ID::keep);
			log_assert(r);
		}
		RTLIL::Wire *remap_wire = module->wire(remap_name(port));
		RTLIL::SigSpec signal(wire, 0, GetSize(remap_wire));
		log_assert(GetSize(signal) >= GetSize(remap_wire));

		RTLIL::SigSig conn;
		if (mapped_wire->port_output) {
			conn.first = signal;
			conn.second = remap_wire;
			out_wires++;
			module->connect(conn);
		}
		else if (mapped_wire->port_input) {
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
		log("This pass contains a set of supporting operations for use during ABC technology\n");
		log("mapping, and is expected to be called in conjunction with other operations from\n");
		log("the `abc9' script pass. Only fully-selected modules are supported.\n");
		log("\n");
		log("    -mark_scc\n");
		log("        for an arbitrarily chosen cell in each unique SCC of each selected module\n");
		log("        (tagged with an (* abc9_scc_id = <int> *) attribute), temporarily mark all\n");
		log("        wires driven by this cell's outputs with a (* keep *) attribute in order\n");
		log("        to break the SCC. this temporary attribute will be removed on -reintegrate.\n");
		log("\n");
		log("    -prep_xaiger\n");
		log("        prepare the design for XAIGER output. this includes computing the\n");
		log("        topological ordering of ABC9 boxes, as well as preparing the\n");
		log("        '<module-name>$holes' module that contains the logic behaviour of ABC9\n");
		log("        whiteboxes.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ABC9_OPS pass (helper functions for ABC9).\n");

		bool mark_scc_mode = false;
		bool prep_dff_mode = false;
		bool prep_xaiger_mode = false;
		bool reintegrate_mode = false;
		bool dff_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-mark_scc") {
				mark_scc_mode = true;
				continue;
			}
			if (arg == "-prep_dff") {
				prep_dff_mode = true;
				continue;
			}
			if (arg == "-prep_xaiger") {
				prep_xaiger_mode = true;
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

		if (!(mark_scc_mode || prep_dff_mode || reintegrate_mode))
			log_cmd_error("At least one of -mark_scc, -prep_{xaiger,dff}, -reintegrate must be specified.\n");

		if (dff_mode && !prep_xaiger_mode)
			log_cmd_error("'-dff' option is only relevant for -prep_xaiger.\n");

		for (auto mod : design->selected_modules()) {
			if (mod->get_bool_attribute("\\abc9_holes"))
				continue;

			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(mod));
				continue;
			}

			if (!design->selected_whole_module(mod))
				log_error("Can't handle partially selected module %s!\n", log_id(mod));

			if (mark_scc_mode)
				mark_scc(mod);
			if (prep_dff_mode)
				prep_dff(mod);
			if (prep_xaiger_mode)
				prep_xaiger(mod, dff_mode);
			if (reintegrate_mode)
				reintegrate(mod);
		}
	}
} Abc9OpsPass;

PRIVATE_NAMESPACE_END
