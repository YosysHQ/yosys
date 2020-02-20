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
#include "kernel/timinginfo.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

int map_autoidx;

inline std::string remap_name(RTLIL::IdString abc9_name)
{
	return stringf("$abc$%d$%s", map_autoidx, abc9_name.c_str()+1);
}

void check(RTLIL::Design *design)
{
	dict<IdString,IdString> box_lookup;
	for (auto m : design->modules()) {
		if (m->name.begins_with("$paramod"))
			continue;

		auto flop = m->get_bool_attribute(ID(abc9_flop));
		auto it = m->attributes.find(ID(abc9_box_id));
		if (!flop) {
			if (it == m->attributes.end())
				continue;
			auto id = it->second.as_int();
			auto r = box_lookup.insert(std::make_pair(stringf("$__boxid%d", id), m->name));
			if (!r.second)
				log_error("Module '%s' has the same abc9_box_id = %d value as '%s'.\n",
						log_id(m), id, log_id(r.first->second));
		}

		// Make carry in the last PI, and carry out the last PO
		//   since ABC requires it this way
		IdString carry_in, carry_out;
		for (const auto &port_name : m->ports) {
			auto w = m->wire(port_name);
			log_assert(w);
			if (w->get_bool_attribute("\\abc9_carry")) {
				if (w->port_input) {
					if (carry_in != IdString())
						log_error("Module '%s' contains more than one (* abc9_carry *) input port.\n", log_id(m));
					carry_in = port_name;
				}
				if (w->port_output) {
					if (carry_out != IdString())
						log_error("Module '%s' contains more than one (* abc9_carry *) output port.\n", log_id(m));
					carry_out = port_name;
				}
			}
		}

		if (carry_in != IdString() && carry_out == IdString())
			log_error("Module '%s' contains an (* abc9_carry *) input port but no output port.\n", log_id(m));
		if (carry_in == IdString() && carry_out != IdString())
			log_error("Module '%s' contains an (* abc9_carry *) output port but no input port.\n", log_id(m));

		if (flop) {
			int num_outputs = 0;
			for (auto port_name : m->ports) {
				auto wire = m->wire(port_name);
				if (wire->port_output) num_outputs++;
			}
			if (num_outputs != 1)
				log_error("Module '%s' with (* abc9_flop *) has %d outputs (expect 1).\n", log_id(m), num_outputs);
		}
	}
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
		auto r2  = cell->attributes.insert(ID(abc9_mergeability));;
		log_assert(r2.second);
		r2.first->second = r.first->second;
	}

	RTLIL::Module *holes_module = design->module(stringf("%s$holes", module->name.c_str()));
	if (holes_module) {
		SigMap sigmap(holes_module);

		dict<SigSpec, SigSpec> replace;
		for (auto cell : holes_module->cells().to_vector()) {
			if (!cell->type.in("$_DFF_N_", "$_DFF_NN0_", "$_DFF_NN1_", "$_DFF_NP0_", "$_DFF_NP1_",
						"$_DFF_P_", "$_DFF_PN0_", "$_DFF_PN1", "$_DFF_PP0_", "$_DFF_PP1_"))
				continue;
			SigBit D = cell->getPort("\\D");
			SigBit Q = cell->getPort("\\Q");
			// Emulate async control embedded inside $_DFF_* cell with mux in front of D
			if (cell->type.in("$_DFF_NN0_", "$_DFF_PN0_"))
				D = holes_module->MuxGate(NEW_ID, State::S0, D, cell->getPort("\\R"));
			else if (cell->type.in("$_DFF_NN1_", "$_DFF_PN1_"))
				D = holes_module->MuxGate(NEW_ID, State::S1, D, cell->getPort("\\R"));
			else if (cell->type.in("$_DFF_NP0_", "$_DFF_PP0_"))
				D = holes_module->MuxGate(NEW_ID, D, State::S0, cell->getPort("\\R"));
			else if (cell->type.in("$_DFF_NP1_", "$_DFF_PP1_"))
				D = holes_module->MuxGate(NEW_ID, D, State::S1, cell->getPort("\\R"));
			// Remove the $_DFF_* cell from what needs to be a combinatorial box
			holes_module->remove(cell);
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
		if (cell->has_keep_attr())
			continue;

		auto inst_module = module->design->module(cell->type);
		bool abc9_flop = inst_module && inst_module->get_bool_attribute("\\abc9_flop");
		if (abc9_flop && !dff)
			continue;

		if ((inst_module && inst_module->get_bool_attribute("\\abc9_box")) || abc9_flop) {
			auto r = box_ports.insert(cell->type);
			if (r.second) {
				// Make carry in the last PI, and carry out the last PO
				//   since ABC requires it this way
				IdString carry_in, carry_out;
				for (const auto &port_name : inst_module->ports) {
					auto w = inst_module->wire(port_name);
					log_assert(w);
					if (w->get_bool_attribute("\\abc9_carry")) {
						log_assert(w->port_input != w->port_output);
						if (w->port_input)
							carry_in = port_name;
						else if (w->port_output)
							carry_out = port_name;
					}
					else
						r.first->second.push_back(port_name);
				}
				if (carry_in != IdString()) {
					r.first->second.push_back(carry_in);
					r.first->second.push_back(carry_out);
				}
			}
		}
		else if (!yosys_celltypes.cell_known(cell->type))
			continue;

		// TODO: Speed up toposort -- we care about box ordering only
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
	TimingInfo timing;

	int port_id = 1, box_count = 0;
	for (auto cell_name : toposort.sorted) {
		RTLIL::Cell *cell = module->cell(cell_name);
		log_assert(cell);

		RTLIL::Module* box_module = design->module(cell->type);
		if (!box_module || (!box_module->get_bool_attribute("\\abc9_box") && !box_module->get_bool_attribute("\\abc9_flop")))
			continue;

		cell->attributes["\\abc9_box_seq"] = box_count++;

		IdString derived_type = box_module->derive(design, cell->parameters);
		box_module = design->module(derived_type);

		auto r = cell_cache.insert(derived_type);
		auto &holes_cell = r.first->second;
		if (r.second) {
			if (box_module->has_processes())
				Pass::call_on_module(design, box_module, "proc");

			if (box_module->get_bool_attribute("\\whitebox")) {
				holes_cell = holes_module->addCell(cell->name, derived_type);

				if (box_module->has_processes())
					Pass::call_on_module(design, box_module, "proc");

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
						conn = holes_module->addWire(stringf("%s.%s", derived_type.c_str(), log_id(port_name)), GetSize(w));
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

void prep_delays(RTLIL::Design *design, bool dff_mode)
{
	TimingInfo timing;

	// Derive all Yosys blackbox modules that are not combinatorial abc9 boxes
	//   (e.g. DSPs, RAMs, etc.) nor abc9 flops and collect all such instantiations
	pool<Module*> flops;
	std::vector<Cell*> cells;
	for (auto module : design->selected_modules()) {
		if (module->processes.size() > 0) {
			log("Skipping module %s as it contains processes.\n", log_id(module));
			continue;
		}

		for (auto cell : module->cells()) {
			if (cell->type.in(ID($_AND_), ID($_NOT_), ID($__ABC9_FF_), ID($__ABC9_DELAY)))
				continue;

			RTLIL::Module* inst_module = module->design->module(cell->type);
			if (!inst_module)
				continue;
			if (!inst_module->get_blackbox_attribute())
				continue;
			if (inst_module->attributes.count(ID(abc9_box)))
				continue;
			IdString derived_type = inst_module->derive(design, cell->parameters);
			inst_module = design->module(derived_type);
			log_assert(inst_module);

			if (dff_mode && inst_module->get_bool_attribute(ID(abc9_flop))) {
				flops.insert(inst_module);
				continue; // do not add $__ABC9_DELAY boxes to flops
				//   as delays will be captured in the flop box
			}

			if (!timing.count(derived_type))
				timing.setup_module(inst_module);

			cells.emplace_back(cell);
		}
	}

	// Insert $__ABC9_DELAY cells on all cells that instantiate blackboxes
	//   with required times
	for (auto cell : cells) {
		auto module = cell->module;
		RTLIL::Module* inst_module = module->design->module(cell->type);
		log_assert(inst_module);
		IdString derived_type = inst_module->derive(design, cell->parameters);
		inst_module = design->module(derived_type);
		log_assert(inst_module);

		auto &t = timing.at(derived_type).required;
		for (auto &conn : cell->connections_) {
			auto port_wire = inst_module->wire(conn.first);
			if (!port_wire->port_input)
				continue;

			SigSpec O = module->addWire(NEW_ID, GetSize(conn.second));
			for (int i = 0; i < GetSize(conn.second); i++) {
				auto d = t.at(TimingInfo::NameBit(conn.first,i), 0);
				if (d == 0)
					continue;

#ifndef NDEBUG
				if (ys_debug(1)) {
					static std::set<std::tuple<IdString,IdString,int>> seen;
					if (seen.emplace(derived_type, conn.first, i).second) log("%s.%s[%d] abc9_required = %d\n",
							log_id(cell->type), log_id(conn.first), i, d);
				}
#endif
				auto box = module->addCell(NEW_ID, ID($__ABC9_DELAY));
				box->setPort(ID(I), conn.second[i]);
				box->setPort(ID(O), O[i]);
				box->setParam(ID(DELAY), d);
				conn.second[i] = O[i];
			}
		}
	}
}

void prep_lut(RTLIL::Design *design, int maxlut)
{
	TimingInfo timing;

	std::vector<std::tuple<int, IdString, int, std::vector<int>>> table;
	for (auto module : design->modules()) {
		auto it = module->attributes.find(ID(abc9_lut));
		if (it == module->attributes.end())
			continue;

		auto &t = timing.setup_module(module);

		TimingInfo::NameBit o;
		std::vector<int> specify;
		for (const auto &i : t.comb) {
			auto &d = i.first.second;
			if (o == TimingInfo::NameBit())
				o = d;
			else if (o != d)
				log_error("(* abc9_lut *) module '%s' with has more than one output.\n", log_id(module));
			specify.push_back(i.second);
		}

		if (maxlut && GetSize(specify) > maxlut)
			continue;
		// ABC requires non-decreasing LUT input delays
		std::sort(specify.begin(), specify.end());
		table.emplace_back(GetSize(specify), module->name, it->second.as_int(), std::move(specify));
	}
	// ABC requires ascending size
	std::sort(table.begin(), table.end());

	std::stringstream ss;
	const auto &first = table.front();
	// If the first entry does not start from a 1-input LUT,
	//   (as ABC requires) crop the first entry to do so
	for (int i = 1; i < std::get<0>(first); i++) {
		ss << "# $__ABC9_LUT" << i << std::endl;
		ss << i << " " << std::get<2>(first);
		for (int j = 0; j < i; j++)
			ss << " " << std::get<3>(first)[j];
		ss << std::endl;
	}
	for (const auto &i : table) {
		ss << "# " << log_id(std::get<1>(i)) << std::endl;
		ss << std::get<0>(i) << " " << std::get<2>(i);
		for (const auto &j : std::get<3>(i))
			ss << " " << j;
		ss << std::endl;
	}
	design->scratchpad_set_string("abc9_ops.lut_library", ss.str());
}

void write_lut(RTLIL::Module *module, const std::string &dst) {
	std::ofstream ofs(dst);
	log_assert(ofs.is_open());
	ofs << module->design->scratchpad_get_string("abc9_ops.lut_library");
	ofs.close();
}

void prep_box(RTLIL::Design *design, bool dff_mode)
{
	TimingInfo timing;

	std::stringstream ss;
	int abc9_box_id = 1;
	for (auto module : design->modules()) {
		auto it = module->attributes.find(ID(abc9_box_id));
		if (it == module->attributes.end())
			continue;
		abc9_box_id = std::max(abc9_box_id, it->second.as_int());
	}

	dict<IdString,std::vector<IdString>> box_ports;
	for (auto module : design->modules()) {
		auto abc9_flop = module->get_bool_attribute(ID(abc9_flop));
		if (abc9_flop) {
			auto r = module->attributes.insert(ID(abc9_box_id));
			if (!r.second)
				continue;
			r.first->second = abc9_box_id++;

			if (dff_mode) {
				int num_inputs = 0, num_outputs = 0;
				for (auto port_name : module->ports) {
					auto wire = module->wire(port_name);
					log_assert(GetSize(wire) == 1);
					if (wire->port_input) num_inputs++;
					if (wire->port_output) num_outputs++;
				}
				log_assert(num_outputs == 1);

				ss << log_id(module) << " " << r.first->second.as_int();
				ss << " " << (module->get_bool_attribute(ID::whitebox) ? "1" : "0");
				ss << " " << num_inputs+1 << " " << num_outputs << std::endl;

				ss << "#";
				bool first = true;
				for (auto port_name : module->ports) {
					auto wire = module->wire(port_name);
					if (!wire->port_input)
						continue;
					if (first)
						first = false;
					else
						ss << " ";
					ss << log_id(wire);
				}
				ss << " abc9_ff.Q" << std::endl;

				auto &t = timing.setup_module(module).required;
				first = true;
				for (auto port_name : module->ports) {
					auto wire = module->wire(port_name);
					if (!wire->port_input)
						continue;
					if (first)
						first = false;
					else
						ss << " ";
					log_assert(GetSize(wire) == 1);
					auto it = t.find(TimingInfo::NameBit(port_name,0));
					if (it == t.end())
						// Assume that no setup time means zero
						ss << 0;
					else {
						ss << it->second;

#ifndef NDEBUG
						if (ys_debug(1)) {
							static std::set<std::pair<IdString,IdString>> seen;
							if (seen.emplace(module->name, port_name).second) log("%s.%s abc9_required = %d\n", log_id(module),
									log_id(port_name), it->second);
						}
#endif
					}

				}
				// Last input is 'abc9_ff.Q'
				ss << " 0" << std::endl << std::endl;
				continue;
			}
		}
		else {
			if (!module->attributes.erase(ID(abc9_box)))
				continue;

			auto r = module->attributes.insert(ID(abc9_box_id));
			if (!r.second)
				continue;
			r.first->second = abc9_box_id++;
		}

		auto r = box_ports.insert(module->name);
		if (r.second) {
			// Make carry in the last PI, and carry out the last PO
			//   since ABC requires it this way
			IdString carry_in, carry_out;
			for (const auto &port_name : module->ports) {
				auto w = module->wire(port_name);
				log_assert(w);
				if (w->get_bool_attribute("\\abc9_carry")) {
					log_assert(w->port_input != w->port_output);
					if (w->port_input)
						carry_in = port_name;
					else if (w->port_output)
						carry_out = port_name;
				}
				else
					r.first->second.push_back(port_name);
			}

			if (carry_in != IdString()) {
				r.first->second.push_back(carry_in);
				r.first->second.push_back(carry_out);
			}
		}

		std::vector<SigBit> inputs;
		std::vector<SigBit> outputs;
		for (auto port_name : r.first->second) {
			auto wire = module->wire(port_name);
			if (wire->port_input)
				for (int i = 0; i < GetSize(wire); i++)
					inputs.emplace_back(wire, i);
			if (wire->port_output)
				for (int i = 0; i < GetSize(wire); i++)
					outputs.emplace_back(wire, i);
		}

		ss << log_id(module) << " " << module->attributes.at(ID(abc9_box_id)).as_int();
		ss << " " << (module->get_bool_attribute(ID::whitebox) ? "1" : "0");
		ss << " " << GetSize(inputs) << " " << GetSize(outputs) << std::endl;

		bool first = true;
		ss << "#";
		for (const auto &i : inputs) {
			if (first)
				first = false;
			else
				ss << " ";
			if (GetSize(i.wire) == 1)
				ss << log_id(i.wire);
			else
				ss << log_id(i.wire) << "[" << i.offset << "]";
		}
		ss << std::endl;

		auto &t = timing.setup_module(module).comb;
		if (!abc9_flop && t.empty())
			log_warning("(* abc9_box *) module '%s' has no timing (and thus no connectivity) information.\n", log_id(module));

		for (const auto &o : outputs) {
			first = true;
			for (const auto &i : inputs) {
				if (first)
					first = false;
				else
					ss << " ";
				auto jt = t.find(TimingInfo::BitBit(i,o));
				if (jt == t.end())
					ss << "-";
				else
					ss << jt->second;
			}
			ss << " # ";
			if (GetSize(o.wire) == 1)
				ss << log_id(o.wire);
			else
				ss << log_id(o.wire) << "[" << o.offset << "]";
			ss << std::endl;

		}
		ss << std::endl;
	}

	// ABC expects at least one box
	if (ss.tellp() == 0)
		ss << "(dummy) 1 0 0 0";

	design->scratchpad_set_string("abc9_ops.box_library", ss.str());
}

void write_box(RTLIL::Module *module, const std::string &dst) {
	std::ofstream ofs(dst);
	log_assert(ofs.is_open());
	ofs << module->design->scratchpad_get_string("abc9_ops.box_library");
	ofs.close();
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

	dict<IdString,std::vector<IdString>> box_ports;

	for (auto m : design->modules()) {
		if (!m->attributes.count(ID(abc9_box_id)))
			continue;

		auto r = box_ports.insert(m->name);
		if (!r.second)
			continue;

		// Make carry in the last PI, and carry out the last PO
		//   since ABC requires it this way
		IdString carry_in, carry_out;
		for (const auto &port_name : m->ports) {
			auto w = m->wire(port_name);
			log_assert(w);
			if (w->get_bool_attribute("\\abc9_carry")) {
				log_assert(w->port_input != w->port_output);
				if (w->port_input)
					carry_in = port_name;
				else if (w->port_output)
					carry_out = port_name;
			}
			else
				r.first->second.push_back(port_name);
		}

		if (carry_in != IdString()) {
			r.first->second.push_back(carry_in);
			r.first->second.push_back(carry_out);
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
		// TODO: Speed up toposort -- we care about NOT ordering only
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
			if (!existing_cell)
				log_error("Cannot find existing box cell with name '%s' in original design.\n", log_id(mapped_cell));

			if (existing_cell->type == ID($__ABC9_DELAY)) {
				SigBit I = mapped_cell->getPort(ID(i));
				SigBit O = mapped_cell->getPort(ID(o));
				if (I.wire)
					I.wire = module->wires_.at(remap_name(I.wire->name));
				log_assert(O.wire);
				O.wire = module->wires_.at(remap_name(O.wire->name));
				module->connect(O, I);
				continue;
			}

			RTLIL::Module* box_module = design->module(existing_cell->type);
			IdString derived_type = box_module->derive(design, existing_cell->parameters);
			RTLIL::Module* derived_module = design->module(derived_type);
			log_assert(derived_module);
			log_assert(mapped_cell->type == stringf("$__boxid%d", derived_module->attributes.at("\\abc9_box_id").as_int()));
			mapped_cell->type = existing_cell->type;

			RTLIL::Cell *cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
			cell->parameters = existing_cell->parameters;
			cell->attributes = existing_cell->attributes;
			module->swap_names(cell, existing_cell);

			auto jt = mapped_cell->connections_.find("\\i");
			log_assert(jt != mapped_cell->connections_.end());
			SigSpec inputs = std::move(jt->second);
			mapped_cell->connections_.erase(jt);
			jt = mapped_cell->connections_.find("\\o");
			log_assert(jt != mapped_cell->connections_.end());
			SigSpec outputs = std::move(jt->second);
			mapped_cell->connections_.erase(jt);

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
			for (const auto &port_name : box_ports.at(derived_type)) {
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

	// ABC9 will return $_NOT_ gates in its mapping (since they are
	//   treated as being "free"), in particular driving primary
	//   outputs (real primary outputs, or cells treated as blackboxes)
	//   or driving box inputs.
	// Instead of just mapping those $_NOT_ gates into 2-input $lut-s
	//   at an area and delay cost, see if it is possible to push
	//   this $_NOT_ into the driving LUT, or into all sink LUTs.
	// When this is not possible, (i.e. this signal drives two primary
	//   outputs, only one of which is complemented) and when the driver
	//   is a LUT, then clone the LUT so that it can be inverted without
	//   increasing depth/delay.
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
		log("    -check\n");
		log("        check that the design is valid, e.g. (* abc9_box_id *) values are unique,\n");
		log("        (* abc9_carry *) is only given for one input/output port, etc.\n");
		log("\n");
		log("    -prep_delays\n");
		log("        insert `$__ABC9_DELAY' blackbox cells into the design to account for\n");
		log("        certain required times.\n");
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
		log("    -dff\n");
		log("        consider flop cells (those instantiating modules marked with (* abc9_flop *))\n");
		log("        during -prep_{delays,xaiger,box}.\n");
		log("\n");
		log("    -prep_dff\n");
		log("        compute the clock domain and initial value of each flop in the design.\n");
		log("        process the '$holes' module to support clock-enable functionality.\n");
		log("\n");
		log("    -prep_lut <maxlut>\n");
		log("        pre-compute the lut library by analysing all modules marked with\n");
		log("        (* abc9_lut=<area> *).\n");
		log("\n");
		log("    -write_lut <dst>\n");
		log("        write the pre-computed lut library to <dst>.\n");
		log("\n");
		log("    -prep_box\n");
		log("        pre-compute the box library by analysing all modules marked with\n");
		log("        (* abc9_box *).\n");
		log("\n");
		log("    -write_box <dst>\n");
		log("        write the pre-computed box library to <dst>.\n");
		log("\n");
		log("    -reintegrate\n");
		log("        for each selected module, re-intergrate the module '<module-name>$abc9'\n");
		log("        by first recovering ABC9 boxes, and then stitching in the remaining primary\n");
		log("        inputs and outputs.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ABC9_OPS pass (helper functions for ABC9).\n");

		bool check_mode = false;
		bool prep_delays_mode = false;
		bool mark_scc_mode = false;
		bool prep_dff_mode = false;
		bool prep_xaiger_mode = false;
		bool prep_lut_mode = false;
		bool prep_box_mode = false;
		bool reintegrate_mode = false;
		bool dff_mode = false;
		std::string write_lut_dst;
		int maxlut = 0;
		std::string write_box_dst;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-check") {
				check_mode = true;
				continue;
			}
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
			if (arg == "-prep_delays") {
				prep_delays_mode = true;
				continue;
			}
			if (arg == "-prep_lut" && argidx+1 < args.size()) {
				prep_lut_mode = true;
				maxlut = atoi(args[++argidx].c_str());
				continue;
			}
			if (arg == "-maxlut" && argidx+1 < args.size()) {
				continue;
			}
			if (arg == "-write_lut" && argidx+1 < args.size()) {
				write_lut_dst = args[++argidx];
				rewrite_filename(write_lut_dst);
				continue;
			}
			if (arg == "-prep_box") {
				prep_box_mode = true;
				continue;
			}
			if (arg == "-write_box" && argidx+1 < args.size()) {
				write_box_dst = args[++argidx];
				rewrite_filename(write_box_dst);
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

		if (!(check_mode || mark_scc_mode || prep_delays_mode || prep_xaiger_mode || prep_dff_mode || prep_lut_mode || prep_box_mode || !write_lut_dst.empty() || !write_box_dst.empty() || reintegrate_mode))
			log_cmd_error("At least one of -check, -mark_scc, -prep_{delays,xaiger,dff,lut,box}, -write_{lut,box}, -reintegrate must be specified.\n");

		if (dff_mode && !prep_delays_mode && !prep_xaiger_mode && !prep_box_mode)
			log_cmd_error("'-dff' option is only relevant for -prep_{delay,xaiger,box}.\n");

		if (check_mode)
			check(design);
		if (prep_delays_mode)
			prep_delays(design, dff_mode);
		if (prep_lut_mode)
			prep_lut(design, maxlut);
		if (prep_box_mode)
			prep_box(design, dff_mode);

		for (auto mod : design->selected_modules()) {
			if (mod->get_bool_attribute("\\abc9_holes"))
				continue;

			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(mod));
				continue;
			}

			if (!design->selected_whole_module(mod))
				log_error("Can't handle partially selected module %s!\n", log_id(mod));

			if (!write_lut_dst.empty())
				write_lut(mod, write_lut_dst);
			if (!write_box_dst.empty())
				write_box(mod, write_box_dst);
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
