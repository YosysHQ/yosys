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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

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
		auto inst_module = design->module(cell->type);
		if (!inst_module || !inst_module->attributes.count("\\abc9_flop")
				|| cell->get_bool_attribute("\\abc9_keep"))
			continue;

		Wire *abc9_clock_wire = module->wire(stringf("%s.$abc9_clock", cell->name.c_str()));
		if (abc9_clock_wire == NULL)
			log_error("'%s$abc9_clock' is not a wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
		SigSpec abc9_clock = assign_map(abc9_clock_wire);

		clkdomain_t key(abc9_clock);

		auto r = clk_to_mergeability.insert(std::make_pair(abc9_clock, clk_to_mergeability.size() + 1));
		auto r2 YS_ATTRIBUTE(unused) = cell->attributes.insert(std::make_pair(ID(abc9_mergeability), r.first->second));
		log_assert(r2.second);

		Wire *abc9_init_wire = module->wire(stringf("%s.$abc9_init", cell->name.c_str()));
		if (abc9_init_wire == NULL)
		    log_error("'%s.$abc9_init' is not a wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
		log_assert(GetSize(abc9_init_wire) == 1);
		SigSpec abc9_init = assign_map(abc9_init_wire);
		if (!abc9_init.is_fully_const())
		    log_error("'%s.$abc9_init' is not a constant wire present in module '%s'.\n", cell->name.c_str(), log_id(module));
		r2 = cell->attributes.insert(std::make_pair(ID(abc9_init), abc9_init.as_const()));
		log_assert(r2.second);
	}
}

void prep_holes(RTLIL::Module *module)
{
	auto design = module->design;
	log_assert(design);

	SigMap sigmap(module);

	// TODO: Speed up toposort -- ultimately we care about
	//       box ordering, but not individual AIG cells
	dict<SigBit, pool<IdString>> bit_drivers, bit_users;
	TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
	bool abc9_box_seen = false;

	for (auto cell : module->selected_cells()) {
		if (cell->type == "$_NOT_")
		{
			SigBit A = sigmap(cell->getPort("\\A").as_bit());
			SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
			toposort.node(cell->name);
			bit_users[A].insert(cell->name);
			bit_drivers[Y].insert(cell->name);
			continue;
		}

		if (cell->type == "$_AND_")
		{
			SigBit A = sigmap(cell->getPort("\\A").as_bit());
			SigBit B = sigmap(cell->getPort("\\B").as_bit());
			SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
			toposort.node(cell->name);
			bit_users[A].insert(cell->name);
			bit_users[B].insert(cell->name);
			bit_drivers[Y].insert(cell->name);
			continue;
		}

		if (cell->type == "$__ABC9_FF_")
			continue;

		RTLIL::Module* inst_module = design->module(cell->type);
		if (inst_module) {
			if (!inst_module->attributes.count("\\abc9_box_id") || cell->get_bool_attribute("\\abc9_keep"))
				continue;

			for (const auto &conn : cell->connections()) {
				auto port_wire = inst_module->wire(conn.first);
				// Ignore inout for the sake of topographical ordering
				if (port_wire->port_input && !port_wire->port_output)
					for (auto bit : sigmap(conn.second))
						bit_users[bit].insert(cell->name);
				if (port_wire->port_output)
					for (auto bit : sigmap(conn.second))
						bit_drivers[bit].insert(cell->name);
			}

                        abc9_box_seen = true;

                        toposort.node(cell->name);
		}
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
		if (!box_module || !box_module->attributes.count("\\abc9_box_id")
				|| cell->get_bool_attribute("\\abc9_keep"))
			continue;

		bool blackbox = box_module->get_blackbox_attribute(true /* ignore_wb */);

		// Fully pad all unused input connections of this box cell with S0
		// Fully pad all undriven output connections of this box cell with anonymous wires
		// NB: Assume box_module->ports are sorted alphabetically
		//     (as RTLIL::Module::fixup_ports() would do)
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

		box_list.emplace_back(cell);
	}
	log_assert(!box_list.empty());

	RTLIL::Module *holes_module = design->addModule(stringf("%s$holes", module->name.c_str()));
	log_assert(holes_module);

	dict<IdString, Cell*> cell_cache;

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

			// Since Module::derive() will create a new module, there
			//   is a chance that the ports will be alphabetically ordered
			//   again, which is a problem when carry-chains are involved.
			//   Inherit the port ordering from the original module here...
			//   (and set the port_id below, when iterating through those)
			log_assert(GetSize(box_module->ports) == GetSize(orig_box_module->ports));
			box_module->ports = orig_box_module->ports;
		}

		// NB: Assume box_module->ports are sorted alphabetically
		//     (as RTLIL::Module::fixup_ports() would do)
		int box_port_id = 1;
		for (const auto &port_name : box_module->ports) {
			RTLIL::Wire *w = box_module->wire(port_name);
			log_assert(w);
			if (r.second)
				w->port_id = box_port_id++;
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
			Wire *w = holes_module->addWire(stringf("%s.$abc9_currQ", cell->name.c_str()));
			holes_module->connect(w, holes_wire);
		}
	}

	log_push();

	// NB: fixup_ports() will sort ports by name
	//holes_module->fixup_ports();
	holes_module->check();

	// Cannot techmap/aigmap/check all lib_whitebox-es outside of write_xaiger
	//   since boxes may contain parameters in which case `flatten` would have
	//   created a new $paramod ...
	Pass::call_on_module(design, holes_module, "flatten -wb; techmap; aigmap");

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
			Wire *currQ = holes_module->wire(stringf("%s.$abc9_currQ", driver.c_str()));
			log_assert(currQ);
			holes_module->connect(Q, currQ);
			continue;
		}
		else if (!cell->type.in("$_NOT_", "$_AND_"))
			log_error("Whitebox contents cannot be represented as AIG. Please verify whiteboxes are synthesisable.\n");
		++it;
	}

	for (auto &conn : holes_module->connections_) {
		auto it = replace.find(conn);
		if (it != replace.end())
			conn = it->second;
	}

	// Move into a new (temporary) design so that "clean" will only
	// operate (and run checks on) this one module
	RTLIL::Design *holes_design = new RTLIL::Design;
	holes_design->add(holes_module);
	Pass::call(holes_design, "opt -purge");
	holes_design->modules_.erase(holes_module->name);
	holes_module->design = design;

	holes_module->set_bool_attribute(ID::whitebox);

	log_pop();
}

struct Abc9PrepPass : public Pass {
	Abc9PrepPass() : Pass("abc9_ops", "helper functions for ABC9") { }
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
		log_push();

		bool break_scc_mode = false;
		bool unbreak_scc_mode = false;
		bool prep_dff_mode = false;
		bool prep_holes_mode = false;

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
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			if (mod->get_blackbox_attribute())
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
				prep_holes(mod);
		}
	}
} Abc9PrepPass;

PRIVATE_NAMESPACE_END
