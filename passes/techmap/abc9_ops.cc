/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/newcelltypes.h"
#include "kernel/timinginfo.h"
#include <optional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void check(RTLIL::Design *design, bool dff_mode)
{
	dict<IdString,IdString> box_lookup;
	for (auto m : design->modules()) {
		auto flop = m->get_bool_attribute(ID::abc9_flop);
		auto it = m->attributes.find(ID::abc9_box_id);
		if (!flop) {
			if (it == m->attributes.end())
				continue;
			auto id = it->second.as_int();
			auto r = box_lookup.insert(std::make_pair(stringf("$__boxid%d", id), m->name));
			if (!r.second)
				log_error("Module '%s' has the same abc9_box_id = %d value as '%s'.\n",
						m, id, r.first->second.unescape());
		}

		// Make carry in the last PI, and carry out the last PO
		//   since ABC requires it this way
		IdString carry_in, carry_out;
		for (const auto &port_name : m->ports) {
			auto w = m->wire(port_name);
			log_assert(w);
			if (w->get_bool_attribute(ID::abc9_carry)) {
				if (w->port_input) {
					if (carry_in != IdString())
						log_error("Module '%s' contains more than one (* abc9_carry *) input port.\n", m);
					carry_in = port_name;
				}
				if (w->port_output) {
					if (carry_out != IdString())
						log_error("Module '%s' contains more than one (* abc9_carry *) output port.\n", m);
					carry_out = port_name;
				}
			}
		}

		if (carry_in != IdString() && carry_out == IdString())
			log_error("Module '%s' contains an (* abc9_carry *) input port but no output port.\n", m);
		if (carry_in == IdString() && carry_out != IdString())
			log_error("Module '%s' contains an (* abc9_carry *) output port but no input port.\n", m);

		if (flop) {
			int num_outputs = 0;
			for (auto port_name : m->ports) {
				auto wire = m->wire(port_name);
				if (wire->port_output) num_outputs++;
			}
			if (num_outputs != 1)
				log_error("Module '%s' with (* abc9_flop *) has %d outputs (expect 1).\n", m, num_outputs);
		}
	}

	if (dff_mode) {
		static pool<IdString> unsupported{
			ID($adff), ID($dlatch), ID($dlatchsr), ID($sr),
			ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
			ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_),
			ID($_DLATCH_N_), ID($_DLATCH_P_),
			ID($_DLATCHSR_NNN_), ID($_DLATCHSR_NNP_), ID($_DLATCHSR_NPN_), ID($_DLATCHSR_NPP_),
			ID($_DLATCHSR_PNN_), ID($_DLATCHSR_PNP_), ID($_DLATCHSR_PPN_), ID($_DLATCHSR_PPP_),
			ID($_SR_NN_), ID($_SR_NP_), ID($_SR_PN_), ID($_SR_PP_)
		};
		for (auto module : design->selected_modules())
			for (auto cell : module->cells()) {
				auto inst_module = design->module(cell->type);
				if (!inst_module)
					continue;
				IdString derived_type;
				Module *derived_module;
				if (cell->parameters.empty()) {
					derived_type = cell->type;
					derived_module = inst_module;
				}
				else {
					// Check potential (since its value may depend on a parameter,
					//   but not its existence)
					if (!inst_module->has_attribute(ID::abc9_flop))
						continue;
					derived_type = inst_module->derive(design, cell->parameters);
					derived_module = design->module(derived_type);
					log_assert(derived_module);
				}
				if (!derived_module->get_bool_attribute(ID::abc9_flop))
					continue;
				if (derived_module->get_blackbox_attribute(true /* ignore_wb */))
					log_error("Module '%s' with (* abc9_flop *) is a blackbox.\n", derived_type.unescape());

				if (derived_module->has_processes())
					Pass::call_on_module(design, derived_module, "proc -noopt");

				bool found = false;
				for (auto derived_cell : derived_module->cells()) {
					if (derived_cell->type.in(ID($dff), ID($_DFF_N_), ID($_DFF_P_))) {
						if (found)
							log_error("Whitebox '%s' with (* abc9_flop *) contains more than one $_DFF_[NP]_ cell.\n", derived_module);
						found = true;

						SigBit Q = derived_cell->getPort(ID::Q);
						log_assert(GetSize(Q.wire) == 1);

						if (!Q.wire->port_output)
							log_error("Whitebox '%s' with (* abc9_flop *) contains a %s cell where its 'Q' port does not drive a module output.\n", derived_module, derived_cell->type.unescape());

						Const init = Q.wire->attributes.at(ID::init, State::Sx);
						log_assert(GetSize(init) == 1);
					}
					else if (unsupported.count(derived_cell->type))
						log_error("Whitebox '%s' with (* abc9_flop *) contains a %s cell, which is not supported for sequential synthesis.\n", derived_module, derived_cell->type.unescape());
				}
			}
	}
}

void prep_hier(RTLIL::Design *design, bool dff_mode)
{
	auto r = saved_designs.emplace("$abc9_unmap", nullptr);
	if (r.second)
		r.first->second = new Design;
	Design *unmap_design = r.first->second;

	// Keep track of derived versions of modules that we haven't used, to prevent these being used for unwanted techmaps later on.
	pool<IdString> unused_derived;

	for (auto module : design->selected_modules())
		for (auto cell : module->cells()) {
			auto inst_module = design->module(cell->type);
			if (!inst_module)
				continue;
			IdString derived_type;
			Module *derived_module;
			if (cell->parameters.empty()) {
				derived_type = cell->type;
				derived_module = inst_module;
			}
			else {
				derived_type = inst_module->derive(design, cell->parameters);
				derived_module = design->module(derived_type);
				unused_derived.insert(derived_type);
			}

			if (derived_module->get_bool_attribute(ID::abc9_flop)) {
				if (!dff_mode)
					continue;
			}
			else {
				bool has_timing = false;
				for (auto derived_cell : derived_module->cells()) {
					if (derived_cell->type.in(ID($specify2), ID($specify3), ID($specrule))) {
						// If the module contains timing; then we potentially care about deriving its content too,
						// as timings (or associated port widths) could be dependent on parameters.
						has_timing = true;
						break;
					}
				}
				if (!derived_module->get_bool_attribute(ID::abc9_box) && !derived_module->get_bool_attribute(ID::abc9_bypass) && !has_timing) {
					if (unmap_design->module(derived_type)) {
						// If derived_type is present in unmap_design, it means that it was processed previously, but found to be incompatible -- e.g. if
						// it contained a non-zero initial state. In this case, continue to replace the cell type/parameters so that it has the same properties
						// as a compatible type, yet will be safely unmapped later
						cell->type = derived_type;
						cell->parameters.clear();
						unused_derived.erase(derived_type);
					}
					continue;
				}
			}

			if (!unmap_design->module(derived_type)) {
				if (derived_module->has_processes())
					Pass::call_on_module(design, derived_module, "proc -noopt");

				if (derived_module->get_bool_attribute(ID::abc9_flop)) {
					for (auto derived_cell : derived_module->cells())
						if (derived_cell->type.in(ID($dff), ID($_DFF_N_), ID($_DFF_P_))) {
							SigBit Q = derived_cell->getPort(ID::Q);
							Const init = Q.wire->attributes.at(ID::init, State::Sx);
							log_assert(GetSize(init) == 1);

							// Block sequential synthesis on cells with (* init *) != 1'b0
							//   because ABC9 doesn't support them
							if (init != State::S0) {
								log_warning("Whitebox '%s' with (* abc9_flop *) contains a %s cell with non-zero initial state -- this is not supported for ABC9 sequential synthesis. Treating as a blackbox.\n", derived_module, derived_cell->type.unescape());
								derived_module->set_bool_attribute(ID::abc9_flop, false);
							}
							break;
						}
				}
				else if (derived_module->get_bool_attribute(ID::abc9_box)) {
					for (auto derived_cell : derived_module->cells())
						if (derived_cell->is_mem_cell() || derived_cell->is_builtin_ff()) {
							derived_module->set_bool_attribute(ID::abc9_box, false);
							derived_module->set_bool_attribute(ID::abc9_bypass);
							break;
						}
				}

				if (derived_type != cell->type) {
					auto unmap_module = unmap_design->addModule(derived_type);
					auto replace_cell = unmap_module->addCell(ID::_TECHMAP_REPLACE_, cell->type);
					for (auto port : derived_module->ports) {
						auto w = unmap_module->addWire(port, derived_module->wire(port));
						// Do not propagate (* init *) values into the box,
						//   in fact, remove it from outside too
						if (w->port_output)
							w->attributes.erase(ID::init);
						// Attach (* techmap_autopurge *) to all ports to ensure that
						//   undriven inputs/unused outputs are propagated through to
						//   the techmapped cell
						w->attributes[ID::techmap_autopurge] = 1;

						replace_cell->setPort(port, w);
					}
					unmap_module->ports = derived_module->ports;
					unmap_module->check();

					replace_cell->parameters = cell->parameters;
				}
			}

			cell->type = derived_type;
			cell->parameters.clear();
			unused_derived.erase(derived_type);
		}
	for (auto unused : unused_derived) {
		design->remove(design->module(unused));
	}
}

void prep_bypass(RTLIL::Design *design)
{
	auto r = saved_designs.emplace("$abc9_map", nullptr);
	if (r.second)
		r.first->second = new Design;
	Design *map_design = r.first->second;

	r = saved_designs.emplace("$abc9_unmap", nullptr);
	if (r.second)
		r.first->second = new Design;
	Design *unmap_design = r.first->second;

	pool<IdString> processed;
	for (auto module : design->selected_modules())
		for (auto cell : module->cells()) {
			if (!processed.insert(cell->type).second)
				continue;
			auto inst_module = design->module(cell->type);
			if (!inst_module)
				continue;
			if (!inst_module->get_bool_attribute(ID::abc9_bypass))
				continue;
			log_assert(!inst_module->get_blackbox_attribute(true /* ignore_wb */));
			log_assert(cell->parameters.empty());


			// The idea is to create two techmap designs, one which maps:
			//
			//   box u0 (.i(i), .o(o));
			//
			// to
			//
			//   wire $abc9$o;
			//   box u0 (.i(i), .o($abc9_byp$o));
			//   box_$abc9_byp (.i(i), .$abc9_byp$o($abc9_byp$o), .o(o));
			//
			// the purpose being to move the (* abc9_box *) status from 'box'
			// (which is stateful) to 'box_$abc9_byp' (which becomes a new
			// combinatorial black- (not white-) box with all state elements
			// removed). This has the effect of preserving any combinatorial
			// paths through an otherwise sequential primitive -- e.g. LUTRAMs.
			//
			// The unmap design performs the reverse:
			//
			//   wire $abc9$o;
			//   box u0 (.i(i), .o($abc9_byp$o));
			//   box_$abc9_byp (.i(i), .$abc9_byp$o($abc9_byp$o), .o(o));
			//
			// to:
			//
			//   wire $abc9$o;
			//   box u0 (.i(i), .o($abc9_byp$o));
			//   assign o = $abc9_byp$o;


			// Copy inst_module into map_design, with the same interface
			//   and duplicate $abc9$* wires for its output ports
			auto map_module = map_design->addModule(cell->type);
			for (auto port_name : inst_module->ports) {
				auto w = map_module->addWire(port_name, inst_module->wire(port_name));
				if (w->port_output)
					w->attributes.erase(ID::init);
			}
			map_module->ports = inst_module->ports;
			map_module->check();
			map_module->set_bool_attribute(ID::whitebox);

			// Create the bypass module in the user design, which has the same
			//   interface as the derived module but with additional input
			//   ports driven by the outputs of the replaced cell
			auto bypass_module = design->addModule(cell->type.str() + "_$abc9_byp");
			for (auto port_name : inst_module->ports) {
				auto port = inst_module->wire(port_name);
				if (!port->port_output)
					continue;
				auto dst = bypass_module->addWire(port_name, port);
				auto src = bypass_module->addWire("$abc9byp$" + port_name.str(), GetSize(port));
				src->port_input = true;
				// For these new input ports driven by the replaced
				//   cell, then create a new simple-path specify entry:
				//     (input => output) = 0
				auto specify = bypass_module->addCell(NEW_ID, ID($specify2));
				specify->setPort(ID::EN, State::S1);
				specify->setPort(ID::SRC, src);
				specify->setPort(ID::DST, dst);
				specify->setParam(ID::FULL, 0);
				specify->setParam(ID::SRC_WIDTH, GetSize(src));
				specify->setParam(ID::DST_WIDTH, GetSize(dst));
				specify->setParam(ID::SRC_DST_PEN, 0);
				specify->setParam(ID::SRC_DST_POL, 0);
				specify->setParam(ID::T_RISE_MIN, 0);
				specify->setParam(ID::T_RISE_TYP, 0);
				specify->setParam(ID::T_RISE_MAX, 0);
				specify->setParam(ID::T_FALL_MIN, 0);
				specify->setParam(ID::T_FALL_TYP, 0);
				specify->setParam(ID::T_FALL_MAX, 0);
			}
			bypass_module->set_bool_attribute(ID::blackbox);
			bypass_module->set_bool_attribute(ID::abc9_box);

			// Copy any 'simple' (combinatorial) specify paths from
			//   the derived module into the bypass module, if EN
			//   is not false and SRC/DST are driven only by
			//   module ports; create new input port if one doesn't
			//   already exist
			for (auto cell : inst_module->cells()) {
				if (cell->type != ID($specify2))
					continue;
				auto EN = cell->getPort(ID::EN).as_bit();
				SigBit newEN;
				if (!EN.wire && EN != State::S1)
					continue;
				auto SRC = cell->getPort(ID::SRC);
				for (const auto &c : SRC.chunks())
					if (c.wire && !c.wire->port_input) {
						SRC = SigSpec();
						break;
					}
				if (SRC.empty())
					continue;
				auto DST = cell->getPort(ID::DST);
				for (const auto &c : DST.chunks())
					if (c.wire && !c.wire->port_output) {
						DST = SigSpec();
						break;
					}
				if (DST.empty())
					continue;
				auto rw = [bypass_module](RTLIL::SigSpec &sig)
				{
					SigSpec new_sig;
					for (auto c : sig.chunks()) {
						if (c.wire) {
							auto port = bypass_module->wire(c.wire->name);
							if (!port)
								port = bypass_module->addWire(c.wire->name, c.wire);
							c.wire = port;
						}
						new_sig.append(std::move(c));
					}
					sig = std::move(new_sig);
				};
				auto specify = bypass_module->addCell(NEW_ID, cell);
				specify->rewrite_sigspecs(rw);
			}
			bypass_module->fixup_ports();

			// Create an _TECHMAP_REPLACE_ cell identical to the original cell,
			//   and a bypass cell that has the same inputs/outputs as the
			//   original cell, but with additional inputs taken from the
			//   replaced cell
			auto replace_cell = map_module->addCell(ID::_TECHMAP_REPLACE_, cell->type);
			auto bypass_cell = map_module->addCell(NEW_ID, cell->type.str() + "_$abc9_byp");
			for (const auto &conn : cell->connections()) {
				auto port = map_module->wire(conn.first);
				if (cell->input(conn.first)) {
					replace_cell->setPort(conn.first, port);
					if (bypass_module->wire(conn.first))
						bypass_cell->setPort(conn.first, port);
				}
				if (cell->output(conn.first)) {
					bypass_cell->setPort(conn.first, port);
					auto n = "$abc9byp$" + conn.first.str();
					auto w = map_module->addWire(n, GetSize(conn.second));
					replace_cell->setPort(conn.first, w);
					bypass_cell->setPort(n, w);
				}
			}


			// Lastly, create a new module in the unmap_design that shorts
			//   out the bypass cell back to leave the replace cell behind
			//   driving the outputs
			auto unmap_module = unmap_design->addModule(cell->type.str() + "_$abc9_byp");
			for (auto port_name : inst_module->ports) {
				auto w = unmap_module->addWire(port_name, inst_module->wire(port_name));
				if (w->port_output) {
					w->attributes.erase(ID::init);
					auto w2 = unmap_module->addWire("$abc9byp$" + port_name.str(), GetSize(w));
					w2->port_input = true;
					unmap_module->connect(w, w2);
				}
			}
			unmap_module->fixup_ports();

			design->scratchpad_set_bool("abc9_ops.prep_bypass.did_something", true);
		}
}

void prep_dff(RTLIL::Design *design)
{
	auto r = design->selection_vars.insert(std::make_pair(ID($abc9_flops), RTLIL::Selection::EmptySelection(design)));
	auto &modules_sel = r.first->second;

	for (auto module : design->selected_modules())
		for (auto cell : module->cells()) {
			if (modules_sel.selected_whole_module(cell->type))
				continue;
			auto inst_module = design->module(cell->type);
			if (!inst_module)
				continue;
			if (!inst_module->get_bool_attribute(ID::abc9_flop))
				continue;
			log_assert(!inst_module->get_blackbox_attribute(true /* ignore_wb */));
			if (!cell->parameters.empty())
			{
				// At this stage of the ABC9 flow, cells instantiating (* abc9_flop *) modules must not contain any parameters -- instead it should
				// be instantiating the derived module which will have had any parameters constant-propagated.
				// This task is expected to be performed by `abc9_ops -prep_hier`, but it looks like it failed to do so for this design.
				// Please file a bug report!
				log_error("Not expecting parameters on cell '%s' instantiating module '%s' marked (* abc9_flop *)\n", cell->name.unescape(), cell->type.unescape());
			}
			modules_sel.select(inst_module);
		}
}

void prep_dff_submod(RTLIL::Design *design)
{
	for (auto module : design->modules()) {
		vector<Cell*> specify_cells;
		SigBit Q;
		Cell* dff_cell = nullptr;

		if (!module->get_bool_attribute(ID::abc9_flop))
			continue;

		for (auto cell : module->cells())
			if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_))) {
				log_assert(!dff_cell);
				dff_cell = cell;
				Q = cell->getPort(ID::Q);
				log_assert(GetSize(Q.wire) == 1);
			}
			else if (cell->type.in(ID($specify3), ID($specrule)))
				specify_cells.emplace_back(cell);
		log_assert(dff_cell);

		// Add an always-enabled CE mux that drives $_DFF_[NP]_.D so that:
		//   (a) flop box will have an output
		//   (b) $_DFF_[NP]_.Q will be present as an input
		SigBit D = module->addWire(NEW_ID);
		module->addMuxGate(NEW_ID, dff_cell->getPort(ID::D), Q, State::S0, D);
		dff_cell->setPort(ID::D, D);

		// Rewrite $specify cells that end with $_DFF_[NP]_.Q
		//   to $_DFF_[NP]_.D since it will be moved into
		//   the submodule
		for (auto cell : specify_cells) {
			auto DST = cell->getPort(ID::DST);
			DST.replace(Q, D);
			cell->setPort(ID::DST, DST);
		}

		design->scratchpad_set_bool("abc9_ops.prep_dff_submod.did_something", true);
	}
}

void prep_dff_unmap(RTLIL::Design *design)
{
	Design *unmap_design = saved_designs.at("$abc9_unmap");

	for (auto module : design->modules()) {
		if (!module->get_bool_attribute(ID::abc9_flop) || module->get_bool_attribute(ID::abc9_box))
			continue;

		// Make sure the box module has all the same ports present on flop cell
		auto replace_cell = module->cell(ID::_TECHMAP_REPLACE_);
		log_assert(replace_cell);
		auto box_module = design->module(module->name.str() + "_$abc9_flop");
		log_assert(box_module);
		for (auto port_name : module->ports) {
			auto port = module->wire(port_name);
			auto box_port = box_module->wire(port_name);
			if (box_port) {
				// Do not propagate init -- already captured by box
				box_port->attributes.erase(ID::init);
				continue;
			}
			log_assert(port->port_input);
			box_module->addWire(port_name, port);
			replace_cell->setPort(port_name, port);
		}
		box_module->fixup_ports();

		auto unmap_module = unmap_design->addModule(box_module->name);
		replace_cell = unmap_module->addCell(ID::_TECHMAP_REPLACE_, module->name);
		for (auto port_name : box_module->ports) {
			auto w = unmap_module->addWire(port_name, box_module->wire(port_name));
			if (module->wire(port_name))
				replace_cell->setPort(port_name, w);
		}
		unmap_module->ports = box_module->ports;
		unmap_module->check();
	}
}

void break_scc(RTLIL::Module *module)
{
	// For every unique SCC found, (arbitrarily) find the first
	//   cell in the component, and interrupt all its output connections
	//   with the $__ABC9_SCC_BREAKER cell

	// Do not break SCCs which have a cell instantiating an abc9_bypass-able
	// module (but which wouldn't have been bypassed)
	auto design = module->design;
	pool<RTLIL::Cell*> scc_cells;
	pool<RTLIL::Const> ids_seen;
	for (auto cell : module->cells()) {
		auto it = cell->attributes.find(ID::abc9_scc_id);
		if (it == cell->attributes.end())
			continue;
		scc_cells.insert(cell);
		auto inst_module = design->module(cell->type);
		if (inst_module && inst_module->has_attribute(ID::abc9_bypass))
			ids_seen.insert(it->second);
	}

	SigSpec I, O;
	for (auto cell : scc_cells) {
		auto it = cell->attributes.find(ID::abc9_scc_id);
		log_assert(it != cell->attributes.end());
		auto id = it->second;
		auto r = ids_seen.insert(id);
		cell->attributes.erase(it);
		// Cut exactly one representative cell per SCC id.
		if (!r.second)
			continue;
		for (auto &c : cell->connections_) {
			if (c.second.is_fully_const()) continue;
			if (cell->output(c.first)) {
				Wire *w = module->addWire(NEW_ID, GetSize(c.second));
				I.append(w);
				O.append(c.second);
				c.second = w;
			}
		}
	}

	if (!I.empty())
	{
		auto cell = module->addCell(NEW_ID, ID($__ABC9_SCC_BREAKER));
		log_assert(GetSize(I) == GetSize(O));
		cell->setParam(ID::WIDTH, GetSize(I));
		cell->setPort(ID::I, std::move(I));
		cell->setPort(ID::O, std::move(O));
	}
}

void prep_delays(RTLIL::Design *design, bool dff_mode)
{
	TimingInfo timing;

	// Derive all Yosys blackbox modules that are not combinatorial abc9 boxes
	//   (e.g. DSPs, RAMs, etc.) nor abc9 flops and collect all such instantiations
	std::vector<Cell*> cells;
	for (auto module : design->selected_modules()) {
		if (module->processes.size() > 0) {
			log("Skipping module %s as it contains processes.\n", module);
			continue;
		}

		for (auto cell : module->cells()) {
			if (cell->type.in(ID($_AND_), ID($_NOT_), ID($_DFF_N_), ID($_DFF_P_)))
				continue;
			log_assert(!cell->type.begins_with("$paramod$__ABC9_DELAY\\DELAY="));

			RTLIL::Module* inst_module = design->module(cell->type);
			if (!inst_module)
				continue;
			if (!inst_module->get_blackbox_attribute())
				continue;
			if (!cell->parameters.empty())
				continue;

			if (inst_module->get_bool_attribute(ID::abc9_box))
				continue;
			if (inst_module->get_bool_attribute(ID::abc9_bypass))
				continue;

			if (dff_mode && inst_module->get_bool_attribute(ID::abc9_flop)) {
				continue; 	// do not add $__ABC9_DELAY boxes to flops
						//   as delays will be captured in the flop box
			}

			if (!timing.count(cell->type))
				timing.setup_module(inst_module);

			cells.emplace_back(cell);
		}
	}

	// Insert $__ABC9_DELAY cells on all cells that instantiate blackboxes
	//   (or bypassed white-boxes with required times)
	dict<int, IdString> box_cache;
	Module *delay_module = design->module(ID($__ABC9_DELAY));
	log_assert(delay_module);
	for (auto cell : cells) {
		auto module = cell->module;
		auto inst_module = design->module(cell->type);
		log_assert(inst_module);

		for (auto &i : timing.at(cell->type).required) {
			auto port_wire = inst_module->wire(i.first.name);
			if (!port_wire)
				log_error("Port %s in cell %s (type %s) from module %s does not actually exist",
						i.first.name.unescape(), cell, cell->type.unescape(), module);
			log_assert(port_wire->port_input);

			auto d = i.second.first;
			if (d == 0)
				continue;

			auto offset = i.first.offset;
			if (!cell->hasPort(i.first.name))
				continue;
			auto rhs = cell->getPort(i.first.name);
			if (offset >= rhs.size())
				continue;
			auto O = module->addWire(NEW_ID);

#ifndef NDEBUG
			if (ys_debug(1)) {
				static pool<std::pair<IdString,TimingInfo::NameBit>> seen;
				if (seen.emplace(cell->type, i.first).second) log("%s.%s[%d] abc9_required = %d\n",
						cell->type.unescape(), i.first.name.unescape(), offset, d);
			}
#endif
			auto r = box_cache.insert(d);
			if (r.second) {
				r.first->second = delay_module->derive(design, {{ID::DELAY, d}});
				log_assert(r.first->second.begins_with("$paramod$__ABC9_DELAY\\DELAY="));
			}
			auto box = module->addCell(NEW_ID, r.first->second);
			box->setPort(ID::I, rhs[offset]);
			box->setPort(ID::O, O);
			rhs[offset] = O;
			cell->setPort(i.first.name, rhs);
		}
	}
}

void prep_xaiger(RTLIL::Module *module, bool dff)
{
	auto design = module->design;
	log_assert(design);

	SigMap sigmap(module);

	dict<IdString, std::vector<IdString>> box_ports;

	for (auto cell : module->cells()) {
		if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_)))
			continue;
		if (cell->has_keep_attr())
			continue;

		auto inst_module = design->module(cell->type);
		bool abc9_flop = inst_module && inst_module->get_bool_attribute(ID::abc9_flop);
		if (abc9_flop && !dff)
			continue;

		if (inst_module && inst_module->get_bool_attribute(ID::abc9_box)) {
			auto r = box_ports.insert(cell->type);
			if (r.second) {
				// Make carry in the last PI, and carry out the last PO
				//   since ABC requires it this way
				IdString carry_in, carry_out;
				for (const auto &port_name : inst_module->ports) {
					auto w = inst_module->wire(port_name);
					log_assert(w);
					if (w->get_bool_attribute(ID::abc9_carry)) {
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
	}

	if (box_ports.empty())
		return;

	// Build the same topo graph for the initial pass and the optional retry.
	auto build_toposort = [&](TopoSort<IdString, RTLIL::sort_by_id_str> &toposort) {
		dict<SigBit, pool<IdString>> bit_drivers, bit_users;

		for (auto cell : module->cells()) {
			if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_)))
				continue;
			if (cell->has_keep_attr())
				continue;

			auto inst_module = design->module(cell->type);
			bool abc9_flop = inst_module && inst_module->get_bool_attribute(ID::abc9_flop);
			if (abc9_flop && !dff)
				continue;
			if (!(inst_module && inst_module->get_bool_attribute(ID::abc9_box)) && !yosys_celltypes.cell_known(cell->type))
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

		// Build producer -> consumer edges on sigmapped nets.
		for (auto &it : bit_users)
			if (bit_drivers.count(it.first))
				for (auto driver_cell : bit_drivers.at(it.first))
					for (auto user_cell : it.second)
						toposort.edge(driver_cell, user_cell);
		if (ys_debug(1))
			toposort.analyze_loops = true;
		return toposort.sort();
	};

	// Build TopoSort in a container, as we may need to conditionally rebuild it on retry.
	std::optional<TopoSort<IdString, RTLIL::sort_by_id_str>> toposort;
	toposort.emplace();
	bool no_loops = build_toposort(toposort.value());

	// Fallback for residual loops after SCC cutting: insert additional
	// breakers on non-box loop cells, then re-run toposort checks.
	if (!no_loops) {
		SigSpec I, O;
		pool<IdString> broken_cells;

		for (auto &loop : toposort.value().loops)
			for (auto cell_name : loop) {
				// Loop reports can overlap; cut each cell at most once.
				if (!broken_cells.insert(cell_name).second)
					continue;
				auto cell = module->cell(cell_name);
				log_assert(cell);
				auto inst_module = design->module(cell->type);
				if (inst_module && inst_module->get_bool_attribute(ID::abc9_box))
					continue;
				for (auto &c : cell->connections_) {
					if (c.second.is_fully_const()) continue;
					if (cell->output(c.first)) {
						Wire *w = module->addWire(NEW_ID, GetSize(c.second));
						I.append(w);
						O.append(c.second);
						c.second = w;
					}
				}
			}

		if (!I.empty()) {
			auto cell = module->addCell(NEW_ID, ID($__ABC9_SCC_BREAKER));
			log_assert(GetSize(I) == GetSize(O));
			cell->setParam(ID::WIDTH, GetSize(I));
			cell->setPort(ID::I, std::move(I));
			cell->setPort(ID::O, std::move(O));

			// Rebuild topo ordering after inserting the additional breakers.
			toposort.emplace();
			no_loops = build_toposort(toposort.value());
		}
	}

	if (ys_debug(1)) {
		unsigned i = 0;
		for (auto &it : toposort.value().loops) {
			log("  loop %d\n", i++);
			for (auto cell_name : it) {
				auto cell = module->cell(cell_name);
				log_assert(cell);
				log("\t%s (%s @ %s)\n", cell, cell->type.unescape(), cell->get_src_attribute());
			}
		}
	}

	log_assert(no_loops);

	auto r = saved_designs.emplace("$abc9_holes", nullptr);
	if (r.second)
		r.first->second = new Design;
	RTLIL::Design *holes_design = r.first->second;
	log_assert(holes_design);
	RTLIL::Module *holes_module = holes_design->addModule(module->name);
	log_assert(holes_module);

	dict<IdString, Cell*> cell_cache;
	TimingInfo timing;

	int port_id = 1, box_count = 0;
	for (auto cell_name : toposort.value().sorted) {
		RTLIL::Cell *cell = module->cell(cell_name);
		log_assert(cell);

		RTLIL::Module* box_module = design->module(cell->type);
		if (!box_module)
			continue;
		if (!box_module->get_bool_attribute(ID::abc9_box))
			continue;
		if (!cell->parameters.empty())
		{
			// At this stage of the ABC9 flow, cells instantiating (* abc9_box *) modules must not contain any parameters -- instead it should
			// be instantiating the derived module which will have had any parameters constant-propagated.
			// This task is expected to be performed by `abc9_ops -prep_hier`, but it looks like it failed to do so for this design.
			// Please file a bug report!
			log_error("Not expecting parameters on cell '%s' instantiating module '%s' marked (* abc9_box *)\n", cell_name.unescape(), cell->type.unescape());
		}
		log_assert(box_module->get_blackbox_attribute());

		cell->attributes[ID::abc9_box_seq] = box_count++;

		auto r = cell_cache.insert(cell->type);
		auto &holes_cell = r.first->second;
		if (r.second) {
			if (box_module->get_bool_attribute(ID::whitebox)) {
				holes_cell = holes_module->addCell(NEW_ID, cell->type);

				if (box_module->has_processes())
					Pass::call_on_module(design, box_module, "proc -noopt");

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
						conn = holes_module->addWire(stringf("%s.%s", cell->type, port_name.unescape()), GetSize(w));
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
			Wire *holes_wire = holes_module->addWire(stringf("$abc%s.%s", cell->name, port_name.unescape()), GetSize(w));
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

void prep_lut(RTLIL::Design *design, int maxlut)
{
	TimingInfo timing;

	struct t_lut {
		IdString name;
		int area;
		std::vector<int> delays;
	};
	std::map<int,t_lut> table;
	for (auto module : design->modules()) {
		auto it = module->attributes.find(ID::abc9_lut);
		if (it == module->attributes.end())
			continue;

		auto &t = timing.setup_module(module);

		TimingInfo::NameBit o;
		std::vector<int> delays;
		for (const auto &i : t.comb) {
			auto &d = i.first.second;
			if (o == TimingInfo::NameBit())
				o = d;
			else if (o != d)
				log_error("Module '%s' with (* abc9_lut *) has more than one output.\n", module);
			delays.push_back(i.second);
		}

		if (GetSize(delays) == 0)
			log_error("Module '%s' with (* abc9_lut *) has no specify entries.\n", module);
		if (maxlut && GetSize(delays) > maxlut)
			continue;
		// ABC requires non-decreasing LUT input delays
		std::sort(delays.begin(), delays.end());

		int K = GetSize(delays);
		auto entry = t_lut{module->name, it->second.as_int(), std::move(delays)};
		auto r = table.emplace(K, entry);
		if (!r.second) {
			if (r.first->second.area != entry.area)
				log_error("Modules '%s' and '%s' have conflicting (* abc9_lut *) values.\n", module, r.first->second.name.unescape());
			if (r.first->second.delays != entry.delays)
				log_error("Modules '%s' and '%s' have conflicting specify entries.\n", module, r.first->second.name.unescape());
		}
	}

	if (table.empty())
		log_error("Design does not contain any modules with (* abc9_lut *).\n");

	std::stringstream ss;
	const auto &front = *table.begin();
	// If the first entry does not start from a 1-input LUT,
	//   (as ABC requires) crop the first entry to do so
	for (int i = 1; i < front.first; i++) {
		ss << "# $__ABC9_LUT" << i << std::endl;
		ss << i << " " << front.second.area;
		for (int j = 0; j < i; j++)
			ss << " " << front.second.delays[j];
		ss << std::endl;
	}
	for (const auto &i : table) {
		ss << "# " << i.second.name.unescape() << std::endl;
		ss << i.first << " " << i.second.area;
		for (const auto &j : i.second.delays)
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

void prep_box(RTLIL::Design *design)
{
	TimingInfo timing;

	int abc9_box_id = 1;
	std::stringstream ss;
	dict<IdString,std::vector<IdString>> box_ports;
	for (auto module : design->modules()) {
		auto it = module->attributes.find(ID::abc9_box);
		if (it == module->attributes.end())
			continue;
		bool box = it->second.as_bool();
		if (!box)
			continue;

		auto r = module->attributes.insert(ID::abc9_box_id);
		r.first->second = abc9_box_id++;

		if (module->get_bool_attribute(ID::abc9_flop)) {
			int num_inputs = 0, num_outputs = 0;
			for (auto port_name : module->ports) {
				auto wire = module->wire(port_name);
				log_assert(GetSize(wire) == 1);
				if (wire->port_input) num_inputs++;
				if (wire->port_output) num_outputs++;
			}
			log_assert(num_outputs == 1);

			ss << module->name.unescape() << " " << r.first->second.as_int();
			log_assert(module->get_bool_attribute(ID::whitebox));
			ss << " " << "1";
			ss << " " << num_inputs << " " << num_outputs << std::endl;

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
				ss << wire->name.unescape();
			}
			ss << std::endl;

			auto &t = timing.setup_module(module).required;
			if (t.empty())
				log_error("Module '%s' with (* abc9_flop *) has no clk-to-q timing (and thus no connectivity) information.\n", module);

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
					ss << it->second.first;

#ifndef NDEBUG
					if (ys_debug(1)) {
						static std::set<std::pair<IdString,IdString>> seen;
						if (seen.emplace(module->name, port_name).second) log("%s.%s abc9_required = %d\n", module,
								port_name.unescape(), it->second.first);
					}
#endif
				}
			}
			ss << " # $_DFF_[NP]_.D" << std::endl;
			ss << std::endl;
		}
		else {
			auto r2 = box_ports.insert(module->name);
			if (r2.second) {
				// Make carry in the last PI, and carry out the last PO
				//   since ABC requires it this way
				IdString carry_in, carry_out;
				for (const auto &port_name : module->ports) {
					auto w = module->wire(port_name);
					log_assert(w);
					if (w->get_bool_attribute(ID::abc9_carry)) {
						log_assert(w->port_input != w->port_output);
						if (w->port_input)
							carry_in = port_name;
						else if (w->port_output)
							carry_out = port_name;
					}
					else
						r2.first->second.push_back(port_name);
				}

				if (carry_in != IdString()) {
					r2.first->second.push_back(carry_in);
					r2.first->second.push_back(carry_out);
				}
			}

			std::vector<SigBit> inputs, outputs;
			for (auto port_name : r2.first->second) {
				auto wire = module->wire(port_name);
				if (wire->port_input)
					for (int i = 0; i < GetSize(wire); i++)
						inputs.emplace_back(wire, i);
				if (wire->port_output)
					for (int i = 0; i < GetSize(wire); i++)
						outputs.emplace_back(wire, i);
			}

			ss << module->name.unescape() << " " << module->attributes.at(ID::abc9_box_id).as_int();
			bool has_model = module->get_bool_attribute(ID::whitebox) || !module->get_bool_attribute(ID::blackbox);
			ss << " " << (has_model ? "1" : "0");
			ss << " " << GetSize(inputs) << " " << GetSize(outputs) << std::endl;

			bool first = true;
			ss << "#";
			for (const auto &i : inputs) {
				if (first)
					first = false;
				else
					ss << " ";
				if (GetSize(i.wire) == 1)
					ss << i.wire->name.unescape();
				else
					ss << i.wire->name.unescape() << "[" << i.offset << "]";
			}
			ss << std::endl;

			auto &t = timing.setup_module(module);
			if (t.comb.empty() && !outputs.empty() && !inputs.empty()) {
				log_error("Module '%s' with (* abc9_box *) has no timing (and thus no connectivity) information.\n", module);
			}

			for (const auto &o : outputs) {
				first = true;
				for (const auto &i : inputs) {
					if (first)
						first = false;
					else
						ss << " ";
					auto jt = t.comb.find(TimingInfo::BitBit(i,o));
					if (jt == t.comb.end())
						ss << "-";
					else
						ss << jt->second;
				}
				ss << " # ";
				if (GetSize(o.wire) == 1)
					ss << o.wire->name.unescape();
				else
					ss << o.wire->name.unescape() << "[" << o.offset << "]";
				ss << std::endl;
			}
			ss << std::endl;
		}
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


static void replace_zbufs(Design *design)
{
	design->bufNormalize(true);
	std::vector<Cell *> zbufs;

	for (auto mod : design->modules()) {
		zbufs.clear();
		for (auto cell : mod->cells()) {
			if (cell->type != ID($buf))
				continue;
			auto &sig = cell->getPort(ID::A);
			for (int i = 0; i < GetSize(sig); ++i) {
				if (sig[i] == State::Sz) {
					zbufs.push_back(cell);
					break;
				}
			}
		}

		for (auto cell : zbufs) {
			auto sig = cell->getPort(ID::A);
			for (int i = 0; i < GetSize(sig); ++i) {
				if (sig[i] == State::Sz) {
					Wire *w = mod->addWire(NEW_ID);
					Cell *ud = mod->addCell(NEW_ID, ID($tribuf));
					ud->set_bool_attribute(ID::aiger2_zbuf);
					ud->setParam(ID::WIDTH, 1);
					ud->setPort(ID::Y, w);
					ud->setPort(ID::EN, State::S0);
					ud->setPort(ID::A, State::S0);
					sig[i] = w;
				}
			}
			cell->setPort(ID::A, sig);
		}

		mod->bufNormalize();
	}
	design->bufNormalize(false);
}



static void restore_zbufs(Design *design)
{
	std::vector<Cell *> to_remove;

	for (auto mod : design->modules()) {
		to_remove.clear();
		for (auto cell : mod->cells())
			if (cell->type == ID($tribuf) && cell->has_attribute(ID(aiger2_zbuf)))
				to_remove.push_back(cell);

		for (auto cell : to_remove) {
			SigSpec sig_y = cell->getPort(ID::Y);
			mod->addBuf(NEW_ID, Const(State::Sz, GetSize(sig_y)), sig_y);
			mod->remove(cell);
		}
	}
}


struct Abc9OpsPass : public Pass {
	Abc9OpsPass() : Pass("abc9_ops", "helper functions for ABC9") { }
	void help() override
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
		log("        check that the design is valid, e.g. (* abc9_box_id *) values are\n");
		log("        unique, (* abc9_carry *) is only given for one input/output port, etc.\n");
		log("\n");
		log("    -prep_hier\n");
		log("        derive all used (* abc9_box *) or (* abc9_flop *) (if -dff option)\n");
		log("        whitebox modules. with (* abc9_flop *) modules, only those containing\n");
		log("        $dff/$_DFF_[NP]_ cells with zero initial state -- due to an ABC\n");
		log("        limitation -- will be derived.\n");
		log("\n");
		log("    -prep_bypass\n");
		log("        create techmap rules in the '$abc9_map' and '$abc9_unmap' designs for\n");
		log("        bypassing sequential (* abc9_box *) modules using a combinatorial box\n");
		log("        (named *_$abc9_byp). bypassing is necessary if sequential elements (e.g.\n");
		log("        $dff, $mem, etc.) are discovered inside so that any combinatorial paths\n");
		log("        will be correctly captured. this bypass box will only contain ports that\n");
		log("        are referenced by a simple path declaration ($specify2 cell) inside a\n");
		log("        specify block.\n");
		log("\n");
		log("    -prep_dff\n");
		log("        select all (* abc9_flop *) modules instantiated in the design and store\n");
		log("        in the named selection '$abc9_flops'.\n");
		log("\n");
		log("    -prep_dff_submod\n");
		log("        within (* abc9_flop *) modules, rewrite all edge-sensitive path\n");
		log("        declarations and $setup() timing checks ($specify3 and $specrule cells)\n");
		log("        that share a 'DST' port with the $_DFF_[NP]_.Q port from this 'Q' port\n");
		log("        to the DFF's 'D' port. this is to prepare such specify cells to be moved\n");
		log("        into the flop box.\n");
		log("\n");
		log("    -prep_dff_unmap\n");
		log("        populate the '$abc9_unmap' design with techmap rules for mapping\n");
		log("        *_$abc9_flop cells back into their derived cell types (where the rules\n");
		log("        created by -prep_hier will then map back to the original cell with\n");
		log("        parameters).\n");
		log("\n");
		log("    -prep_delays\n");
		log("        insert `$__ABC9_DELAY' blackbox cells into the design to account for\n");
		log("        certain required times.\n");
		log("\n");
		log("    -break_scc\n");
		log("        for an arbitrarily chosen cell in each unique SCC of each selected\n");
		log("        module (tagged with an (* abc9_scc_id = <int> *) attribute) interrupt\n");
		log("        all wires driven by this cell's outputs with a temporary\n");
		log("        $__ABC9_SCC_BREAKER cell to break the SCC.\n");
		log("\n");
		log("    -prep_xaiger\n");
		log("        prepare the design for XAIGER output. this includes computing the\n");
		log("        topological ordering of ABC9 boxes, as well as preparing the \n");
		log("        '$abc9_holes' design that contains the logic behaviour of ABC9\n");
		log("        whiteboxes.\n");
		log("\n");
		log("    -dff\n");
		log("        consider flop cells (those instantiating modules marked with\n");
		log("        (* abc9_flop *)) during -prep_{delays,xaiger,box}.\n");
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
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ABC9_OPS pass (helper functions for ABC9).\n");

		bool check_mode = false;
		bool prep_delays_mode = false;
		bool break_scc_mode = false;
		bool prep_hier_mode = false;
		bool prep_bypass_mode = false;
		bool prep_dff_mode = false, prep_dff_submod_mode = false, prep_dff_unmap_mode = false;
		bool prep_xaiger_mode = false;
		bool prep_lut_mode = false;
		bool prep_box_mode = false;
		bool replace_zbufs_mode = false;
		bool restore_zbufs_mode = false;
		bool dff_mode = false;
		std::string write_lut_dst;
		int maxlut = 0;
		std::string write_box_dst;

		bool valid = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-check") {
				check_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-break_scc") {
				break_scc_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-prep_hier") {
				prep_hier_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-prep_bypass") {
				prep_bypass_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-prep_dff") {
				prep_dff_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-prep_dff_submod") {
				prep_dff_submod_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-prep_dff_unmap") {
				prep_dff_unmap_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-prep_xaiger") {
				prep_xaiger_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-prep_delays") {
				prep_delays_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-prep_lut" && argidx+1 < args.size()) {
				prep_lut_mode = true;
				maxlut = atoi(args[++argidx].c_str());
				valid = true;
				continue;
			}
			if (arg == "-write_lut" && argidx+1 < args.size()) {
				write_lut_dst = args[++argidx];
				rewrite_filename(write_lut_dst);
				valid = true;
				continue;
			}
			if (arg == "-prep_box") {
				prep_box_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-write_box" && argidx+1 < args.size()) {
				write_box_dst = args[++argidx];
				rewrite_filename(write_box_dst);
				valid = true;
				continue;
			}
			if (arg == "-dff") {
				dff_mode = true;
				continue;
			}
			if (arg == "-replace_zbufs") {
				replace_zbufs_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-restore_zbufs") {
				restore_zbufs_mode = true;
				valid = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!valid)
			log_cmd_error("At least one of -check, -break_scc, -prep_{delays,xaiger,dff[123],lut,box}, -write_{lut,box}, -reintegrate, -{replace,restore}_zbufs must be specified.\n");

		if (dff_mode && !check_mode && !prep_hier_mode && !prep_delays_mode && !prep_xaiger_mode)
			log_cmd_error("'-dff' option is only relevant for -prep_{hier,delay,xaiger}.\n");

		if (replace_zbufs_mode)
			replace_zbufs(design);
		if (restore_zbufs_mode)
			restore_zbufs(design);
		if (check_mode)
			check(design, dff_mode);
		if (prep_hier_mode)
			prep_hier(design, dff_mode);
		if (prep_bypass_mode)
			prep_bypass(design);
		if (prep_dff_mode)
			prep_dff(design);
		if (prep_dff_submod_mode)
			prep_dff_submod(design);
		if (prep_dff_unmap_mode)
			prep_dff_unmap(design);
		if (prep_delays_mode)
			prep_delays(design, dff_mode);
		if (prep_lut_mode)
			prep_lut(design, maxlut);
		if (prep_box_mode)
			prep_box(design);

		for (auto mod : design->selected_modules()) {
			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", mod);
				continue;
			}

			if (!design->selected_whole_module(mod))
				log_error("Can't handle partially selected module %s!\n", mod);

			if (!write_lut_dst.empty())
				write_lut(mod, write_lut_dst);
			if (!write_box_dst.empty())
				write_box(mod, write_box_dst);
			if (break_scc_mode)
				break_scc(mod);
			if (prep_xaiger_mode)
				prep_xaiger(mod, dff_mode);
		}
	}
} Abc9OpsPass;

PRIVATE_NAMESPACE_END
