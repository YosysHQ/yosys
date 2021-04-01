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
						log_id(m), id, log_id(r.first->second));
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
		pool<IdString> processed;
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
					log_error("Module '%s' with (* abc9_flop *) is a blackbox.\n", log_id(derived_type));

				if (derived_module->has_processes())
					Pass::call_on_module(design, derived_module, "proc");

				bool found = false;
				for (auto derived_cell : derived_module->cells()) {
					if (derived_cell->type.in(ID($dff), ID($_DFF_N_), ID($_DFF_P_))) {
						if (found)
							log_error("Whitebox '%s' with (* abc9_flop *) contains more than one $_DFF_[NP]_ cell.\n", log_id(derived_module));
						found = true;

						SigBit Q = derived_cell->getPort(ID::Q);
						log_assert(GetSize(Q.wire) == 1);

						if (!Q.wire->port_output)
							log_error("Whitebox '%s' with (* abc9_flop *) contains a %s cell where its 'Q' port does not drive a module output.\n", log_id(derived_module), log_id(derived_cell->type));

						Const init = Q.wire->attributes.at(ID::init, State::Sx);
						log_assert(GetSize(init) == 1);
					}
					else if (unsupported.count(derived_cell->type))
						log_error("Whitebox '%s' with (* abc9_flop *) contains a %s cell, which is not supported for sequential synthesis.\n", log_id(derived_module), log_id(derived_cell->type));
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

	static const pool<IdString> seq_types{
		ID($dff), ID($dffsr), ID($adff),
		ID($dlatch), ID($dlatchsr), ID($sr),
		ID($mem),
		ID($_DFF_N_), ID($_DFF_P_),
		ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
		ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_),
		ID($_DFF_N_), ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
		ID($_DFF_P_), ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_),
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
				// Check potential for any one of those three
				//   (since its value may depend on a parameter, but not its existence)
				if (!inst_module->has_attribute(ID::abc9_flop) && !inst_module->has_attribute(ID::abc9_box) && !inst_module->get_bool_attribute(ID::abc9_bypass))
					continue;
				derived_type = inst_module->derive(design, cell->parameters);
				derived_module = design->module(derived_type);
			}

			if (derived_module->get_bool_attribute(ID::abc9_flop)) {
				if (!dff_mode)
					continue;
			}
			else {
				if (!derived_module->get_bool_attribute(ID::abc9_box) && !derived_module->get_bool_attribute(ID::abc9_bypass))
					continue;
			}

			if (!unmap_design->module(derived_type)) {
				if (derived_module->has_processes())
					Pass::call_on_module(design, derived_module, "proc");

				if (derived_module->get_bool_attribute(ID::abc9_flop)) {
					for (auto derived_cell : derived_module->cells())
						if (derived_cell->type.in(ID($dff), ID($_DFF_N_), ID($_DFF_P_))) {
							SigBit Q = derived_cell->getPort(ID::Q);
							Const init = Q.wire->attributes.at(ID::init, State::Sx);
							log_assert(GetSize(init) == 1);

							// Block sequential synthesis on cells with (* init *) != 1'b0
							//   because ABC9 doesn't support them
							if (init != State::S0) {
								log_warning("Whitebox '%s' with (* abc9_flop *) contains a %s cell with non-zero initial state -- this is not supported for ABC9 sequential synthesis. Treating as a blackbox.\n", log_id(derived_module), log_id(derived_cell->type));
								derived_module->set_bool_attribute(ID::abc9_flop, false);
							}
							break;
						}
				}
				else if (derived_module->get_bool_attribute(ID::abc9_box)) {
					for (auto derived_cell : derived_module->cells())
						if (seq_types.count(derived_cell->type)) {
							derived_module->set_bool_attribute(ID::abc9_box, false);
							derived_module->set_bool_attribute(ID::abc9_bypass);
							break;
						}
				}

				if (derived_type != cell->type) {
					auto unmap_module = unmap_design->addModule(derived_type);
					for (auto port : derived_module->ports) {
						auto w = unmap_module->addWire(port, derived_module->wire(port));
						// Do not propagate (* init *) values into the box,
						//   in fact, remove it from outside too
						if (w->port_output)
							w->attributes.erase(ID::init);
					}
					unmap_module->ports = derived_module->ports;
					unmap_module->check();

					auto replace_cell = unmap_module->addCell(ID::_TECHMAP_REPLACE_, cell->type);
					for (const auto &conn : cell->connections()) {
						auto w = unmap_module->wire(conn.first);
						log_assert(w);
						replace_cell->setPort(conn.first, w);
					}
					replace_cell->parameters = cell->parameters;
				}
			}

			cell->type = derived_type;
			cell->parameters.clear();
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
		}
}

void prep_dff(RTLIL::Design *design)
{
	auto r = design->selection_vars.insert(std::make_pair(ID($abc9_flops), RTLIL::Selection(false)));
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
			log_assert(cell->parameters.empty());
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
			log("Skipping module %s as it contains processes.\n", log_id(module));
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

		auto &t = timing.at(cell->type).required;
		for (auto &conn : cell->connections_) {
			auto port_wire = inst_module->wire(conn.first);
			if (!port_wire)
				log_error("Port %s in cell %s (type %s) from module %s does not actually exist",
						log_id(conn.first), log_id(cell), log_id(cell->type), log_id(module));
			if (!port_wire->port_input)
				continue;
			if (conn.second.is_fully_const())
				continue;

			SigSpec O = module->addWire(NEW_ID, GetSize(conn.second));
			for (int i = 0; i < GetSize(conn.second); i++) {
				auto d = t.at(TimingInfo::NameBit(conn.first,i), 0);
				if (d == 0)
					continue;

#ifndef NDEBUG
				if (ys_debug(1)) {
					static std::set<std::tuple<IdString,IdString,int>> seen;
					if (seen.emplace(cell->type, conn.first, i).second) log("%s.%s[%d] abc9_required = %d\n",
							log_id(cell->type), log_id(conn.first), i, d);
				}
#endif
				auto r = box_cache.insert(d);
				if (r.second) {
					r.first->second = delay_module->derive(design, {{ID::DELAY, d}});
					log_assert(r.first->second.begins_with("$paramod$__ABC9_DELAY\\DELAY="));
				}
				auto box = module->addCell(NEW_ID, r.first->second);
				box->setPort(ID::I, conn.second[i]);
				box->setPort(ID::O, O[i]);
				conn.second[i] = O[i];
			}
		}
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

	bool no_loops = toposort.sort();

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
	for (auto cell_name : toposort.sorted) {
		RTLIL::Cell *cell = module->cell(cell_name);
		log_assert(cell);

		RTLIL::Module* box_module = design->module(cell->type);
		if (!box_module)
			continue;
		if (!box_module->get_bool_attribute(ID::abc9_box))
			continue;
		if (!cell->parameters.empty())
		{
		    // At this stage of the ABC9 flow, all modules must be nonparametric, because ABC itself requires concrete netlists, and the presence of
		    // parameters implies a non-concrete netlist. This means an (* abc9_box *) parametric module but due to a bug somewhere this hasn't been
		    // uniquified into a concrete parameter-free module. This is a bug, and a bug report would be welcomed.
		    log_error("Not expecting parameters on module '%s'  marked (* abc9_box *)\n", log_id(cell_name));
		}
		log_assert(box_module->get_blackbox_attribute());

		cell->attributes[ID::abc9_box_seq] = box_count++;

		auto r = cell_cache.insert(cell->type);
		auto &holes_cell = r.first->second;
		if (r.second) {
			if (box_module->get_bool_attribute(ID::whitebox)) {
				holes_cell = holes_module->addCell(cell->name, cell->type);

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
						conn = holes_module->addWire(stringf("%s.%s", cell->type.c_str(), log_id(port_name)), GetSize(w));
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
				log_error("Module '%s' with (* abc9_lut *) has more than one output.\n", log_id(module));
			delays.push_back(i.second);
		}

		if (GetSize(delays) == 0)
			log_error("Module '%s' with (* abc9_lut *) has no specify entries.\n", log_id(module));
		if (maxlut && GetSize(delays) > maxlut)
			continue;
		// ABC requires non-decreasing LUT input delays
		std::sort(delays.begin(), delays.end());

		int K = GetSize(delays);
		auto entry = t_lut{module->name, it->second.as_int(), std::move(delays)};
		auto r = table.emplace(K, entry);
		if (!r.second) {
			if (r.first->second.area != entry.area)
				log_error("Modules '%s' and '%s' have conflicting (* abc9_lut *) values.\n", log_id(module), log_id(r.first->second.name));
			if (r.first->second.delays != entry.delays)
				log_error("Modules '%s' and '%s' have conflicting specify entries.\n", log_id(module), log_id(r.first->second.name));
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
		ss << "# " << log_id(i.second.name) << std::endl;
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

	std::stringstream ss;
	int abc9_box_id = 1;
	for (auto module : design->modules()) {
		auto it = module->attributes.find(ID::abc9_box_id);
		if (it == module->attributes.end())
			continue;
		abc9_box_id = std::max(abc9_box_id, it->second.as_int());
	}

	dict<IdString,std::vector<IdString>> box_ports;
	for (auto module : design->modules()) {
		auto it = module->attributes.find(ID::abc9_box);
		if (it == module->attributes.end())
			continue;
		bool box = it->second.as_bool();
		module->attributes.erase(it);
		if (!box)
			continue;

		auto r = module->attributes.insert(ID::abc9_box_id);
		if (!r.second)
			continue;
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

			ss << log_id(module) << " " << r.first->second.as_int();
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
				ss << log_id(wire);
			}
			ss << std::endl;

			auto &t = timing.setup_module(module).required;
			if (t.empty())
				log_error("Module '%s' with (* abc9_flop *) has no clk-to-q timing (and thus no connectivity) information.\n", log_id(module));

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
					// Assume no connectivity if no setup time
					ss << "-";
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

			ss << log_id(module) << " " << module->attributes.at(ID::abc9_box_id).as_int();
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

			auto &t = timing.setup_module(module);
			if (t.comb.empty())
				log_error("Module '%s' with (* abc9_box *) has no timing (and thus no connectivity) information.\n", log_id(module));

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
					ss << log_id(o.wire);
				else
					ss << log_id(o.wire) << "[" << o.offset << "]";
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

void reintegrate(RTLIL::Module *module, bool dff_mode)
{
	auto design = module->design;
	log_assert(design);

	map_autoidx = autoidx++;

	RTLIL::Module *mapped_mod = design->module(stringf("%s$abc9", module->name.c_str()));
	if (mapped_mod == NULL)
		log_error("ABC output file does not contain a module `%s$abc'.\n", log_id(module));

	for (auto w : mapped_mod->wires()) {
		auto nw = module->addWire(remap_name(w->name), GetSize(w));
		nw->start_offset = w->start_offset;
		// Remove all (* init *) since they only exist on $_DFF_[NP]_
		w->attributes.erase(ID::init);
	}

	dict<IdString,std::vector<IdString>> box_ports;

	for (auto m : design->modules()) {
		if (!m->attributes.count(ID::abc9_box_id))
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

	SigMap initmap;
	if (dff_mode) {
		// Build a sigmap prioritising bits with (* init *)
		initmap.set(module);
		for (auto w : module->wires()) {
			auto it = w->attributes.find(ID::init);
			if (it == w->attributes.end())
				continue;
			for (auto i = 0; i < GetSize(w); i++)
				if (it->second[i] == State::S0 || it->second[i] == State::S1)
					initmap.add(w);
		}
	}

	std::vector<Cell*> boxes;
	for (auto cell : module->cells().to_vector()) {
		if (cell->has_keep_attr())
			continue;

		// Short out (so that existing name can be preserved) and remove
		//   $_DFF_[NP]_ cells since flop box already has all the information
		//   we need to reconstruct them
		if (dff_mode && cell->type.in(ID($_DFF_N_), ID($_DFF_P_)) && !cell->get_bool_attribute(ID::abc9_keep)) {
			SigBit Q = cell->getPort(ID::Q);
			module->connect(Q, cell->getPort(ID::D));
			module->remove(cell);
			auto Qi = initmap(Q);
			auto it = Qi.wire->attributes.find(ID::init);
			if (it != Qi.wire->attributes.end())
				it->second[Qi.offset] = State::Sx;
		}
		else if (cell->type.in(ID($_AND_), ID($_NOT_)))
			module->remove(cell);
		else if (cell->attributes.erase(ID::abc9_box_seq))
			boxes.emplace_back(cell);
	}

	dict<SigBit, pool<IdString>> bit_drivers, bit_users;
	TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
	dict<RTLIL::Cell*,RTLIL::Cell*> not2drivers;
	dict<SigBit, std::vector<RTLIL::Cell*>> bit2sinks;

	std::map<IdString, int> cell_stats;
	for (auto mapped_cell : mapped_mod->cells())
	{
		// Short out $_FF_ cells since the flop box already has
		//   all the information we need to reconstruct cell
		if (dff_mode && mapped_cell->type == ID($_FF_)) {
			SigBit D = mapped_cell->getPort(ID::D);
			SigBit Q = mapped_cell->getPort(ID::Q);
			if (D.wire)
				D.wire = module->wires_.at(remap_name(D.wire->name));
			Q.wire = module->wires_.at(remap_name(Q.wire->name));
			module->connect(Q, D);
			continue;
		}

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

		if (mapped_cell->type == ID($lut)) {
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

			if (existing_cell->type.begins_with("$paramod$__ABC9_DELAY\\DELAY=")) {
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
			log_assert(existing_cell->parameters.empty());
			log_assert(mapped_cell->type == stringf("$__boxid%d", box_module->attributes.at(ID::abc9_box_id).as_int()));
			mapped_cell->type = existing_cell->type;

			RTLIL::Cell *cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
			cell->parameters = existing_cell->parameters;
			cell->attributes = existing_cell->attributes;
			module->swap_names(cell, existing_cell);

			auto jt = mapped_cell->connections_.find(ID(i));
			log_assert(jt != mapped_cell->connections_.end());
			SigSpec inputs = std::move(jt->second);
			mapped_cell->connections_.erase(jt);
			jt = mapped_cell->connections_.find(ID(o));
			log_assert(jt != mapped_cell->connections_.end());
			SigSpec outputs = std::move(jt->second);
			mapped_cell->connections_.erase(jt);

			auto abc9_flop = box_module->get_bool_attribute(ID::abc9_flop);
			if (abc9_flop) {
				// Link this sole flop box output to the output of the existing
				//   flop box, so that any (public) signal it drives will be
				//   preserved
				SigBit old_q;
				for (const auto &port_name : box_ports.at(existing_cell->type)) {
					RTLIL::Wire *w = box_module->wire(port_name);
					log_assert(w);
					if (!w->port_output)
						continue;
					log_assert(old_q == SigBit());
					log_assert(GetSize(w) == 1);
					old_q = existing_cell->getPort(port_name);
				}
				auto new_q = outputs[0];
				new_q.wire = module->wires_.at(remap_name(new_q.wire->name));
				module->connect(old_q,  new_q);
			}
			else {
				for (const auto &i : inputs)
					bit_users[i].insert(mapped_cell->name);
				for (const auto &i : outputs)
					// Ignore inouts for topo ordering
					if (i.wire && !(i.wire->port_input && i.wire->port_output))
						bit_drivers[i].insert(mapped_cell->name);
			}

			int input_count = 0, output_count = 0;
			for (const auto &port_name : box_ports.at(existing_cell->type)) {
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

				if (w->port_input && !abc9_flop)
					for (const auto &i : newsig)
						bit2sinks[i].push_back(cell);

				cell->setPort(port_name, std::move(newsig));
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

		RTLIL::Wire *remap_wire = module->wire(remap_name(port));
		RTLIL::SigSpec signal(wire, remap_wire->start_offset-wire->start_offset, GetSize(remap_wire));
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
	// Instead of just mapping those $_NOT_ gates into 1-input $lut-s
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
	bool no_loops = toposort.sort();
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
			RTLIL::Const mask = sink_cell->getParam(ID::LUT);
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
			sink_cell->setParam(ID::LUT, mask);
		}

		// Since we have rewritten all sinks (which we know
		// to be only LUTs) to be after the inverter, we can
		// go ahead and clone the LUT with the expectation
		// that the original driving LUT will become dangling
		// and get cleaned away
clone_lut:
		driver_mask = driver_lut->getParam(ID::LUT);
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
		log("        check that the design is valid, e.g. (* abc9_box_id *) values are unique,\n");
		log("        (* abc9_carry *) is only given for one input/output port, etc.\n");
		log("\n");
		log("    -prep_hier\n");
		log("        derive all used (* abc9_box *) or (* abc9_flop *) (if -dff option)\n");
		log("        whitebox modules. with (* abc9_flop *) modules, only those containing\n");
		log("        $dff/$_DFF_[NP]_ cells with zero initial state -- due to an ABC limitation\n");
		log("        -- will be derived.\n");
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
		log("        that share a 'DST' port with the $_DFF_[NP]_.Q port from this 'Q' port to\n");
		log("        the DFF's 'D' port. this is to prepare such specify cells to be moved\n");
		log("        into the flop box.\n");
		log("\n");
		log("    -prep_dff_unmap\n");
		log("        populate the '$abc9_unmap' design with techmap rules for mapping *_$abc9_flop\n");
		log("        cells back into their derived cell types (where the rules created by\n");
		log("        -prep_hier will then map back to the original cell with parameters).\n");
		log("\n");
		log("    -prep_delays\n");
		log("        insert `$__ABC9_DELAY' blackbox cells into the design to account for\n");
		log("        certain required times.\n");
		log("\n");
		log("    -break_scc\n");
		log("        for an arbitrarily chosen cell in each unique SCC of each selected module\n");
		log("        (tagged with an (* abc9_scc_id = <int> *) attribute) interrupt all wires\n");
		log("        driven by this cell's outputs with a temporary $__ABC9_SCC_BREAKER cell\n");
		log("        to break the SCC.\n");
		log("\n");
		log("    -prep_xaiger\n");
		log("        prepare the design for XAIGER output. this includes computing the\n");
		log("        topological ordering of ABC9 boxes, as well as preparing the '$abc9_holes'\n");
		log("        design that contains the logic behaviour of ABC9 whiteboxes.\n");
		log("\n");
		log("    -dff\n");
		log("        consider flop cells (those instantiating modules marked with (* abc9_flop *))\n");
		log("        during -prep_{delays,xaiger,box}.\n");
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
		bool reintegrate_mode = false;
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
			if (arg == "-reintegrate") {
				reintegrate_mode = true;
				valid = true;
				continue;
			}
			if (arg == "-dff") {
				dff_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!valid)
			log_cmd_error("At least one of -check, -break_scc, -prep_{delays,xaiger,dff[123],lut,box}, -write_{lut,box}, -reintegrate must be specified.\n");

		if (dff_mode && !check_mode && !prep_hier_mode && !prep_delays_mode && !prep_xaiger_mode && !reintegrate_mode)
			log_cmd_error("'-dff' option is only relevant for -prep_{hier,delay,xaiger} or -reintegrate.\n");

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
				log("Skipping module %s as it contains processes.\n", log_id(mod));
				continue;
			}

			if (!design->selected_whole_module(mod))
				log_error("Can't handle partially selected module %s!\n", log_id(mod));

			if (!write_lut_dst.empty())
				write_lut(mod, write_lut_dst);
			if (!write_box_dst.empty())
				write_box(mod, write_box_dst);
			if (break_scc_mode)
				break_scc(mod);
			if (prep_xaiger_mode)
				prep_xaiger(mod, dff_mode);
			if (reintegrate_mode)
				reintegrate(mod, dff_mode);
		}
	}
} Abc9OpsPass;

PRIVATE_NAMESPACE_END
