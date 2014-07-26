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

// [[CITE]]
// Yiqiong Shi; Chan Wai Ting; Bah-Hwee Gwee; Ye Ren, "A highly efficient method for extracting FSMs from flattened gate-level netlist,"
// Circuits and Systems (ISCAS), Proceedings of 2010 IEEE International Symposium on , vol., no., pp.2610,2613, May 30 2010-June 2 2010
// doi: 10.1109/ISCAS.2010.5537093

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/celltypes.h"
#include "fsmdata.h"

static RTLIL::Module *module;
static SigMap assign_map;
typedef std::pair<std::string, std::string> sig2driver_entry_t;
static SigSet<sig2driver_entry_t> sig2driver, sig2trigger;

static bool find_states(RTLIL::SigSpec sig, const RTLIL::SigSpec &dff_out, RTLIL::SigSpec &ctrl, std::map<RTLIL::Const, int> &states, RTLIL::Const *reset_state = NULL)
{
	sig.extend(dff_out.size(), false);

	if (sig == dff_out)
		return true;

	assign_map.apply(sig);
	if (sig.is_fully_const()) {
		if (states.count(sig.as_const()) == 0) {
			log("  found state code: %s\n", log_signal(sig));
			states[sig.as_const()] = -1;
		}
		return true;
	}

	std::set<sig2driver_entry_t> cellport_list;
	sig2driver.find(sig, cellport_list);
	for (auto &cellport : cellport_list) {
		RTLIL::Cell *cell = module->cells.at(cellport.first);
		if ((cell->type != "$mux" && cell->type != "$pmux" && cell->type != "$safe_pmux") || cellport.second != "\\Y") {
			log("  unexpected cell type %s (%s) found in state selection tree.\n", cell->type.c_str(), cell->name.c_str());
			return false;
		}
		RTLIL::SigSpec sig_a = assign_map(cell->get("\\A"));
		RTLIL::SigSpec sig_b = assign_map(cell->get("\\B"));
		RTLIL::SigSpec sig_s = assign_map(cell->get("\\S"));
		if (reset_state && RTLIL::SigSpec(*reset_state).is_fully_undef())
			do {
				if (sig_a.is_fully_def())
					*reset_state = sig_a.as_const();
				else if (sig_b.is_fully_def())
					*reset_state = sig_b.as_const();
				else
					break;
				log("  found reset state: %s (guessed from mux tree)\n", log_signal(*reset_state));
			} while (0);
		if (ctrl.extract(sig_s).size() == 0) {
			log("  found ctrl input: %s\n", log_signal(sig_s));
			ctrl.append(sig_s);
		}
		if (!find_states(sig_a, dff_out, ctrl, states))
			return false;
		for (int i = 0; i < sig_b.size()/sig_a.size(); i++) {
			if (!find_states(sig_b.extract(i*sig_a.size(), sig_a.size()), dff_out, ctrl, states))
				return false;
		}
	}

	return true;
}

static RTLIL::Const sig2const(ConstEval &ce, RTLIL::SigSpec sig, RTLIL::State noconst_state, RTLIL::SigSpec dont_care = RTLIL::SigSpec())
{
	if (dont_care.size() > 0) {
		for (int i = 0; i < SIZE(sig); i++)
			if (dont_care.extract(sig[i]).size() > 0)
				sig[i] = noconst_state;
	}

	ce.assign_map.apply(sig);
	ce.values_map.apply(sig);

	for (int i = 0; i < SIZE(sig); i++)
		if (sig[i].wire != NULL)
			sig[i] = noconst_state;

	return sig.as_const();
}

static void find_transitions(ConstEval &ce, ConstEval &ce_nostop, FsmData &fsm_data, std::map<RTLIL::Const, int> &states, int state_in, RTLIL::SigSpec ctrl_in, RTLIL::SigSpec ctrl_out, RTLIL::SigSpec dff_in, RTLIL::SigSpec dont_care)
{
	RTLIL::SigSpec undef, constval;

	if (ce.eval(ctrl_out, undef) && ce.eval(dff_in, undef)) {
		assert(ctrl_out.is_fully_const() && dff_in.is_fully_const());
		FsmData::transition_t tr;
		tr.state_in = state_in;
		tr.state_out = states[ce.values_map(ce.assign_map(dff_in)).as_const()];
		tr.ctrl_in = sig2const(ce, ctrl_in, RTLIL::State::Sa, dont_care);
		tr.ctrl_out = sig2const(ce, ctrl_out, RTLIL::State::Sx);
		RTLIL::Const log_state_in = RTLIL::Const(RTLIL::State::Sx, fsm_data.state_bits);
		if (state_in >= 0)
			log_state_in = fsm_data.state_table[tr.state_in];
		if (dff_in.is_fully_def()) {
			fsm_data.transition_table.push_back(tr);
			log("  transition: %10s %s -> %10s %s\n",
					log_signal(log_state_in), log_signal(tr.ctrl_in),
					log_signal(fsm_data.state_table[tr.state_out]), log_signal(tr.ctrl_out));
		} else {
			log("  transition: %10s %s -> %10s %s  <ignored undef transistion!>\n",
					log_signal(log_state_in), log_signal(tr.ctrl_in),
					log_signal(fsm_data.state_table[tr.state_out]), log_signal(tr.ctrl_out));
		}
		return;
	}

	log_assert(undef.size() > 0);
	log_assert(ce.stop_signals.check_all(undef));

	undef = undef.extract(0, 1);
	constval = undef;

	if (ce_nostop.eval(constval))
	{
		ce.push();
		dont_care.append(undef);
		ce.set(undef, constval.as_const());
		find_transitions(ce, ce_nostop, fsm_data, states, state_in, ctrl_in, ctrl_out, dff_in, dont_care);
		ce.pop();
	}
	else
	{
		ce.push(), ce_nostop.push();
		ce.set(undef, RTLIL::Const(0, 1));
		ce_nostop.set(undef, RTLIL::Const(0, 1));
		find_transitions(ce, ce_nostop, fsm_data, states, state_in, ctrl_in, ctrl_out, dff_in, dont_care);
		ce.pop(), ce_nostop.pop();

		ce.push(), ce_nostop.push();
		ce.set(undef, RTLIL::Const(1, 1));
		ce_nostop.set(undef, RTLIL::Const(1, 1));
		find_transitions(ce, ce_nostop, fsm_data, states, state_in, ctrl_in, ctrl_out, dff_in, dont_care);
		ce.pop(), ce_nostop.pop();
	}
}

static void extract_fsm(RTLIL::Wire *wire)
{
	log("Extracting FSM `%s' from module `%s'.\n", wire->name.c_str(), module->name.c_str());

	// get input and output signals for state ff 

	RTLIL::SigSpec dff_out = assign_map(RTLIL::SigSpec(wire));
	RTLIL::SigSpec dff_in(RTLIL::State::Sm, wire->width);
	RTLIL::Const reset_state(RTLIL::State::Sx, wire->width);

	RTLIL::SigSpec clk = RTLIL::SigSpec(0, 1);
	RTLIL::SigSpec arst = RTLIL::SigSpec(0, 1);
	bool clk_polarity = true;
	bool arst_polarity = true;

	std::set<sig2driver_entry_t> cellport_list;
	sig2driver.find(dff_out, cellport_list);
	for (auto &cellport : cellport_list) {
		RTLIL::Cell *cell = module->cells.at(cellport.first);
		if ((cell->type != "$dff" && cell->type != "$adff") || cellport.second != "\\Q")
			continue;
		log("  found %s cell for state register: %s\n", cell->type.c_str(), cell->name.c_str());
		RTLIL::SigSpec sig_q = assign_map(cell->get("\\Q"));
		RTLIL::SigSpec sig_d = assign_map(cell->get("\\D"));
		clk = cell->get("\\CLK");
		clk_polarity = cell->parameters["\\CLK_POLARITY"].as_bool();
		if (cell->type == "$adff") {
			arst = cell->get("\\ARST");
			arst_polarity = cell->parameters["\\ARST_POLARITY"].as_bool();
			reset_state = cell->parameters["\\ARST_VALUE"];
		}
		sig_q.replace(dff_out, sig_d, &dff_in);
		break;
	}

	log("  root of input selection tree: %s\n", log_signal(dff_in));
	if (dff_in.has_marked_bits()) {
		log("  fsm extraction failed: incomplete input selection tree root.\n");
		return;
	}

	// find states and control inputs

	RTLIL::SigSpec ctrl_in;
	std::map<RTLIL::Const, int> states;
	if (!arst.is_fully_const()) {
		log("  found reset state: %s (from async reset)\n", log_signal(reset_state));
		states[reset_state] = -1;
	}
	if (!find_states(dff_in, dff_out, ctrl_in, states, &reset_state)) {
		log("  fsm extraction failed: state selection tree is not closed.\n");
		return;
	}

	// find control outputs
	// (add the state signals to the list of control outputs. if everything goes right, this signals
	// become unused and can then be removed from the fsm control output)

	RTLIL::SigSpec ctrl_out = dff_in;
	cellport_list.clear();
	sig2trigger.find(dff_out, cellport_list);
	for (auto &cellport : cellport_list) {
		RTLIL::Cell *cell = module->cells.at(cellport.first);
		RTLIL::SigSpec sig_a = assign_map(cell->get("\\A"));
		RTLIL::SigSpec sig_b = assign_map(cell->get("\\B"));
		RTLIL::SigSpec sig_y = assign_map(cell->get("\\Y"));
		if (cellport.second == "\\A" && !sig_b.is_fully_const())
			continue;
		if (cellport.second == "\\B" && !sig_a.is_fully_const())
			continue;
		log("  found ctrl output: %s\n", log_signal(sig_y));
		ctrl_out.append(sig_y);
	}
	ctrl_in.remove(ctrl_out);

	ctrl_in.sort_and_unify();
	ctrl_out.sort_and_unify();

	log("  ctrl inputs: %s\n", log_signal(ctrl_in));
	log("  ctrl outputs: %s\n", log_signal(ctrl_out));

	// Initialize fsm data struct

	FsmData fsm_data;
	fsm_data.num_inputs = ctrl_in.size();
	fsm_data.num_outputs = ctrl_out.size();
	fsm_data.state_bits = wire->width;
	fsm_data.reset_state = -1;
	for (auto &it : states) {
		it.second = fsm_data.state_table.size();
		fsm_data.state_table.push_back(it.first);
	}
	if (!arst.is_fully_const() || RTLIL::SigSpec(reset_state).is_fully_def())
		fsm_data.reset_state = states[reset_state];

	// Create transition table

	ConstEval ce(module), ce_nostop(module);
	ce.stop(ctrl_in);
	for (int state_idx = 0; state_idx < int(fsm_data.state_table.size()); state_idx++) {
		ce.push(), ce_nostop.push();
		ce.set(dff_out, fsm_data.state_table[state_idx]);
		ce_nostop.set(dff_out, fsm_data.state_table[state_idx]);
		find_transitions(ce, ce_nostop, fsm_data, states, state_idx, ctrl_in, ctrl_out, dff_in, RTLIL::SigSpec());
		ce.pop(), ce_nostop.pop();
	}

	// create fsm cell

	RTLIL::Cell *fsm_cell = module->addCell(stringf("$fsm$%s$%d", wire->name.c_str(), RTLIL::autoidx++), "$fsm");
	fsm_cell->set("\\CLK", clk);
	fsm_cell->set("\\ARST", arst);
	fsm_cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity ? 1 : 0, 1);
	fsm_cell->parameters["\\ARST_POLARITY"] = RTLIL::Const(arst_polarity ? 1 : 0, 1);
	fsm_cell->set("\\CTRL_IN", ctrl_in);
	fsm_cell->set("\\CTRL_OUT", ctrl_out);
	fsm_cell->parameters["\\NAME"] = RTLIL::Const(wire->name);
	fsm_cell->attributes = wire->attributes;
	fsm_data.copy_to_cell(fsm_cell);

	// rename original state wire

	module->wires.erase(wire->name);
	wire->attributes.erase("\\fsm_encoding");
	wire->name = stringf("$fsm$oldstate%s", wire->name.c_str());
	module->wires[wire->name] = wire;

	// unconnect control outputs from old drivers

	cellport_list.clear();
	sig2driver.find(ctrl_out, cellport_list);
	for (auto &cellport : cellport_list) {
		RTLIL::Cell *cell = module->cells.at(cellport.first);
		RTLIL::SigSpec port_sig = assign_map(cell->connections()[cellport.second]);
		RTLIL::SigSpec unconn_sig = port_sig.extract(ctrl_out);
		RTLIL::Wire *unconn_wire = new RTLIL::Wire;
		unconn_wire->name = stringf("$fsm_unconnect$%s$%d", log_signal(unconn_sig), RTLIL::autoidx++);
		unconn_wire->width = unconn_sig.size();
		module->wires[unconn_wire->name] = unconn_wire;
		port_sig.replace(unconn_sig, RTLIL::SigSpec(unconn_wire), &cell->connections()[cellport.second]);
	}
}

struct FsmExtractPass : public Pass {
	FsmExtractPass() : Pass("fsm_extract", "extracting FSMs in design") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm_extract [selection]\n");
		log("\n");
		log("This pass operates on all signals marked as FSM state signals using the\n");
		log("'fsm_encoding' attribute. It consumes the logic that creates the state signal\n");
		log("and uses the state signal to generate control signal and replaces it with an\n");
		log("FSM cell.\n");
		log("\n");
		log("The generated FSM cell still generates the original state signal with its\n");
		log("original encoding. The 'fsm_opt' pass can be used in combination with the\n");
		log("'opt_clean' pass to eliminate this signal.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing FSM_EXTRACT pass (extracting FSM from design).\n");
		extra_args(args, 1, design);

		CellTypes ct;
		ct.setup_internals();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();

		for (auto &mod_it : design->modules)
		{
			if (!design->selected(mod_it.second))
				continue;

			module = mod_it.second;
			assign_map.set(module);

			sig2driver.clear();
			sig2trigger.clear();
			for (auto &cell_it : module->cells)
				for (auto &conn_it : cell_it.second->connections()) {
					if (ct.cell_output(cell_it.second->type, conn_it.first) || !ct.cell_known(cell_it.second->type)) {
						RTLIL::SigSpec sig = conn_it.second;
						assign_map.apply(sig);
						sig2driver.insert(sig, sig2driver_entry_t(cell_it.first, conn_it.first));
					}
					if (ct.cell_input(cell_it.second->type, conn_it.first) && cell_it.second->connections().count("\\Y") > 0 &&
							cell_it.second->get("\\Y").size() == 1 && (conn_it.first == "\\A" || conn_it.first == "\\B")) {
						RTLIL::SigSpec sig = conn_it.second;
						assign_map.apply(sig);
						sig2trigger.insert(sig, sig2driver_entry_t(cell_it.first, conn_it.first));
					}
				}

			std::vector<RTLIL::Wire*> wire_list;
			for (auto &wire_it : module->wires)
				if (wire_it.second->attributes.count("\\fsm_encoding") > 0 && wire_it.second->attributes["\\fsm_encoding"].decode_string() != "none")
					if (design->selected(module, wire_it.second))
						wire_list.push_back(wire_it.second);
			for (auto wire : wire_list)
				extract_fsm(wire);
		}

		assign_map.clear();
		sig2driver.clear();
		sig2trigger.clear();
	}
} FsmExtractPass;
 
