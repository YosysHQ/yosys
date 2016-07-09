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

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/celltypes.h"
#include "fsmdata.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static RTLIL::Module *module;
static SigMap assign_map;
typedef std::pair<RTLIL::Cell*, RTLIL::IdString> sig2driver_entry_t;
static SigSet<sig2driver_entry_t> sig2driver, sig2user;
static std::set<RTLIL::Cell*> muxtree_cells;
static SigPool sig_at_port;

static bool check_state_mux_tree(RTLIL::SigSpec old_sig, RTLIL::SigSpec sig, pool<Cell*> &recursion_monitor)
{
	if (sig.is_fully_const() || old_sig == sig) {
		return true;
	}

	if (sig_at_port.check_any(assign_map(sig))) {
		return false;
	}

	std::set<sig2driver_entry_t> cellport_list;
	sig2driver.find(sig, cellport_list);
	for (auto &cellport : cellport_list)
	{
		if ((cellport.first->type != "$mux" && cellport.first->type != "$pmux") || cellport.second != "\\Y") {
			return false;
		}

		if (recursion_monitor.count(cellport.first)) {
			log_warning("logic loop in mux tree at signal %s in module %s.\n",
					log_signal(sig), RTLIL::id2cstr(module->name));
			return false;
		}

		recursion_monitor.insert(cellport.first);

		RTLIL::SigSpec sig_a = assign_map(cellport.first->getPort("\\A"));
		RTLIL::SigSpec sig_b = assign_map(cellport.first->getPort("\\B"));

		if (!check_state_mux_tree(old_sig, sig_a, recursion_monitor)) {
			recursion_monitor.erase(cellport.first);
			return false;
		}

		for (int i = 0; i < sig_b.size(); i += sig_a.size())
			if (!check_state_mux_tree(old_sig, sig_b.extract(i, sig_a.size()), recursion_monitor)) {
				recursion_monitor.erase(cellport.first);
				return false;
			}

		recursion_monitor.erase(cellport.first);
		muxtree_cells.insert(cellport.first);
	}

	return true;
}

static bool check_state_users(RTLIL::SigSpec sig)
{
	if (sig_at_port.check_any(assign_map(sig)))
		return false;

	std::set<sig2driver_entry_t> cellport_list;
	sig2user.find(sig, cellport_list);
	for (auto &cellport : cellport_list) {
		RTLIL::Cell *cell = cellport.first;
		if (muxtree_cells.count(cell) > 0)
			continue;
		if (cell->type == "$logic_not" && assign_map(cell->getPort("\\A")) == sig)
			continue;
		if (cellport.second != "\\A" && cellport.second != "\\B")
			return false;
		if (!cell->hasPort("\\A") || !cell->hasPort("\\B") || !cell->hasPort("\\Y"))
			return false;
		for (auto &port_it : cell->connections())
			if (port_it.first != "\\A" && port_it.first != "\\B" && port_it.first != "\\Y")
				return false;
		if (assign_map(cell->getPort("\\A")) == sig && cell->getPort("\\B").is_fully_const())
			continue;
		if (assign_map(cell->getPort("\\B")) == sig && cell->getPort("\\A").is_fully_const())
			continue;
		return false;
	}

	return true;
}

static void detect_fsm(RTLIL::Wire *wire)
{
	bool has_fsm_encoding_attr = wire->attributes.count("\\fsm_encoding") > 0 && wire->attributes.at("\\fsm_encoding").decode_string() != "none";
	bool has_fsm_encoding_none = wire->attributes.count("\\fsm_encoding") > 0 && wire->attributes.at("\\fsm_encoding").decode_string() == "none";
	bool has_init_attr = wire->attributes.count("\\init") > 0;
	bool is_module_port = sig_at_port.check_any(assign_map(RTLIL::SigSpec(wire)));
	bool looks_like_state_reg = false, looks_like_good_state_reg = false;
	bool is_self_resetting = false;

	if (has_fsm_encoding_none)
		return;

	if (wire->width <= 1) {
		if (has_fsm_encoding_attr) {
			log_warning("Removing fsm_encoding attribute from 1-bit net: %s.%s\n", log_id(wire->module), log_id(wire));
			wire->attributes.erase("\\fsm_encoding");
		}
		return;
	}

	std::set<sig2driver_entry_t> cellport_list;
	sig2driver.find(RTLIL::SigSpec(wire), cellport_list);

	for (auto &cellport : cellport_list)
	{
		if ((cellport.first->type != "$dff" && cellport.first->type != "$adff") || cellport.second != "\\Q")
			continue;

		muxtree_cells.clear();
		pool<Cell*> recursion_monitor;
		RTLIL::SigSpec sig_q = assign_map(cellport.first->getPort("\\Q"));
		RTLIL::SigSpec sig_d = assign_map(cellport.first->getPort("\\D"));

		if (sig_q != assign_map(wire))
			continue;

		looks_like_state_reg = check_state_mux_tree(sig_q, sig_d, recursion_monitor);
		looks_like_good_state_reg = check_state_users(sig_q);

		if (!looks_like_state_reg)
			break;

		ConstEval ce(wire->module);

		std::set<sig2driver_entry_t> cellport_list;
		sig2user.find(sig_q, cellport_list);

		for (auto &cellport : cellport_list)
		{
			RTLIL::Cell *cell = cellport.first;
			bool set_output = false, clr_output = false;

			if (cell->type == "$ne")
				set_output = true;

			if (cell->type == "$eq")
				clr_output = true;

			if (!set_output && !clr_output) {
				clr_output = true;
				for (auto &port_it : cell->connections())
					if (port_it.first != "\\A" || port_it.first != "\\Y")
						clr_output = false;
			}

			if (set_output || clr_output) {
				for (auto &port_it : cell->connections())
					if (cell->output(port_it.first)) {
						SigSpec sig = assign_map(port_it.second);
						Const val(set_output ? State::S1 : State::S0, GetSize(sig)); 
						ce.set(sig, val);
					}
			}
		}

		SigSpec sig_y = sig_d, sig_undef;
		if (ce.eval(sig_y, sig_undef))
			is_self_resetting = true;
	}

	if (has_fsm_encoding_attr)
	{
		vector<string> warnings;

		if (is_module_port)
			warnings.push_back("Forcing fsm recoding on module port might result in larger circuit.\n");

		if (!looks_like_good_state_reg)
			warnings.push_back("Users of state reg look like fsm recoding might result in larger circuit.\n");

		if (has_init_attr)
			warnings.push_back("Init value on fsm state registers are ignored. Possible simulation-synthesis mismatch!");

		if (!looks_like_state_reg)
			warnings.push_back("Doesn't look like a proper FSM. Possible simulation-synthesis mismatch!\n");

		if (is_self_resetting)
			warnings.push_back("FSM seems to be self-resetting. Possible simulation-synthesis mismatch!\n");

		if (!warnings.empty()) {
			string warnmsg = stringf("Regarding the user-specified fsm_encoding attribute on %s.%s:\n", log_id(wire->module), log_id(wire));
			for (auto w : warnings) warnmsg += "    " + w;
			log_warning("%s", warnmsg.c_str());
		} else {
			log("FSM state register %s.%s already has fsm_encoding attribute.\n", log_id(wire->module), log_id(wire)); 
		}
	}
	else
	if (looks_like_state_reg && looks_like_good_state_reg && !has_init_attr && !is_module_port && !is_self_resetting)
	{
		log("Found FSM state register %s.%s.\n", log_id(wire->module), log_id(wire));
		wire->attributes["\\fsm_encoding"] = RTLIL::Const("auto");
	}
	else
	if (looks_like_state_reg)
	{
		log("Not marking %s.%s as FSM state register:\n", log_id(wire->module), log_id(wire));

		if (is_module_port)
			log("    Register is connected to module port.\n");

		if (!looks_like_good_state_reg)
			log("    Users of register don't seem to benefit from recoding.\n");

		if (has_init_attr)
			log("    Register has an initialization value.");

		if (is_self_resetting)
			log("    Circuit seems to be self-resetting.\n");
	}
}

struct FsmDetectPass : public Pass {
	FsmDetectPass() : Pass("fsm_detect", "finding FSMs in design") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm_detect [selection]\n");
		log("\n");
		log("This pass detects finite state machines by identifying the state signal.\n");
		log("The state signal is then marked by setting the attribute 'fsm_encoding'\n");
		log("on the state signal to \"auto\".\n");
		log("\n");
		log("Existing 'fsm_encoding' attributes are not changed by this pass.\n");
		log("\n");
		log("Signals can be protected from being detected by this pass by setting the\n");
		log("'fsm_encoding' attribute to \"none\".\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing FSM_DETECT pass (finding FSMs in design).\n");
		extra_args(args, 1, design);

		CellTypes ct;
		ct.setup_internals();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();

		for (auto &mod_it : design->modules_)
		{
			if (!design->selected(mod_it.second))
				continue;

			module = mod_it.second;
			assign_map.set(module);

			sig2driver.clear();
			sig2user.clear();
			sig_at_port.clear();
			for (auto &cell_it : module->cells_)
				for (auto &conn_it : cell_it.second->connections()) {
					if (ct.cell_output(cell_it.second->type, conn_it.first) || !ct.cell_known(cell_it.second->type)) {
						RTLIL::SigSpec sig = conn_it.second;
						assign_map.apply(sig);
						sig2driver.insert(sig, sig2driver_entry_t(cell_it.second, conn_it.first));
					}
					if (!ct.cell_known(cell_it.second->type) || ct.cell_input(cell_it.second->type, conn_it.first)) {
						RTLIL::SigSpec sig = conn_it.second;
						assign_map.apply(sig);
						sig2user.insert(sig, sig2driver_entry_t(cell_it.second, conn_it.first));
					}
				}

			for (auto &wire_it : module->wires_)
				if (wire_it.second->port_id != 0)
					sig_at_port.add(assign_map(RTLIL::SigSpec(wire_it.second)));

			for (auto &wire_it : module->wires_)
				if (design->selected(module, wire_it.second))
					detect_fsm(wire_it.second);
		}

		assign_map.clear();
		sig2driver.clear();
		sig2user.clear();
		muxtree_cells.clear();
	}
} FsmDetectPass;

PRIVATE_NAMESPACE_END
