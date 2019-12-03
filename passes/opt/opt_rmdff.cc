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
#include "kernel/rtlil.h"
#include "kernel/satgen.h"
#include "kernel/sigtools.h"
#include <stdio.h>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

SigMap assign_map, dff_init_map;
SigSet<RTLIL::Cell*> mux_drivers;
dict<SigBit, RTLIL::Cell*> bit2driver;
dict<SigBit, pool<SigBit>> init_attributes;

bool keepdc;
bool sat;

void remove_init_attr(SigSpec sig)
{
	for (auto bit : assign_map(sig))
		if (init_attributes.count(bit))
			for (auto wbit : init_attributes.at(bit))
				wbit.wire->attributes.at(ID(init))[wbit.offset] = State::Sx;
}

bool handle_dffsr(RTLIL::Module *mod, RTLIL::Cell *cell)
{
	SigSpec sig_set, sig_clr;
	State pol_set, pol_clr;

	if (cell->hasPort(ID(S)))
		sig_set = cell->getPort(ID(S));

	if (cell->hasPort(ID(R)))
		sig_clr = cell->getPort(ID(R));

	if (cell->hasPort(ID(SET)))
		sig_set = cell->getPort(ID(SET));

	if (cell->hasPort(ID(CLR)))
		sig_clr = cell->getPort(ID(CLR));

	log_assert(GetSize(sig_set) == GetSize(sig_clr));

	if (cell->type.begins_with("$_DFFSR_")) {
		pol_set = cell->type[9] == 'P' ? State::S1 : State::S0;
		pol_clr = cell->type[10] == 'P' ? State::S1 : State::S0;
	} else
	if (cell->type.begins_with("$_DLATCHSR_")) {
		pol_set = cell->type[12] == 'P' ? State::S1 : State::S0;
		pol_clr = cell->type[13] == 'P' ? State::S1 : State::S0;
	} else
	if (cell->type.in(ID($dffsr), ID($dlatchsr))) {
		pol_set = cell->parameters[ID(SET_POLARITY)].as_bool() ? State::S1 : State::S0;
		pol_clr = cell->parameters[ID(CLR_POLARITY)].as_bool() ? State::S1 : State::S0;
	} else
		log_abort();

	State npol_set = pol_set == State::S0 ? State::S1 : State::S0;
	State npol_clr = pol_clr == State::S0 ? State::S1 : State::S0;

	SigSpec sig_d = cell->getPort(ID(D));
	SigSpec sig_q = cell->getPort(ID(Q));

	bool did_something = false;
	bool proper_sr = false;
	bool used_pol_set = false;
	bool used_pol_clr = false;
	bool hasreset = false;
	Const reset_val;
	SigSpec sig_reset;

	for (int i = 0; i < GetSize(sig_set); i++)
	{
		SigBit s = sig_set[i], c = sig_clr[i];

		if (s != npol_set || c != npol_clr)
			hasreset = true;

		if (s == pol_set || c == pol_clr)
		{
			log("Constantly %s Q bit %s for SR cell %s (%s) from module %s.\n",
					s == pol_set ? "set" : "cleared", log_signal(sig_q[i]),
					log_id(cell), log_id(cell->type), log_id(mod));

			remove_init_attr(sig_q[i]);
			mod->connect(sig_q[i], s == pol_set ? State::S1 : State::S0);
			sig_set.remove(i);
			sig_clr.remove(i);
			sig_d.remove(i);
			sig_q.remove(i--);
			did_something = true;
			continue;
		}
		if (sig_reset.empty() && s.wire != nullptr) sig_reset = s;
		if (sig_reset.empty() && c.wire != nullptr) sig_reset = c;

		if (s.wire != nullptr && s != sig_reset) proper_sr = true;
		if (c.wire != nullptr && c != sig_reset) proper_sr = true;

		if ((s.wire == nullptr) != (c.wire == nullptr)) {
			if (s.wire != nullptr) used_pol_set = true;
			if (c.wire != nullptr) used_pol_clr = true;
			reset_val.bits.push_back(c.wire == nullptr ? State::S1 : State::S0);
		} else
			proper_sr = true;
	}

	if (!hasreset)
		proper_sr = false;

	if (GetSize(sig_set) == 0)
	{
		log("Removing %s (%s) from module %s.\n", log_id(cell), log_id(cell->type), log_id(mod));
		mod->remove(cell);
		return true;
	}

	if (cell->type.in(ID($dffsr), ID($dlatchsr)))
	{
		cell->setParam(ID(WIDTH), GetSize(sig_d));
		cell->setPort(ID(SET), sig_set);
		cell->setPort(ID(CLR), sig_clr);
		cell->setPort(ID(D), sig_d);
		cell->setPort(ID(Q), sig_q);
	}
	else
	{
		cell->setPort(ID(S), sig_set);
		cell->setPort(ID(R), sig_clr);
		cell->setPort(ID(D), sig_d);
		cell->setPort(ID(Q), sig_q);
	}

	if (proper_sr)
		return did_something;

	if (used_pol_set && used_pol_clr && pol_set != pol_clr)
		return did_something;

	if (cell->type == ID($dlatchsr))
		return did_something;

	State unified_pol = used_pol_set ? pol_set : pol_clr;

	if (cell->type == ID($dffsr))
	{
		if (hasreset)
		{
			log("Converting %s (%s) to %s in module %s.\n", log_id(cell), log_id(cell->type), "$adff", log_id(mod));

			cell->type = ID($adff);
			cell->setParam(ID(ARST_POLARITY), unified_pol);
			cell->setParam(ID(ARST_VALUE), reset_val);
			cell->setPort(ID(ARST), sig_reset);

			cell->unsetParam(ID(SET_POLARITY));
			cell->unsetParam(ID(CLR_POLARITY));
			cell->unsetPort(ID(SET));
			cell->unsetPort(ID(CLR));
		}
		else
		{
			log("Converting %s (%s) to %s in module %s.\n", log_id(cell), log_id(cell->type), "$dff", log_id(mod));

			cell->type = ID($dff);
			cell->unsetParam(ID(SET_POLARITY));
			cell->unsetParam(ID(CLR_POLARITY));
			cell->unsetPort(ID(SET));
			cell->unsetPort(ID(CLR));
		}

		return true;
	}

	if (!hasreset)
	{
		IdString new_type;

		if (cell->type.begins_with("$_DFFSR_"))
			new_type = stringf("$_DFF_%c_", cell->type[8]);
		else if (cell->type.begins_with("$_DLATCHSR_"))
			new_type = stringf("$_DLATCH_%c_", cell->type[11]);
		else
			log_abort();

		log("Converting %s (%s) to %s in module %s.\n", log_id(cell), log_id(cell->type), log_id(new_type), log_id(mod));

		cell->type = new_type;
		cell->unsetPort(ID(S));
		cell->unsetPort(ID(R));

		return true;
	}

	return did_something;
}

bool handle_dlatch(RTLIL::Module *mod, RTLIL::Cell *dlatch)
{
	SigSpec sig_e;
	State on_state, off_state;

	if (dlatch->type == ID($dlatch)) {
		sig_e = assign_map(dlatch->getPort(ID(EN)));
		on_state = dlatch->getParam(ID(EN_POLARITY)).as_bool() ? State::S1 : State::S0;
		off_state = dlatch->getParam(ID(EN_POLARITY)).as_bool() ? State::S0 : State::S1;
	} else
	if (dlatch->type == ID($_DLATCH_P_)) {
		sig_e = assign_map(dlatch->getPort(ID(E)));
		on_state = State::S1;
		off_state = State::S0;
	} else
	if (dlatch->type == ID($_DLATCH_N_)) {
		sig_e = assign_map(dlatch->getPort(ID(E)));
		on_state = State::S0;
		off_state = State::S1;
	} else
		log_abort();

	if (sig_e == off_state)
	{
		RTLIL::Const val_init;
		for (auto bit : dff_init_map(dlatch->getPort(ID(Q))))
			val_init.bits.push_back(bit.wire == NULL ? bit.data : State::Sx);
		mod->connect(dlatch->getPort(ID(Q)), val_init);
		goto delete_dlatch;
	}

	if (sig_e == on_state)
	{
		mod->connect(dlatch->getPort(ID(Q)), dlatch->getPort(ID(D)));
		goto delete_dlatch;
	}

	return false;

delete_dlatch:
	log("Removing %s (%s) from module %s.\n", log_id(dlatch), log_id(dlatch->type), log_id(mod));
	remove_init_attr(dlatch->getPort(ID(Q)));
	mod->remove(dlatch);
	return true;
}

bool handle_dff(RTLIL::Module *mod, RTLIL::Cell *dff)
{
	RTLIL::SigSpec sig_d, sig_q, sig_c, sig_r, sig_e;
	RTLIL::Const val_cp, val_rp, val_rv, val_ep;

	if (dff->type == ID($_FF_)) {
		sig_d = dff->getPort(ID(D));
		sig_q = dff->getPort(ID(Q));
	}
	else if (dff->type == ID($_DFF_N_) || dff->type == ID($_DFF_P_)) {
		sig_d = dff->getPort(ID(D));
		sig_q = dff->getPort(ID(Q));
		sig_c = dff->getPort(ID(C));
		val_cp = RTLIL::Const(dff->type == ID($_DFF_P_), 1);
	}
	else if (dff->type.begins_with("$_DFF_") && dff->type.compare(9, 1, "_") == 0 &&
			(dff->type[6] == 'N' || dff->type[6] == 'P') &&
			(dff->type[7] == 'N' || dff->type[7] == 'P') &&
			(dff->type[8] == '0' || dff->type[8] == '1')) {
		sig_d = dff->getPort(ID(D));
		sig_q = dff->getPort(ID(Q));
		sig_c = dff->getPort(ID(C));
		sig_r = dff->getPort(ID(R));
		val_cp = RTLIL::Const(dff->type[6] == 'P', 1);
		val_rp = RTLIL::Const(dff->type[7] == 'P', 1);
		val_rv = RTLIL::Const(dff->type[8] == '1', 1);
	}
	else if (dff->type.begins_with("$_DFFE_") && dff->type.compare(9, 1, "_") == 0 &&
			(dff->type[7] == 'N' || dff->type[7] == 'P') &&
			(dff->type[8] == 'N' || dff->type[8] == 'P')) {
		sig_d = dff->getPort(ID(D));
		sig_q = dff->getPort(ID(Q));
		sig_c = dff->getPort(ID(C));
		sig_e = dff->getPort(ID(E));
		val_cp = RTLIL::Const(dff->type[7] == 'P', 1);
		val_ep = RTLIL::Const(dff->type[8] == 'P', 1);
	}
	else if (dff->type == ID($ff)) {
		sig_d = dff->getPort(ID(D));
		sig_q = dff->getPort(ID(Q));
	}
	else if (dff->type == ID($dff)) {
		sig_d = dff->getPort(ID(D));
		sig_q = dff->getPort(ID(Q));
		sig_c = dff->getPort(ID(CLK));
		val_cp = RTLIL::Const(dff->parameters[ID(CLK_POLARITY)].as_bool(), 1);
	}
	else if (dff->type == ID($dffe)) {
		sig_e = dff->getPort(ID(EN));
		sig_d = dff->getPort(ID(D));
		sig_q = dff->getPort(ID(Q));
		sig_c = dff->getPort(ID(CLK));
		val_cp = RTLIL::Const(dff->parameters[ID(CLK_POLARITY)].as_bool(), 1);
		val_ep = RTLIL::Const(dff->parameters[ID(EN_POLARITY)].as_bool(), 1);
	}
	else if (dff->type == ID($adff)) {
		sig_d = dff->getPort(ID(D));
		sig_q = dff->getPort(ID(Q));
		sig_c = dff->getPort(ID(CLK));
		sig_r = dff->getPort(ID(ARST));
		val_cp = RTLIL::Const(dff->parameters[ID(CLK_POLARITY)].as_bool(), 1);
		val_rp = RTLIL::Const(dff->parameters[ID(ARST_POLARITY)].as_bool(), 1);
		val_rv = dff->parameters[ID(ARST_VALUE)];
	}
	else
		log_abort();

	assign_map.apply(sig_d);
	assign_map.apply(sig_q);
	assign_map.apply(sig_c);
	assign_map.apply(sig_r);

	bool has_init = false;
	RTLIL::Const val_init;
	for (auto bit : dff_init_map(sig_q).to_sigbit_vector()) {
		if (bit.wire == NULL || keepdc)
			has_init = true;
		val_init.bits.push_back(bit.wire == NULL ? bit.data : RTLIL::State::Sx);
	}

	if (dff->type.in(ID($ff), ID($dff)) && mux_drivers.has(sig_d)) {
		std::set<RTLIL::Cell*> muxes;
		mux_drivers.find(sig_d, muxes);
		for (auto mux : muxes) {
			RTLIL::SigSpec sig_a = assign_map(mux->getPort(ID::A));
			RTLIL::SigSpec sig_b = assign_map(mux->getPort(ID::B));
			if (sig_a == sig_q && sig_b.is_fully_const() && (!has_init || val_init == sig_b.as_const())) {
				mod->connect(sig_q, sig_b);
				goto delete_dff;
			}
			if (sig_b == sig_q && sig_a.is_fully_const() && (!has_init || val_init == sig_a.as_const())) {
				mod->connect(sig_q, sig_a);
				goto delete_dff;
			}
		}
	}

	// If clock is driven by a constant and (i) no reset signal
	//                                      (ii) Q has no initial value
	//                                      (iii) initial value is same as reset value
	if (!sig_c.empty() && sig_c.is_fully_const() && (!sig_r.size() || !has_init || val_init == val_rv)) {
		if (val_rv.bits.size() == 0)
			val_rv = val_init;
		// Q is permanently reset value or initial value
		mod->connect(sig_q, val_rv);
		goto delete_dff;
	}

	// If D is fully undefined and reset signal present and (i) Q has no initial value
	//                                                     (ii) initial value is same as reset value
	if (sig_d.is_fully_undef() && sig_r.size() && (!has_init || val_init == val_rv)) {
		// Q is permanently reset value
		mod->connect(sig_q, val_rv);
		goto delete_dff;
	}

	// If D is fully undefined and no reset signal and Q has an initial value
	if (sig_d.is_fully_undef() && !sig_r.size() && has_init) {
		// Q is permanently initial value
		mod->connect(sig_q, val_init);
		goto delete_dff;
	}

	// If D is fully constant and (i) no reset signal
	//                            (ii) reset value is same as constant D
	//                        and (a) has no initial value
	//                            (b) initial value same as constant D
	if (sig_d.is_fully_const() && (!sig_r.size() || val_rv == sig_d.as_const()) && (!has_init || val_init == sig_d.as_const())) {
		// Q is permanently D
		mod->connect(sig_q, sig_d);
		goto delete_dff;
	}

	// If D input is same as Q output and (i) no reset signal
	//                                    (ii) no initial signal
	//                                    (iii) initial value is same as reset value
	if (sig_d == sig_q && (sig_r.empty() || !has_init || val_init == val_rv)) {
		// Q is permanently reset value or initial value
		if (sig_r.size())
			mod->connect(sig_q, val_rv);
		else if (has_init)
			mod->connect(sig_q, val_init);
		goto delete_dff;
	}

	// If reset signal is present, and is fully constant
	if (!sig_r.empty() && sig_r.is_fully_const())
	{
		// If reset value is permanently active or if reset is undefined
		if (sig_r == val_rp || sig_r.is_fully_undef()) {
			// Q is permanently reset value
			mod->connect(sig_q, val_rv);
			goto delete_dff;
		}

		log("Removing unused reset from %s (%s) from module %s.\n", log_id(dff), log_id(dff->type), log_id(mod));

		if (dff->type == ID($adff)) {
			dff->type = ID($dff);
			dff->unsetPort(ID(ARST));
			dff->unsetParam(ID(ARST_POLARITY));
			dff->unsetParam(ID(ARST_VALUE));
			return true;
		}

		log_assert(dff->type.begins_with("$_DFF_"));
		dff->type = stringf("$_DFF_%c_", + dff->type[6]);
		dff->unsetPort(ID(R));
	}

	// If enable signal is present, and is fully constant
	if (!sig_e.empty() && sig_e.is_fully_const())
	{
		// If enable value is permanently inactive
		if (sig_e != val_ep) {
			// Q is permanently initial value
			mod->connect(sig_q, val_init);
			goto delete_dff;
		}

		log("Removing unused enable from %s (%s) from module %s.\n", log_id(dff), log_id(dff->type), log_id(mod));

		if (dff->type == ID($dffe)) {
			dff->type = ID($dff);
			dff->unsetPort(ID(EN));
			dff->unsetParam(ID(EN_POLARITY));
			return true;
		}

		log_assert(dff->type.begins_with("$_DFFE_"));
		dff->type = stringf("$_DFF_%c_", + dff->type[7]);
		dff->unsetPort(ID(E));
	}

	if (sat && has_init && (!sig_r.size() || val_init == val_rv))
	{
		bool removed_sigbits = false;

		ezSatPtr ez;
		SatGen satgen(ez.get(), &assign_map);
		pool<Cell*> sat_cells;

		std::function<void(Cell*)> sat_import_cell = [&](Cell *c) {
			if (!sat_cells.insert(c).second)
				return;
			if (!satgen.importCell(c))
				return;
			for (auto &conn : c->connections()) {
				if (!c->input(conn.first))
					continue;
				for (auto bit : assign_map(conn.second))
					if (bit2driver.count(bit))
						sat_import_cell(bit2driver.at(bit));
			}
		};

		// For each register bit, try to prove that it cannot change from the initial value. If so, remove it
		for (int position = 0; position < GetSize(sig_d); position += 1) {
			RTLIL::SigBit q_sigbit = sig_q[position];
			RTLIL::SigBit d_sigbit = sig_d[position];

			if ((!q_sigbit.wire) || (!d_sigbit.wire))
				continue;

			if (!bit2driver.count(d_sigbit))
				continue;

			sat_import_cell(bit2driver.at(d_sigbit));

			RTLIL::State sigbit_init_val = val_init[position];
			if (sigbit_init_val != State::S0 && sigbit_init_val != State::S1)
				continue;

			int init_sat_pi = satgen.importSigSpec(sigbit_init_val).front();
			int q_sat_pi = satgen.importSigBit(q_sigbit);
			int d_sat_pi = satgen.importSigBit(d_sigbit);

			// Try to find out whether the register bit can change under some circumstances
			bool counter_example_found = ez->solve(ez->IFF(q_sat_pi, init_sat_pi), ez->NOT(ez->IFF(d_sat_pi, init_sat_pi)));

			// If the register bit cannot change, we can replace it with a constant
			if (!counter_example_found)
			{
				log("Setting constant %d-bit at position %d on %s (%s) from module %s.\n", sigbit_init_val ? 1 : 0,
						position, log_id(dff), log_id(dff->type), log_id(mod));

				SigSpec tmp = dff->getPort(ID(D));
				tmp[position] = sigbit_init_val;
				dff->setPort(ID(D), tmp);

				removed_sigbits = true;
			}
		}

		if (removed_sigbits) {
			handle_dff(mod, dff);
			return true;
		}
	}


	return false;

delete_dff:
	log("Removing %s (%s) from module %s.\n", log_id(dff), log_id(dff->type), log_id(mod));
	remove_init_attr(dff->getPort(ID(Q)));
	mod->remove(dff);

	for (auto &entry : bit2driver)
		if (entry.second == dff)
			bit2driver.erase(entry.first);

	return true;
}

struct OptRmdffPass : public Pass {
	OptRmdffPass() : Pass("opt_rmdff", "remove DFFs with constant inputs") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_rmdff [-keepdc] [-sat] [selection]\n");
		log("\n");
		log("This pass identifies flip-flops with constant inputs and replaces them with\n");
		log("a constant driver.\n");
		log("\n");
		log("    -sat\n");
		log("        additionally invoke SAT solver to detect and remove flip-flops (with \n");
		log("        non-constant inputs) that can also be replaced with a constant driver\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		int total_count = 0, total_initdrv = 0;
		log_header(design, "Executing OPT_RMDFF pass (remove dff with constant values).\n");

		keepdc = false;
		sat = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-keepdc") {
				keepdc = true;
				continue;
			}
			if (args[argidx] == "-sat") {
				sat = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			pool<SigBit> driven_bits;
			dict<SigBit, State> init_bits;

			assign_map.set(module);
			dff_init_map.set(module);
			mux_drivers.clear();
			bit2driver.clear();
			init_attributes.clear();

			for (auto wire : module->wires())
			{
				if (wire->attributes.count(ID(init)) != 0) {
					Const initval = wire->attributes.at(ID(init));
					for (int i = 0; i < GetSize(initval) && i < GetSize(wire); i++)
						if (initval[i] == State::S0 || initval[i] == State::S1)
							dff_init_map.add(SigBit(wire, i), initval[i]);
					for (int i = 0; i < GetSize(wire); i++) {
						SigBit wire_bit(wire, i), mapped_bit = assign_map(wire_bit);
						if (mapped_bit.wire) {
							init_attributes[mapped_bit].insert(wire_bit);
							if (i < GetSize(initval))
								init_bits[mapped_bit] = initval[i];
						}
					}
				}

				if (wire->port_input) {
					for (auto bit : assign_map(wire))
						driven_bits.insert(bit);
				}
			}

			std::vector<RTLIL::IdString> dff_list;
			std::vector<RTLIL::IdString> dffsr_list;
			std::vector<RTLIL::IdString> dlatch_list;
			for (auto cell : module->cells())
			{
				for (auto &conn : cell->connections()) {
					bool is_output = cell->output(conn.first);
					if (is_output || !cell->known())
						for (auto bit : assign_map(conn.second)) {
							if (is_output)
								bit2driver[bit] = cell;
							driven_bits.insert(bit);
						}
				}

				if (cell->type.in(ID($mux), ID($pmux))) {
					if (cell->getPort(ID::A).size() == cell->getPort(ID::B).size())
						mux_drivers.insert(assign_map(cell->getPort(ID::Y)), cell);
					continue;
				}

				if (!design->selected(module, cell))
					continue;

				if (cell->type.in(ID($_DFFSR_NNN_), ID($_DFFSR_NNP_), ID($_DFFSR_NPN_), ID($_DFFSR_NPP_),
						ID($_DFFSR_PNN_), ID($_DFFSR_PNP_), ID($_DFFSR_PPN_), ID($_DFFSR_PPP_), ID($dffsr),
						ID($_DLATCHSR_NNN_), ID($_DLATCHSR_NNP_), ID($_DLATCHSR_NPN_), ID($_DLATCHSR_NPP_),
						ID($_DLATCHSR_PNN_), ID($_DLATCHSR_PNP_), ID($_DLATCHSR_PPN_), ID($_DLATCHSR_PPP_), ID($dlatchsr)))
					dffsr_list.push_back(cell->name);

				if (cell->type.in(ID($_FF_), ID($_DFF_N_), ID($_DFF_P_),
						ID($_DFF_NN0_), ID($_DFF_NN1_), ID($_DFF_NP0_), ID($_DFF_NP1_),
						ID($_DFF_PN0_), ID($_DFF_PN1_), ID($_DFF_PP0_), ID($_DFF_PP1_),
						ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_),
						ID($ff), ID($dff), ID($dffe), ID($adff)))
					dff_list.push_back(cell->name);

				if (cell->type.in(ID($dlatch), ID($_DLATCH_P_), ID($_DLATCH_N_)))
					dlatch_list.push_back(cell->name);
			}

			for (auto &id : dffsr_list) {
				if (module->cell(id) != nullptr &&
						handle_dffsr(module, module->cells_[id]))
					total_count++;
			}

			for (auto &id : dff_list) {
				if (module->cell(id) != nullptr &&
						handle_dff(module, module->cells_[id]))
					total_count++;
			}

			for (auto &id : dlatch_list) {
				if (module->cell(id) != nullptr &&
						handle_dlatch(module, module->cells_[id]))
					total_count++;
			}

			SigSpec const_init_sigs;

			for (auto bit : init_bits)
				if (!driven_bits.count(bit.first))
					const_init_sigs.append(bit.first);

			const_init_sigs.sort_and_unify();

			for (SigSpec sig : const_init_sigs.chunks())
			{
				Const val;

				for (auto bit : sig)
					val.bits.push_back(init_bits.at(bit));

				log("Promoting init spec %s = %s to constant driver in module %s.\n",
						log_signal(sig), log_signal(val), log_id(module));

				module->connect(sig, val);
				remove_init_attr(sig);
				total_initdrv++;
			}
		}

		assign_map.clear();
		mux_drivers.clear();
		bit2driver.clear();
		init_attributes.clear();

		if (total_count || total_initdrv)
			design->scratchpad_set_bool("opt.did_something", true);

		if (total_initdrv)
			log("Promoted %d init specs to constant drivers.\n", total_initdrv);

		if (total_count)
			log("Replaced %d DFF cells.\n", total_count);
	}
} OptRmdffPass;

PRIVATE_NAMESPACE_END
