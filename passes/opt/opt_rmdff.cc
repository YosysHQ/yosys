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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

SigMap assign_map, dff_init_map;
SigSet<RTLIL::Cell*> mux_drivers;
dict<SigBit, pool<SigBit>> init_attributes;
bool keepdc;

void remove_init_attr(SigSpec sig)
{
	for (auto bit : assign_map(sig))
		if (init_attributes.count(bit))
			for (auto wbit : init_attributes.at(bit))
				wbit.wire->attributes.at("\\init")[wbit.offset] = State::Sx;
}

bool handle_dlatch(RTLIL::Module *mod, RTLIL::Cell *dlatch)
{
	SigSpec sig_e = dlatch->getPort("\\EN");

	if (sig_e == State::S0)
	{
		RTLIL::Const val_init;
		for (auto bit : dff_init_map(dlatch->getPort("\\Q")))
			val_init.bits.push_back(bit.wire == NULL ? bit.data : State::Sx);
		mod->connect(dlatch->getPort("\\Q"), val_init);
		goto delete_dlatch;
	}

	if (sig_e == State::S1)
	{
		mod->connect(dlatch->getPort("\\Q"), dlatch->getPort("\\D"));
		goto delete_dlatch;
	}

	return false;

delete_dlatch:
	log("Removing %s (%s) from module %s.\n", log_id(dlatch), log_id(dlatch->type), log_id(mod));
	remove_init_attr(dlatch->getPort("\\Q"));
	mod->remove(dlatch);
	return true;
}

bool handle_dff(RTLIL::Module *mod, RTLIL::Cell *dff)
{
	RTLIL::SigSpec sig_d, sig_q, sig_c, sig_r;
	RTLIL::Const val_cp, val_rp, val_rv;

	if (dff->type == "$_FF_") {
		sig_d = dff->getPort("\\D");
		sig_q = dff->getPort("\\Q");
	}
	else if (dff->type == "$_DFF_N_" || dff->type == "$_DFF_P_") {
		sig_d = dff->getPort("\\D");
		sig_q = dff->getPort("\\Q");
		sig_c = dff->getPort("\\C");
		val_cp = RTLIL::Const(dff->type == "$_DFF_P_", 1);
	}
	else if (dff->type.substr(0,6) == "$_DFF_" && dff->type.substr(9) == "_" &&
			(dff->type[6] == 'N' || dff->type[6] == 'P') &&
			(dff->type[7] == 'N' || dff->type[7] == 'P') &&
			(dff->type[8] == '0' || dff->type[8] == '1')) {
		sig_d = dff->getPort("\\D");
		sig_q = dff->getPort("\\Q");
		sig_c = dff->getPort("\\C");
		sig_r = dff->getPort("\\R");
		val_cp = RTLIL::Const(dff->type[6] == 'P', 1);
		val_rp = RTLIL::Const(dff->type[7] == 'P', 1);
		val_rv = RTLIL::Const(dff->type[8] == '1', 1);
	}
	else if (dff->type == "$ff") {
		sig_d = dff->getPort("\\D");
		sig_q = dff->getPort("\\Q");
	}
	else if (dff->type == "$dff") {
		sig_d = dff->getPort("\\D");
		sig_q = dff->getPort("\\Q");
		sig_c = dff->getPort("\\CLK");
		val_cp = RTLIL::Const(dff->parameters["\\CLK_POLARITY"].as_bool(), 1);
	}
	else if (dff->type == "$adff") {
		sig_d = dff->getPort("\\D");
		sig_q = dff->getPort("\\Q");
		sig_c = dff->getPort("\\CLK");
		sig_r = dff->getPort("\\ARST");
		val_cp = RTLIL::Const(dff->parameters["\\CLK_POLARITY"].as_bool(), 1);
		val_rp = RTLIL::Const(dff->parameters["\\ARST_POLARITY"].as_bool(), 1);
		val_rv = dff->parameters["\\ARST_VALUE"];
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

	if (dff->type.in("$ff", "$dff") && mux_drivers.has(sig_d)) {
		std::set<RTLIL::Cell*> muxes;
		mux_drivers.find(sig_d, muxes);
		for (auto mux : muxes) {
			RTLIL::SigSpec sig_a = assign_map(mux->getPort("\\A"));
			RTLIL::SigSpec sig_b = assign_map(mux->getPort("\\B"));
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

	if (!sig_c.empty() && sig_c.is_fully_const() && (!sig_r.size() || !has_init || val_init == val_rv)) {
		if (val_rv.bits.size() == 0)
			val_rv = val_init;
		mod->connect(sig_q, val_rv);
		goto delete_dff;
	}

	if (sig_d.is_fully_undef() && sig_r.size() && (!has_init || val_init == val_rv)) {
		mod->connect(sig_q, val_rv);
		goto delete_dff;
	}

	if (sig_d.is_fully_undef() && !sig_r.size() && has_init) {
		mod->connect(sig_q, val_init);
		goto delete_dff;
	}

	if (sig_d.is_fully_const() && (!sig_r.size() || val_rv == sig_d.as_const()) && (!has_init || val_init == sig_d.as_const())) {
		mod->connect(sig_q, sig_d);
		goto delete_dff;
	}

	if (sig_d == sig_q && (!sig_r.size() || !has_init || val_init == val_rv)) {
		if (sig_r.size())
			mod->connect(sig_q, val_rv);
		if (has_init)
			mod->connect(sig_q, val_init);
		goto delete_dff;
	}

	return false;

delete_dff:
	log("Removing %s (%s) from module %s.\n", log_id(dff), log_id(dff->type), log_id(mod));
	remove_init_attr(dff->getPort("\\Q"));
	mod->remove(dff);
	return true;
}

struct OptRmdffPass : public Pass {
	OptRmdffPass() : Pass("opt_rmdff", "remove DFFs with constant inputs") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_rmdff [-keepdc] [selection]\n");
		log("\n");
		log("This pass identifies flip-flops with constant inputs and replaces them with\n");
		log("a constant driver.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		int total_count = 0, total_initdrv = 0;
		log_header(design, "Executing OPT_RMDFF pass (remove dff with constant values).\n");

		keepdc = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-keepdc") {
				keepdc = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			pool<SigBit> driven_bits;
			dict<SigBit, State> init_bits;

			assign_map.set(module);
			dff_init_map.set(module);

			for (auto wire : module->wires())
			{
				if (wire->attributes.count("\\init") != 0) {
					Const initval = wire->attributes.at("\\init");
					dff_init_map.add(wire, initval);
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
			mux_drivers.clear();

			std::vector<RTLIL::IdString> dff_list;
			std::vector<RTLIL::IdString> dlatch_list;
			for (auto cell : module->cells())
			{
				for (auto &conn : cell->connections())
					if (cell->output(conn.first) || !cell->known())
						for (auto bit : assign_map(conn.second))
							driven_bits.insert(bit);

				if (cell->type == "$mux" || cell->type == "$pmux") {
					if (cell->getPort("\\A").size() == cell->getPort("\\B").size())
						mux_drivers.insert(assign_map(cell->getPort("\\Y")), cell);
					continue;
				}

				if (!design->selected(module, cell))
					continue;

				if (cell->type.in("$_FF_", "$_DFF_N_", "$_DFF_P_",
						"$_DFF_NN0_", "$_DFF_NN1_", "$_DFF_NP0_", "$_DFF_NP1_",
						"$_DFF_PN0_", "$_DFF_PN1_", "$_DFF_PP0_", "$_DFF_PP1_",
						"$ff", "$dff", "$adff"))
					dff_list.push_back(cell->name);

				if (cell->type == "$dlatch")
					dlatch_list.push_back(cell->name);
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

		if (total_count || total_initdrv)
			design->scratchpad_set_bool("opt.did_something", true);

		if (total_initdrv)
			log("Promoted %d init specs to constant drivers.\n", total_initdrv);

		if (total_count)
			log("Replaced %d DFF cells.\n", total_count);
	}
} OptRmdffPass;

PRIVATE_NAMESPACE_END
