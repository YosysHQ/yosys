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

#include "opt_status.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>

static SigMap assign_map;

static bool handle_dff(RTLIL::Module *mod, RTLIL::Cell *dff)
{
	RTLIL::SigSpec sig_d, sig_q, sig_c, sig_r;
	RTLIL::Const val_cp, val_rp, val_rv;

	if (dff->type == "$_DFF_N_" || dff->type == "$_DFF_P_") {
		sig_d = dff->connections["\\D"];
		sig_q = dff->connections["\\Q"];
		sig_c = dff->connections["\\C"];
		val_cp = RTLIL::Const(dff->type == "$_DFF_P_", 1);
	}
	else if (dff->type.substr(0,6) == "$_DFF_" && dff->type.substr(9) == "_" &&
			(dff->type[6] == 'N' || dff->type[6] == 'P') &&
			(dff->type[7] == 'N' || dff->type[7] == 'P') &&
			(dff->type[8] == '0' || dff->type[8] == '1')) {
		sig_d = dff->connections["\\D"];
		sig_q = dff->connections["\\Q"];
		sig_c = dff->connections["\\C"];
		sig_r = dff->connections["\\R"];
		val_cp = RTLIL::Const(dff->type[6] == 'P', 1);
		val_rp = RTLIL::Const(dff->type[7] == 'P', 1);
		val_rv = RTLIL::Const(dff->type[8] == '1', 1);
	}
	else if (dff->type == "$dff") {
		sig_d = dff->connections["\\D"];
		sig_q = dff->connections["\\Q"];
		sig_c = dff->connections["\\CLK"];
		val_cp = RTLIL::Const(dff->parameters["\\CLK_POLARITY"].as_bool(), 1);
	}
	else if (dff->type == "$adff") {
		sig_d = dff->connections["\\D"];
		sig_q = dff->connections["\\Q"];
		sig_c = dff->connections["\\CLK"];
		sig_r = dff->connections["\\ARST"];
		val_cp = RTLIL::Const(dff->parameters["\\CLK_POLARITY"].as_bool(), 1);
		val_rp = RTLIL::Const(dff->parameters["\\ARST_POLARITY"].as_bool(), 1);
		val_rv = dff->parameters["\\ARST_VALUE"];
	}
	else
		log_error("abort.");
	
	assign_map.apply(sig_d);
	assign_map.apply(sig_q);
	assign_map.apply(sig_c);
	assign_map.apply(sig_r);

	if (sig_d.is_fully_const() && sig_r.width == 0) {
		RTLIL::SigSig conn(sig_q, sig_d);
		mod->connections.push_back(conn);
		goto delete_dff;
	}

	if (sig_d == sig_q && sig_r.width == 0) {
		goto delete_dff;
	}

	return false;

delete_dff:
	log("Removing %s (%s) from module %s.\n", dff->name.c_str(), dff->type.c_str(), mod->name.c_str());
	OPT_DID_SOMETHING = true;
	mod->cells.erase(dff->name);
	delete dff;
	return true;
}

struct OptRmdffPass : public Pass {
	OptRmdffPass() : Pass("opt_rmdff") { }
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		int total_count = 0;
		log_header("Executing OPT_RMDFF pass (remove dff with constant values).\n");

		extra_args(args, 1, design);

		for (auto &mod_it : design->modules)
		{
			assign_map.set(mod_it.second);

			std::vector<std::string> dff_list;
			for (auto &it : mod_it.second->cells) {
				if (it.second->type == "$_DFF_N_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_P_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_NN0_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_NN1_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_NP0_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_NP1_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_PN0_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_PN1_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_PP0_") dff_list.push_back(it.first);
				if (it.second->type == "$_DFF_PP1_") dff_list.push_back(it.first);
				if (it.second->type == "$dff") dff_list.push_back(it.first);
				if (it.second->type == "$adff") dff_list.push_back(it.first);
			}

			for (auto &id : dff_list) {
				if (mod_it.second->cells.count(id) > 0 &&
						handle_dff(mod_it.second, mod_it.second->cells[id]))
					total_count++;
			}
		}

		assign_map.clear();
		log("Replaced %d DFF cells.\n", total_count);
	}
} OptRmdffPass;
 
