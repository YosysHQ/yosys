/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *            (C) 2019  Eddie Hung    <eddie@fpgeh.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/pmgen/xilinx_srl_pm.h"

void run_fixed(xilinx_srl_pm &pm)
{
	auto &st = pm.st_fixed;
	auto &ud = pm.ud_fixed;
	log("Found fixed chain of length %d (%s):\n", GetSize(ud.longest_chain), log_id(st.first->type));

	SigSpec initval;
	for (auto cell : ud.longest_chain) {
		log_debug("    %s\n", log_id(cell));
		if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_))) {
			SigBit Q = cell->getPort(ID(Q));
			log_assert(Q.wire);
			auto it = Q.wire->attributes.find(ID(init));
			if (it != Q.wire->attributes.end()) {
				auto &i = it->second[Q.offset];
				initval.append(i);
				i = State::Sx;
			}
			else
				initval.append(State::Sx);
		}
		else if (cell->type.in(ID(FDRE), ID(FDRE_1))) {
			if (cell->parameters.at(ID(INIT), State::S0).as_bool())
				initval.append(State::S1);
			else
				initval.append(State::S0);
		}
		else
			log_abort();
		pm.autoremove(cell);
	}

	auto first_cell = ud.longest_chain.back();
	auto last_cell = ud.longest_chain.front();
	Cell *c = pm.module->addCell(NEW_ID, ID($__XILINX_SHREG_));
	pm.module->swap_names(c, first_cell);

	if (first_cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID(FDRE), ID(FDRE_1))) {
		c->setParam(ID(DEPTH), GetSize(ud.longest_chain));
		c->setParam(ID(INIT), initval.as_const());
		if (first_cell->type.in(ID($_DFF_P_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			c->setParam(ID(CLKPOL), 1);
		else if (first_cell->type.in(ID($_DFF_N_), ID($DFFE_NN_), ID($_DFFE_NP_), ID(FDRE_1)))
			c->setParam(ID(CLKPOL), 0);
		else if (first_cell->type.in(ID(FDRE))) {
			if (!first_cell->parameters.at(ID(IS_C_INVERTED), State::S0).as_bool())
				c->setParam(ID(CLKPOL), 1);
			else
				c->setParam(ID(CLKPOL), 0);
		}
		else
			log_abort();
		if (first_cell->type.in(ID($_DFFE_NP_), ID($_DFFE_PP_)))
			c->setParam(ID(ENPOL), 1);
		else if (first_cell->type.in(ID($_DFFE_NN_), ID($_DFFE_PN_)))
			c->setParam(ID(ENPOL), 0);
		else
			c->setParam(ID(ENPOL), 2);

		c->setPort(ID(C), first_cell->getPort(ID(C)));
		c->setPort(ID(D), first_cell->getPort(ID(D)));
		c->setPort(ID(Q), last_cell->getPort(ID(Q)));
		c->setPort(ID(L), GetSize(ud.longest_chain)-1);
		if (first_cell->type.in(ID($_DFF_N_), ID($_DFF_P_)))
			c->setPort(ID(E), State::S1);
		else if (first_cell->type.in(ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			c->setPort(ID(E), first_cell->getPort(ID(E)));
		else if (first_cell->type.in(ID(FDRE), ID(FDRE_1)))
			c->setPort(ID(E), first_cell->getPort(ID(CE)));
		else
			log_abort();
	}
	else
		log_abort();

	log("    -> %s (%s)\n", log_id(c), log_id(c->type));
}

void run_variable(xilinx_srl_pm &pm)
{
	auto &st = pm.st_variable;
	auto &ud = pm.ud_variable;

	log("Found variable chain of length %d (%s):\n", GetSize(ud.chain), log_id(st.first->type));

	SigSpec initval;
	for (const auto &i : ud.chain) {
		auto cell = i.first;
		auto slice = i.second;
		log_debug("    %s\n", log_id(cell));
		if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID($dff), ID($dffe))) {
			SigBit Q = cell->getPort(ID(Q))[slice];
			log_assert(Q.wire);
			auto it = Q.wire->attributes.find(ID(init));
			if (it != Q.wire->attributes.end()) {
				auto &i = it->second[Q.offset];
				initval.append(i);
				i = State::Sx;
			}
			else
				initval.append(State::Sx);
		}
		else
			log_abort();
	}
	pm.autoremove(st.shiftx);

	auto first_cell = ud.chain.back().first;
	auto first_slice = ud.chain.back().second;

	Cell *c = pm.module->addCell(NEW_ID, ID($__XILINX_SHREG_));
	pm.module->swap_names(c, first_cell);

	if (first_cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID($dff), ID($dffe))) {
		c->setParam(ID(DEPTH), GetSize(ud.chain));
		c->setParam(ID(INIT), initval.as_const());
		Const clkpol, enpol;
		if (first_cell->type.in(ID($_DFF_P_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			clkpol = 1;
		else if (first_cell->type.in(ID($_DFF_N_), ID($DFFE_NN_), ID($_DFFE_NP_)))
			clkpol = 0;
		else if (first_cell->type.in(ID($dff), ID($dffe)))
			clkpol = first_cell->getParam(ID(CLK_POLARITY));
		else
			log_abort();
		if (first_cell->type.in(ID($_DFFE_NP_), ID($_DFFE_PP_)))
			enpol = 1;
		else if (first_cell->type.in(ID($_DFFE_NN_), ID($_DFFE_PN_)))
			enpol = 0;
		else if (first_cell->type.in(ID($dffe)))
			enpol = first_cell->getParam(ID(EN_POLARITY));
		else
			enpol = 2;
		c->setParam(ID(CLKPOL), clkpol);
		c->setParam(ID(ENPOL), enpol);

		if (first_cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			c->setPort(ID(C), first_cell->getPort(ID(C)));
		else if (first_cell->type.in(ID($dff), ID($dffe)))
			c->setPort(ID(C), first_cell->getPort(ID(CLK)));
		else
			log_abort();
		c->setPort(ID(D), first_cell->getPort(ID(D))[first_slice]);
		c->setPort(ID(Q), st.shiftx->getPort(ID(Y)));
		c->setPort(ID(L), st.shiftx->getPort(ID(B)));
		if (first_cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($dff)))
			c->setPort(ID(E), State::S1);
		else if (first_cell->type.in(ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			c->setPort(ID(E), first_cell->getPort(ID(E)));
		else if (first_cell->type.in(ID($dffe)))
			c->setPort(ID(E), first_cell->getPort(ID(EN)));
		else
			log_abort();
	}
	else
		log_abort();

	log("    -> %s (%s)\n", log_id(c), log_id(c->type));
}

struct XilinxSrlPass : public Pass {
	XilinxSrlPass() : Pass("xilinx_srl", "Xilinx shift register extraction") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_srl [options] [selection]\n");
		log("\n");
		log("This pass converts chains of built-in flops (bit-level: $_DFF_[NP]_, $_DFFE_*\n");
		log("and word-level: $dff, $dffe) as well as Xilinx flops (FDRE, FDRE_1) into a\n");
		log("$__XILINX_SHREG cell. Chains must be of the same cell type, clock, clock polarity,\n");
		log("enable, and enable polarity (where relevant).\n");
		log("Flops with resets cannot be mapped to Xilinx devices and will not be inferred.");
		log("\n");
		log("    -minlen N\n");
		log("        min length of shift register (default = 3)\n");
		log("\n");
		log("    -fixed\n");
		log("        infer fixed-length shift registers.\n");
		log("\n");
		log("    -variable\n");
		log("        infer variable-length shift registers (i.e. fixed-length shifts where\n");
		log("        each element also fans-out to a $shiftx cell).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing XILINX_SRL pass (Xilinx shift register extraction).\n");

		bool fixed = false;
		bool variable = false;
		int minlen = 3;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-minlen" && argidx+1 < args.size()) {
				minlen = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-fixed") {
				fixed = true;
				continue;
			}
			if (args[argidx] == "-variable") {
				variable = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!fixed && !variable)
			log_cmd_error("'-fixed' and/or '-variable' must be specified.\n");

		for (auto module : design->selected_modules()) {
			auto pm = xilinx_srl_pm(module, module->selected_cells());
			pm.ud_fixed.minlen = minlen;
			pm.ud_variable.minlen = minlen;

			if (fixed)
				pm.run_fixed(run_fixed);
			if (variable)
				pm.run_variable(run_variable);
		}
	}
} XilinxSrlPass;

PRIVATE_NAMESPACE_END
