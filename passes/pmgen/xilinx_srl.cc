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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// for peepopt_pm
bool did_something;

#include "passes/pmgen/xilinx_srl_pm.h"
#include "passes/pmgen/ice40_dsp_pm.h"
#include "passes/pmgen/peepopt_pm.h"

void reduce_chain(xilinx_srl_pm &pm, int minlen)
{
	auto &st = pm.st_reduce;
	auto &ud = pm.ud_reduce;

	if (GetSize(ud.longest_chain) < minlen)
		return;

	log("Found chain of length %d (%s):\n", GetSize(ud.longest_chain), log_id(st.first->type));

	auto last_cell = ud.longest_chain.back();

	SigSpec initval;
	for (auto cell : ud.longest_chain) {
		log_debug("    %s\n", log_id(cell));
		SigBit Q = cell->getPort(ID(Q));
		log_assert(Q.wire);
		auto it = Q.wire->attributes.find(ID(init));
		if (it != Q.wire->attributes.end()) {
			initval.append(it->second[Q.offset]);
		}
		else
			initval.append(State::Sx);
		if (cell != last_cell)
			pm.autoremove(cell);
	}

	Cell *c = last_cell;
	SigBit Q = st.first->getPort(ID(Q));
	c->setPort(ID(Q), Q);

	if (c->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID(FDRE), ID(FDRE_1))) {
		c->parameters.clear();
		c->setParam(ID(DEPTH), GetSize(ud.longest_chain));
		c->setParam(ID(INIT), initval.as_const());
		if (c->type.in(ID($_DFF_P_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			c->setParam(ID(CLKPOL), 1);
		else
			log_abort();
		if (c->type.in(ID($_DFFE_NN_), ID($_DFFE_PN_)))
			c->setParam(ID(ENPOL), 1);
		else if (c->type.in(ID($_DFFE_NP_), ID($_DFFE_PN_)))
			c->setParam(ID(ENPOL), 0);
		else
			c->setParam(ID(ENPOL), 2);
		if (c->type.in(ID($_DFF_N_), ID($_DFF_P_)))
			c->setPort(ID(E), State::S1);
		c->setPort(ID(L), GetSize(ud.longest_chain)-1);
		c->type = ID($__XILINX_SHREG_);
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
		log("TODO.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing XILINX_SRL pass (Xilinx shift register extraction).\n");

		int minlen = 3;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-minlen" && argidx+1 < args.size()) {
				minlen = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		auto f = std::bind(reduce_chain, std::placeholders::_1, minlen);
		for (auto module : design->selected_modules())
			while (xilinx_srl_pm(module, module->selected_cells()).run_reduce(f)) {}
	}
} XilinxSrlPass;

PRIVATE_NAMESPACE_END
