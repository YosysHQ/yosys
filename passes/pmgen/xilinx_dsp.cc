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

template<class T> inline bool includes(const T &lhs, const T &rhs) {
	return std::includes(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
}
#include <set>
#include "passes/pmgen/xilinx_dsp_pm.h"

void pack_xilinx_dsp(dict<SigBit, Cell*> &bit_to_driver, xilinx_dsp_pm &pm)
{
	auto &st = pm.st_xilinx_dsp;

#if 1
	log("\n");
	log("ffA:     %s\n", log_id(st.ffA, "--"));
	log("ffB:     %s\n", log_id(st.ffB, "--"));
	log("dsp:     %s\n", log_id(st.dsp, "--"));
	log("addAB:   %s\n", log_id(st.addAB, "--"));
	log("ffM:     %s\n", log_id(st.ffM, "--"));
	log("ffP:     %s\n", log_id(st.ffP, "--"));
	//log("muxP:  %s\n", log_id(st.muxP, "--"));
	log("sigPused: %s\n", log_signal(st.sigPused));
#endif

	log("Analysing %s.%s for Xilinx DSP packing.\n", log_id(pm.module), log_id(st.dsp));

	Cell *cell = st.dsp;
	bit_to_driver.insert(std::make_pair(cell->getPort("\\P")[17], cell));
	SigSpec P = st.sigP;

	if (st.addAB) {
		log_assert(st.addAB->getParam("\\A_SIGNED").as_bool());
		log_assert(st.addAB->getParam("\\B_SIGNED").as_bool());
		log("  adder %s (%s)\n", log_id(st.addAB), log_id(st.addAB->type));

		SigSpec C = st.sigC;
		C.extend_u0(48, true);
		cell->setPort("\\C", C);
		SigSpec &opmode = cell->connections_.at("\\OPMODE");
		opmode[6] = State::S0;
		opmode[5] = State::S1;
		opmode[4] = State::S1;
		pm.autoremove(st.addAB);
	}

	if (st.clock != SigBit())
	{
		cell->setPort("\\CLK", st.clock);

		if (st.ffA) {
			SigSpec A = cell->getPort("\\A");
			SigSpec D = st.ffA->getPort("\\D");
			SigSpec Q = st.ffA->getPort("\\Q");
			A.replace(Q, D);
			cell->setPort("\\A", A);
			cell->setParam("\\AREG", 1);
			if (st.ffA->type == "$dff")
				cell->setPort("\\CEA2", State::S1);
			//else if (st.ffA->type == "$dffe")
			//	cell->setPort("\\CEA2", st.ffA->getPort("\\EN"));
			else log_abort();
		}
		if (st.ffB) {
			SigSpec B = cell->getPort("\\B");
			SigSpec D = st.ffB->getPort("\\D");
			SigSpec Q = st.ffB->getPort("\\Q");
			B.replace(Q, D);
			cell->setPort("\\B", B);
			cell->setParam("\\BREG", 1);
			if (st.ffB->type == "$dff")
				cell->setPort("\\CEB2", State::S1);
			//else if (st.ffB->type == "$dffe")
			//	cell->setPort("\\CEB2", st.ffB->getPort("\\EN"));
			else log_abort();
		}
		if (st.ffM) {
			SigSpec D = st.ffM->getPort("\\D");
			SigSpec Q = st.ffM->getPort("\\Q");
			P.replace(pm.sigmap(D), Q);
			cell->setParam("\\MREG", State::S1);
			if (st.ffP->type == "$dff")
				cell->setPort("\\CEM", State::S1);
			//else if (st.ffP->type == "$dffe")
			//	cell->setPort("\\CEP", st.ffP->getPort("\\EN"));
			else log_abort();
		}
		if (st.ffP) {
			SigSpec D;
			//if (st.muxP)
			//	D = st.muxP->getPort("\\B");
			//else
				D = st.ffP->getPort("\\D");
			SigSpec Q = st.ffP->getPort("\\Q");
			P.replace(pm.sigmap(D), Q);
			cell->setParam("\\PREG", State::S1);
			if (st.ffP->type == "$dff")
				cell->setPort("\\CEP", State::S1);
			//else if (st.ffP->type == "$dffe")
			//	cell->setPort("\\CEP", st.ffP->getPort("\\EN"));
			else log_abort();

			st.ffP->connections_.at("\\Q").replace(P, pm.module->addWire(NEW_ID, GetSize(P)));
		}

		log("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffA)
			log(" ffA:%s", log_id(st.ffA));

		if (st.ffB)
			log(" ffB:%s", log_id(st.ffB));

		if (st.ffP)
			log(" ffP:%s", log_id(st.ffP));

		log("\n");
	}

	if (GetSize(P) < 48)
		P.append(pm.module->addWire(NEW_ID, 48-GetSize(P)));
	cell->setPort("\\P", P);

	pm.blacklist(cell);
}

struct XilinxDspPass : public Pass {
	XilinxDspPass() : Pass("xilinx_dsp", "Xilinx: pack DSP registers") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_dsp [options] [selection]\n");
		log("\n");
		log("Pack registers into Xilinx DSPs\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing XILINX_DSP pass (pack DSPs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			xilinx_dsp_pm pm(module, module->selected_cells());
			dict<SigBit, Cell*> bit_to_driver;
			auto f = [&bit_to_driver](xilinx_dsp_pm &pm){ pack_xilinx_dsp(bit_to_driver, pm); };
			pm.run_xilinx_dsp(f);

			// Look for ability to convert C input from another DSP into PCIN
			//   NB: Needs to be done after pattern matcher has folded all
			//       $add cells into the DSP
			for (auto cell : module->cells()) {
				if (cell->type != "\\DSP48E1")
					continue;
				SigSpec &opmode = cell->connections_.at("\\OPMODE");
				if (opmode.extract(4,3) != Const::from_string("011"))
					continue;
				SigSpec C = pm.sigmap(cell->getPort("\\C"));
				if (C.has_const())
					continue;
				auto it = bit_to_driver.find(C[0]);
				if (it == bit_to_driver.end())
					continue;
				auto driver = it->second;

				// Unextend C
				int i;
				for (i = GetSize(C)-1; i > 0; i--)
					if (C[i] != C[i-1])
						break;
				if (i > 48-17)
					continue;
				if (driver->getPort("\\P").extract(17, i) == C.extract(0, i)) {
					cell->setPort("\\C", Const(0, 48));
					Wire *cascade = module->addWire(NEW_ID, 48);
					driver->setPort("\\PCOUT", cascade);
					cell->setPort("\\PCIN", cascade);
					opmode[6] = State::S1;
					opmode[5] = State::S0;
					opmode[4] = State::S1;
					bit_to_driver.erase(it);
				}
			}
		}
	}
} XilinxDspPass;

PRIVATE_NAMESPACE_END
