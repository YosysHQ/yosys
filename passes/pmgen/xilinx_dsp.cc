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

#include "passes/pmgen/xilinx_dsp_pm.h"

static Cell* addDsp(Module *module) {
	Cell *cell = module->addCell(NEW_ID, "\\DSP48E1");
	cell->setParam("\\ACASCREG", 0);
	cell->setParam("\\ADREG", 0);
	cell->setParam("\\A_INPUT", Const("DIRECT"));
	cell->setParam("\\ALUMODEREG", 0);
	cell->setParam("\\AREG", 0);
	cell->setParam("\\BCASCREG", 0);
	cell->setParam("\\B_INPUT", Const("DIRECT"));
	cell->setParam("\\BREG", 0);
	cell->setParam("\\CARRYINREG", 0);
	cell->setParam("\\CARRYINSELREG", 0);
	cell->setParam("\\CREG", 0);
	cell->setParam("\\DREG", 0);
	cell->setParam("\\INMODEREG", 0);
	cell->setParam("\\MREG", 0);
	cell->setParam("\\OPMODEREG", 0);
	cell->setParam("\\PREG", 0);
	cell->setParam("\\USE_MULT", Const("NONE"));

	cell->setPort("\\D", Const(0, 24));
	cell->setPort("\\INMODE", Const(0, 5));
	cell->setPort("\\ALUMODE", Const(0, 4));
	cell->setPort("\\OPMODE", Const(0, 7));
	cell->setPort("\\CARRYINSEL", Const(0, 3));
	cell->setPort("\\ACIN", Const(0, 30));
	cell->setPort("\\BCIN", Const(0, 18));
	cell->setPort("\\PCIN", Const(0, 48));
	cell->setPort("\\CARRYIN", Const(0, 1));
	return cell;
}

void pack_xilinx_simd(Module *module, const std::vector<Cell*> &selected_cells)
{
	std::deque<Cell*> simd12_add, simd12_sub;
	std::deque<Cell*> simd24_add, simd24_sub;

	for (auto cell : selected_cells) {
		if (!cell->type.in("$add", "$sub"))
			continue;
		SigSpec Y = cell->getPort("\\Y");
		if (!Y.is_chunk())
			continue;
		if (!Y.as_chunk().wire->get_strpool_attribute("\\use_dsp").count("simd"))
			continue;
		if (GetSize(Y) > 25)
			continue;
		SigSpec A = cell->getPort("\\A");
		SigSpec B = cell->getPort("\\B");
		if (GetSize(Y) <= 13) {
			if (GetSize(A) > 12)
				continue;
			if (GetSize(B) > 12)
				continue;
			if (cell->type == "$add")
				simd12_add.push_back(cell);
			else if (cell->type == "$sub")
				simd12_sub.push_back(cell);
		}
		else if (GetSize(Y) <= 25) {
			if (GetSize(A) > 24)
				continue;
			if (GetSize(B) > 24)
				continue;
			if (cell->type == "$add")
				simd24_add.push_back(cell);
			else if (cell->type == "$sub")
				simd24_sub.push_back(cell);
		}
		else
			log_abort();
	}

	auto f12 = [module](SigSpec &AB, SigSpec &C, SigSpec &P, SigSpec &CARRYOUT, Cell *lane) {
		SigSpec A = lane->getPort("\\A");
		SigSpec B = lane->getPort("\\B");
		SigSpec Y = lane->getPort("\\Y");
		A.extend_u0(12, lane->getParam("\\A_SIGNED").as_bool());
		B.extend_u0(12, lane->getParam("\\B_SIGNED").as_bool());
		AB.append(A);
		C.append(B);
		if (GetSize(Y) < 13)
			Y.append(module->addWire(NEW_ID, 13-GetSize(Y)));
		else
			log_assert(GetSize(Y) == 13);
		P.append(Y.extract(0, 12));
		CARRYOUT.append(Y[12]);
	};
	auto g12 = [&f12,module](std::deque<Cell*> &simd12) {
		while (simd12.size() > 1) {
			SigSpec AB, C, P, CARRYOUT;

			Cell *lane1 = simd12.front();
			simd12.pop_front();
			Cell *lane2 = simd12.front();
			simd12.pop_front();
			Cell *lane3 = nullptr;
			Cell *lane4 = nullptr;

			if (!simd12.empty()) {
				lane3 = simd12.front();
				simd12.pop_front();
				if (!simd12.empty()) {
					lane4 = simd12.front();
					simd12.pop_front();
				}
			}

			log("Analysing %s.%s for Xilinx DSP SIMD12 packing.\n", log_id(module), log_id(lane1));

			Cell *cell = addDsp(module);
			cell->setParam("\\USE_SIMD", Const("FOUR12"));
			// X = A:B
			// Y = 0
			// Z = C
			cell->setPort("\\OPMODE", Const::from_string("0110011"));

			log_assert(lane1);
			log_assert(lane2);
			f12(AB, C, P, CARRYOUT, lane1);
			f12(AB, C, P, CARRYOUT, lane2);
			if (lane3) {
				f12(AB, C, P, CARRYOUT, lane3);
				if (lane4)
					f12(AB, C, P, CARRYOUT, lane4);
				else {
					AB.append(Const(0, 12));
					C.append(Const(0, 12));
					P.append(module->addWire(NEW_ID, 12));
					CARRYOUT.append(module->addWire(NEW_ID, 1));
				}
			}
			else {
				AB.append(Const(0, 24));
				C.append(Const(0, 24));
				P.append(module->addWire(NEW_ID, 24));
				CARRYOUT.append(module->addWire(NEW_ID, 2));
			}
			log_assert(GetSize(AB) == 48);
			log_assert(GetSize(C) == 48);
			log_assert(GetSize(P) == 48);
			log_assert(GetSize(CARRYOUT) == 4);
			cell->setPort("\\A", AB.extract(18, 30));
			cell->setPort("\\B", AB.extract(0, 18));
			cell->setPort("\\C", C);
			cell->setPort("\\P", P);
			cell->setPort("\\CARRYOUT", CARRYOUT);
			if (lane1->type == "$sub")
				cell->setPort("\\ALUMODE", Const::from_string("0011"));

			module->remove(lane1);
			module->remove(lane2);
			if (lane3) module->remove(lane3);
			if (lane4) module->remove(lane4);

			module->design->select(module, cell);
		}
	};
	g12(simd12_add);
	g12(simd12_sub);

	auto f24 = [module](SigSpec &AB, SigSpec &C, SigSpec &P, SigSpec &CARRYOUT, Cell *lane) {
		SigSpec A = lane->getPort("\\A");
		SigSpec B = lane->getPort("\\B");
		SigSpec Y = lane->getPort("\\Y");
		A.extend_u0(24, lane->getParam("\\A_SIGNED").as_bool());
		B.extend_u0(24, lane->getParam("\\B_SIGNED").as_bool());
		C.append(A);
		AB.append(B);
		if (GetSize(Y) < 25)
			Y.append(module->addWire(NEW_ID, 25-GetSize(Y)));
		else
			log_assert(GetSize(Y) == 25);
		P.append(Y.extract(0, 24));
		CARRYOUT.append(module->addWire(NEW_ID)); // TWO24 uses every other bit
		CARRYOUT.append(Y[24]);
	};
	auto g24 = [&f24,module](std::deque<Cell*> &simd24) {
		while (simd24.size() > 1) {
			SigSpec AB;
			SigSpec C;
			SigSpec P;
			SigSpec CARRYOUT;

			Cell *lane1 = simd24.front();
			simd24.pop_front();
			Cell *lane2 = simd24.front();
			simd24.pop_front();

			log("Analysing %s.%s for Xilinx DSP SIMD24 packing.\n", log_id(module), log_id(lane1));

			Cell *cell = addDsp(module);
			cell->setParam("\\USE_SIMD", Const("TWO24"));
			// X = A:B
			// Y = 0
			// Z = C
			cell->setPort("\\OPMODE", Const::from_string("0110011"));

			log_assert(lane1);
			log_assert(lane2);
			f24(AB, C, P, CARRYOUT, lane1);
			f24(AB, C, P, CARRYOUT, lane2);
			log_assert(GetSize(AB) == 48);
			log_assert(GetSize(C) == 48);
			log_assert(GetSize(P) == 48);
			log_assert(GetSize(CARRYOUT) == 4);
			cell->setPort("\\A", AB.extract(18, 30));
			cell->setPort("\\B", AB.extract(0, 18));
			cell->setPort("\\C", C);
			cell->setPort("\\P", P);
			cell->setPort("\\CARRYOUT", CARRYOUT);
			if (lane1->type == "$sub")
				cell->setPort("\\ALUMODE", Const::from_string("0011"));

			module->remove(lane1);
			module->remove(lane2);

			module->design->select(module, cell);
		}
	};
	g24(simd24_add);
	g24(simd24_sub);
}


void pack_xilinx_dsp(dict<SigBit, Cell*> &bit_to_driver, xilinx_dsp_pm &pm)
{
	auto &st = pm.st_xilinx_dsp;

#if 1
	log("\n");
	log("preAdd:     %s\n", log_id(st.preAdd, "--"));
	log("ffAD:       %s %s %s\n", log_id(st.ffAD, "--"), log_id(st.ffADcemux, "--"), log_id(st.ffADrstmux, "--"));
	log("ffA:        %s %s %s\n", log_id(st.ffA, "--"), log_id(st.ffAcemux, "--"), log_id(st.ffArstmux, "--"));
	log("ffB:        %s %s %s\n", log_id(st.ffB, "--"), log_id(st.ffBcemux, "--"), log_id(st.ffBrstmux, "--"));
	log("ffC:        %s %s %s\n", log_id(st.ffC, "--"), log_id(st.ffCcemux, "--"), log_id(st.ffCrstmux, "--"));
	log("ffD:        %s %s %s\n", log_id(st.ffD, "--"), log_id(st.ffDcemux, "--"), log_id(st.ffDrstmux, "--"));
	log("dsp:        %s\n", log_id(st.dsp, "--"));
	log("ffM:        %s %s %s\n", log_id(st.ffM, "--"), log_id(st.ffMcemux, "--"), log_id(st.ffMrstmux, "--"));
	log("postAdd:    %s\n", log_id(st.postAdd, "--"));
	log("postAddMux: %s\n", log_id(st.postAddMux, "--"));
	log("ffP:        %s %s %s\n", log_id(st.ffP, "--"), log_id(st.ffPcemux, "--"), log_id(st.ffPrstmux, "--"));
#endif

	log("Analysing %s.%s for Xilinx DSP packing.\n", log_id(pm.module), log_id(st.dsp));

	Cell *cell = st.dsp;

	if (st.preAdd) {
		log("  preadder %s (%s)\n", log_id(st.preAdd), log_id(st.preAdd->type));
		bool A_SIGNED = st.preAdd->getParam("\\A_SIGNED").as_bool();
		bool D_SIGNED = st.preAdd->getParam("\\B_SIGNED").as_bool();
		if (st.sigA == st.preAdd->getPort("\\B"))
			std::swap(A_SIGNED, D_SIGNED);
		st.sigA.extend_u0(30, A_SIGNED);
		st.sigD.extend_u0(25, D_SIGNED);
		cell->setPort("\\A", st.sigA);
		cell->setPort("\\D", st.sigD);
		cell->connections_.at("\\INMODE") = Const::from_string("00100");

		if (st.ffAD) {
			if (st.ffADcemux) {
				SigSpec S = st.ffADcemux->getPort("\\S");
				cell->setPort("\\CEAD", st.ffADcepol ? S : pm.module->Not(NEW_ID, S));
			}
			else
				cell->setPort("\\CEAD", State::S1);
			cell->setParam("\\ADREG", 1);
		}

		cell->setParam("\\USE_DPORT", Const("TRUE"));

		pm.autoremove(st.preAdd);
	}
	if (st.postAdd) {
		log("  postadder %s (%s)\n", log_id(st.postAdd), log_id(st.postAdd->type));

		SigSpec &opmode = cell->connections_.at("\\OPMODE");
		if (st.postAddMux) {
			log_assert(st.ffP);
			opmode[4] = st.postAddMux->getPort("\\S");
			pm.autoremove(st.postAddMux);
		}
		else if (st.ffP && st.sigC == st.sigP)
			opmode[4] = State::S0;
		else
			opmode[4] = State::S1;
		opmode[6] = State::S0;
		opmode[5] = State::S1;

		if (opmode[4] != State::S0) {
			//if (st.postAddMuxAB == "\\A")
			//	st.sigC.extend_u0(48, st.postAdd->getParam("\\B_SIGNED").as_bool());
			//else
			//	st.sigC.extend_u0(48, st.postAdd->getParam("\\A_SIGNED").as_bool());
			cell->setPort("\\C", st.sigC);
		}

		pm.autoremove(st.postAdd);
	}

	if (st.clock != SigBit())
	{
		cell->setPort("\\CLK", st.clock);

		auto f = [&pm,cell](SigSpec &A, Cell* ff, Cell* cemux, bool cepol, IdString ceport, Cell* rstmux, bool rstpol, IdString rstport) {
			SigSpec D = ff->getPort("\\D");
			SigSpec Q = pm.sigmap(ff->getPort("\\Q"));
			if (!A.empty())
				A.replace(Q, D);
			if (rstmux) {
				SigSpec Y = rstmux->getPort("\\Y");
				SigSpec AB = rstmux->getPort(rstpol ? "\\A" : "\\B");
				SigSpec S = rstmux->getPort("\\S");
				if (!A.empty())
					A.replace(Y, AB);
				cell->setPort(rstport, rstpol ? S : pm.module->Not(NEW_ID, S));
			}
			else
				cell->setPort(rstport, State::S0);
			if (cemux) {
				SigSpec Y = cemux->getPort("\\Y");
				SigSpec BA = cemux->getPort(cepol ? "\\B" : "\\A");
				SigSpec S = cemux->getPort("\\S");
				if (!A.empty())
					A.replace(Y, BA);
				cell->setPort(ceport, cepol ? S : pm.module->Not(NEW_ID, S));
			}
			else
				cell->setPort(ceport, State::S1);

			for (auto c : Q.chunks()) {
				auto it = c.wire->attributes.find("\\init");
				if (it == c.wire->attributes.end())
					continue;
				for (int i = c.offset; i < c.offset+c.width; i++) {
					log_assert(it->second[i] == State::S0 || it->second[i] == State::Sx);
					it->second[i] = State::Sx;
				}
			}
		};

		if (st.ffA) {
			SigSpec &A = cell->connections_.at("\\A");
			f(A, st.ffA, st.ffAcemux, st.ffAcepol, "\\CEA2", st.ffArstmux, st.ffArstpol, "\\RSTA");
			pm.add_siguser(A, cell);
			cell->setParam("\\AREG", 1);
		}
		if (st.ffB) {
			SigSpec &B = cell->connections_.at("\\B");
			f(B, st.ffB, st.ffBcemux, st.ffBcepol, "\\CEB2", st.ffBrstmux, st.ffBrstpol, "\\RSTB");
			pm.add_siguser(B, cell);
			cell->setParam("\\BREG", 1);
		}
		if (st.ffC) {
			SigSpec &C = cell->connections_.at("\\C");
			f(C, st.ffC, st.ffCcemux, st.ffCcepol, "\\CEC", st.ffCrstmux, st.ffCrstpol, "\\RSTC");
			pm.add_siguser(C, cell);
			cell->setParam("\\CREG", 1);
		}
		if (st.ffD) {
			SigSpec &D = cell->connections_.at("\\D");
			f(D, st.ffD, st.ffDcemux, st.ffDcepol, "\\CED", st.ffDrstmux, st.ffDrstpol, "\\RSTD");
			pm.add_siguser(D, cell);
			cell->setParam("\\DREG", 1);
		}
		if (st.ffM) {
			SigSpec M; // unused
			f(M, st.ffM, st.ffMcemux, st.ffMcepol, "\\CEM", st.ffMrstmux, st.ffMrstpol, "\\RSTM");
			st.ffM->connections_.at("\\Q").replace(st.sigM, pm.module->addWire(NEW_ID, GetSize(st.sigM)));
			cell->setParam("\\MREG", State::S1);
		}
		if (st.ffP) {
			SigSpec P; // unused
			f(P, st.ffP, st.ffPcemux, st.ffPcepol, "\\CEP", st.ffPrstmux, st.ffPrstpol, "\\RSTP");
			st.ffP->connections_.at("\\Q").replace(st.sigP, pm.module->addWire(NEW_ID, GetSize(st.sigP)));
			cell->setParam("\\PREG", State::S1);
		}

		log("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffA)
			log(" ffA:%s", log_id(st.ffA));

		if (st.ffAD)
			log(" ffAD:%s", log_id(st.ffAD));

		if (st.ffB)
			log(" ffB:%s", log_id(st.ffB));

		if (st.ffC)
			log(" ffC:%s", log_id(st.ffC));

		if (st.ffD)
			log(" ffD:%s", log_id(st.ffD));

		if (st.ffM)
			log(" ffM:%s", log_id(st.ffM));

		if (st.ffP)
			log(" ffP:%s", log_id(st.ffP));

		log("\n");
	}

	SigSpec P = st.sigP;
	if (GetSize(P) < 48)
		P.append(pm.module->addWire(NEW_ID, 48-GetSize(P)));
	cell->setPort("\\P", P);

	bit_to_driver.insert(std::make_pair(P[0], cell));
	bit_to_driver.insert(std::make_pair(P[17], cell));

	pm.blacklist(cell);
}

struct XilinxDspPass : public Pass {
	XilinxDspPass() : Pass("xilinx_dsp", "Xilinx: pack resources into DSPs") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_dsp [options] [selection]\n");
		log("\n");
		log("Pack input registers (A, B, C, D, AD; with optional enable/reset), pipeline\n");
		log("registers (M; with optional enable/reset), output registers (P; with optional\n");
		log("enable/reset), pre-adder and/or post-adder into Xilinx DSP resources.\n");
		log("\n");
		log("Multiply-accumulate operations using the post-adder with feedback on the 'C'\n");
		log("input will be folded into the DSP. In this scenario only, the 'C' input can be\n");
		log("used to override the existing accumulation result with a new value.\n");
		log("\n");
		log("Use of the dedicated 'PCOUT' -> 'PCIN' path is detected for 'P' -> 'C' connections\n");
		log("where 'P' is right-shifted by 18-bits and used as an input to the post-adder (a\n");
		log("pattern common for summing partial products to implement wide multiplies).\n");
		log("\n");
		log("\n");
		log("Experimental feature: addition/subtractions less than 12 or 24 bits with the\n");
		log("'(* use_dsp=\"simd\" *)' attribute attached to the output wire or attached to\n");
		log("the add/subtract operator will cause those operations to be implemented using\n");
		log("the 'SIMD' feature of DSPs.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing XILINX_DSP pass (pack resources into DSPs).\n");

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
			pack_xilinx_simd(module, module->selected_cells());

			xilinx_dsp_pm pm(module, module->selected_cells());
			dict<SigBit, Cell*> bit_to_driver;
			auto f = [&bit_to_driver](xilinx_dsp_pm &pm){ pack_xilinx_dsp(bit_to_driver, pm); };
			pm.run_xilinx_dsp(f);

			auto &unextend = pm.ud_xilinx_dsp.unextend;
			// Look for ability to convert C input from another DSP into PCIN
			//   NB: Needs to be done after pattern matcher has folded all
			//       $add cells into the DSP
			for (auto cell : module->cells()) {
				if (cell->type != "\\DSP48E1")
					continue;
				if (cell->parameters.at("\\CREG", State::S1).as_bool())
					continue;
				SigSpec &opmode = cell->connections_.at("\\OPMODE");
				if (opmode.extract(4,3) != Const::from_string("011"))
					continue;
				SigSpec C = unextend(pm.sigmap(cell->getPort("\\C")));
				if (!C[0].wire)
					continue;
				auto it = bit_to_driver.find(C[0]);
				if (it == bit_to_driver.end())
					continue;
				auto driver = it->second;

				SigSpec P = driver->getPort("\\P");
				if (GetSize(P) >= GetSize(C) && P.extract(0, GetSize(C)) == C) {
					cell->setPort("\\C", Const(0, 48));
					Wire *cascade = module->addWire(NEW_ID, 48);
					driver->setPort("\\PCOUT", cascade);
					cell->setPort("\\PCIN", cascade);
					opmode[6] = State::S0;
					opmode[5] = State::S0;
					opmode[4] = State::S1;
					bit_to_driver.erase(it);
				}
				else if (GetSize(P) >= GetSize(C)+17 && P.extract(17, GetSize(C)) == C) {
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
