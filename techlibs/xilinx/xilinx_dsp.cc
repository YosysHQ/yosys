/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2019  Eddie Hung    <eddie@fpgeh.com>
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
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "techlibs/xilinx/xilinx_dsp_pm.h"
#include "techlibs/xilinx/xilinx_dsp48a_pm.h"
#include "techlibs/xilinx/xilinx_dsp_CREG_pm.h"
#include "techlibs/xilinx/xilinx_dsp_cascade_pm.h"

static Cell* addDsp(Module *module) {
	Cell *cell = module->addCell(NEW_TWINE, TW::DSP48E1);
	cell->setParam(ID(ACASCREG), 0);
	cell->setParam(ID(ADREG), 0);
	cell->setParam(ID(A_INPUT), Const("DIRECT"));
	cell->setParam(ID(ALUMODEREG), 0);
	cell->setParam(ID(AREG), 0);
	cell->setParam(ID(BCASCREG), 0);
	cell->setParam(ID(B_INPUT), Const("DIRECT"));
	cell->setParam(ID(BREG), 0);
	cell->setParam(ID(CARRYINREG), 0);
	cell->setParam(ID(CARRYINSELREG), 0);
	cell->setParam(ID(CREG), 0);
	cell->setParam(ID(DREG), 0);
	cell->setParam(ID(INMODEREG), 0);
	cell->setParam(ID(MREG), 0);
	cell->setParam(ID(OPMODEREG), 0);
	cell->setParam(ID(PREG), 0);
	cell->setParam(ID(USE_MULT), Const("NONE"));
	cell->setParam(ID(USE_SIMD), Const("ONE48"));
	cell->setParam(ID(USE_DPORT), Const("FALSE"));

	cell->setPort(TW::D, Const(0, 25));
	cell->setPort(TW::INMODE, Const(0, 5));
	cell->setPort(TW::ALUMODE, Const(0, 4));
	cell->setPort(TW::OPMODE, Const(0, 7));
	cell->setPort(TW::CARRYINSEL, Const(0, 3));
	cell->setPort(TW::ACIN, Const(0, 30));
	cell->setPort(TW::BCIN, Const(0, 18));
	cell->setPort(TW::PCIN, Const(0, 48));
	cell->setPort(TW::CARRYIN, Const(0, 1));
	return cell;
}

SigPool simd_signals(Module *module, SigMap* sigmap)
{
	SigPool simd_signals;
	// Mark representatives of wires that have the attribute
	for (auto wire : module->wires()) {
		SigSpec reps = (*sigmap)(wire);
		log_assert(reps.size() == wire->width);
		for (int i = 0; i < reps.size(); i++) {
			auto bit = reps[i];
			auto src_bit = SigBit(wire, i);
			if (src_bit.is_wire() && src_bit.wire->has_attribute(ID::use_dsp)) {
				auto use_dsp_tokens = split_tokens(src_bit.wire->attributes.at(ID::use_dsp).decode_string(), "|");
				if (std::find(use_dsp_tokens.begin(), use_dsp_tokens.end(), "simd") != use_dsp_tokens.end()) {
					simd_signals.add(bit);
				}
			}
		}
	}
	// Also mark all aliases of those representatives
	for (auto wire : module->wires()) {
		SigSpec reps = (*sigmap)(wire);
		log_assert(reps.size() == wire->width);
		for (int i = 0; i < reps.size(); i++) {
			auto bit = reps[i];
			auto src_bit = SigBit(wire, i);
			if (simd_signals.check(bit)) {
				simd_signals.add(src_bit);
			}
		}
	}
	// This seems silly, but that's generalized RTLIL for you!
	return simd_signals;
}

bool is_allowed(SigSpec& sig, SigPool& allowed_bits)
{
	for (auto bit : sig.bits()) {
		if (!allowed_bits.check(bit)) {
			return false;
		}
	}
	return true;
}

void xilinx_simd_pack(Module *module, SigMap* sigmap, const std::vector<Cell*> &selected_cells)
{
	std::deque<Cell*> simd12_add, simd12_sub;
	std::deque<Cell*> simd24_add, simd24_sub;

	SigPool simds = simd_signals(module, sigmap);

	for (auto cell : selected_cells) {
		if (!cell->type.in(TW($add), TW($sub)))
			continue;
		SigSpec Y = cell->getPort(TW::Y);
		if (!is_allowed(Y, simds))
			continue;
		if (GetSize(Y) > 25)
			continue;
		SigSpec A = cell->getPort(TW::A);
		SigSpec B = cell->getPort(TW::B);
		if (GetSize(Y) <= 13) {
			if (GetSize(A) > 12)
				continue;
			if (GetSize(B) > 12)
				continue;
			if (cell->type == TW($add))
				simd12_add.push_back(cell);
			else if (cell->type == TW($sub))
				simd12_sub.push_back(cell);
		}
		else if (GetSize(Y) <= 25) {
			if (GetSize(A) > 24)
				continue;
			if (GetSize(B) > 24)
				continue;
			if (cell->type == TW($add))
				simd24_add.push_back(cell);
			else if (cell->type == TW($sub))
				simd24_sub.push_back(cell);
		}
		else
			log_abort();
	}

	auto f12 = [module](SigSpec &AB, SigSpec &C, SigSpec &P, SigSpec &CARRYOUT, Cell *lane) {
		SigSpec A = lane->getPort(TW::A);
		SigSpec B = lane->getPort(TW::B);
		SigSpec Y = lane->getPort(TW::Y);
		A.extend_u0(12, lane->getParam(ID::A_SIGNED).as_bool());
		B.extend_u0(12, lane->getParam(ID::B_SIGNED).as_bool());
		AB.append(A);
		C.append(B);
		if (GetSize(Y) < 13)
			Y.append(module->addWire(NEW_TWINE, 13-GetSize(Y)));
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

			log("Analysing %s.%s for Xilinx DSP SIMD12 packing.\n", module, lane1);

			Cell *cell = addDsp(module);
			cell->setParam(ID(USE_SIMD), Const("FOUR12"));
			// X = A:B
			// Y = 0
			// Z = C
			cell->setPort(TW::OPMODE, Const::from_string("0110011"));

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
					P.append(module->addWire(NEW_TWINE, 12));
					CARRYOUT.append(module->addWire(NEW_TWINE, 1));
				}
			}
			else {
				AB.append(Const(0, 24));
				C.append(Const(0, 24));
				P.append(module->addWire(NEW_TWINE, 24));
				CARRYOUT.append(module->addWire(NEW_TWINE, 2));
			}
			log_assert(GetSize(AB) == 48);
			log_assert(GetSize(C) == 48);
			log_assert(GetSize(P) == 48);
			log_assert(GetSize(CARRYOUT) == 4);
			cell->setPort(TW::A, AB.extract(18, 30));
			cell->setPort(TW::B, AB.extract(0, 18));
			cell->setPort(TW::C, C);
			cell->setPort(TW::P, P);
			cell->setPort(TW::CARRYOUT, CARRYOUT);
			if (lane1->type == TW($sub))
				cell->setPort(TW::ALUMODE, Const::from_string("0011"));

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
		SigSpec A = lane->getPort(TW::A);
		SigSpec B = lane->getPort(TW::B);
		SigSpec Y = lane->getPort(TW::Y);
		A.extend_u0(24, lane->getParam(ID::A_SIGNED).as_bool());
		B.extend_u0(24, lane->getParam(ID::B_SIGNED).as_bool());
		C.append(A);
		AB.append(B);
		if (GetSize(Y) < 25)
			Y.append(module->addWire(NEW_TWINE, 25-GetSize(Y)));
		else
			log_assert(GetSize(Y) == 25);
		P.append(Y.extract(0, 24));
		CARRYOUT.append(module->addWire(NEW_TWINE)); // TWO24 uses every other bit
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

			log("Analysing %s.%s for Xilinx DSP SIMD24 packing.\n", module, lane1);

			Cell *cell = addDsp(module);
			cell->setParam(ID(USE_SIMD), Const("TWO24"));
			// X = A:B
			// Y = 0
			// Z = C
			cell->setPort(TW::OPMODE, Const::from_string("0110011"));

			log_assert(lane1);
			log_assert(lane2);
			f24(AB, C, P, CARRYOUT, lane1);
			f24(AB, C, P, CARRYOUT, lane2);
			log_assert(GetSize(AB) == 48);
			log_assert(GetSize(C) == 48);
			log_assert(GetSize(P) == 48);
			log_assert(GetSize(CARRYOUT) == 4);
			cell->setPort(TW::A, AB.extract(18, 30));
			cell->setPort(TW::B, AB.extract(0, 18));
			cell->setPort(TW::C, C);
			cell->setPort(TW::P, P);
			cell->setPort(TW::CARRYOUT, CARRYOUT);
			if (lane1->type == TW($sub))
				cell->setPort(TW::ALUMODE, Const::from_string("0011"));

			module->remove(lane1);
			module->remove(lane2);

			module->design->select(module, cell);
		}
	};
	g24(simd24_add);
	g24(simd24_sub);
}

void xilinx_dsp_pack(xilinx_dsp_pm &pm)
{
	auto &st = pm.st_xilinx_dsp_pack;

	log("Analysing %s.%s for Xilinx DSP packing.\n", pm.module, st.dsp);

	log_debug("preAdd:     %s\n", st.preAdd ? pm.module->design->twines.unescaped_str(st.preAdd->name.ref()) : "--");
	log_debug("preSub:     %s\n", st.preSub ? pm.module->design->twines.unescaped_str(st.preSub->name.ref()) : "--");
	log_debug("ffAD:       %s\n", st.ffAD ? pm.module->design->twines.unescaped_str(st.ffAD->name.ref()) : "--");
	log_debug("ffA2:       %s\n", st.ffA2 ? pm.module->design->twines.unescaped_str(st.ffA2->name.ref()) : "--");
	log_debug("ffA1:       %s\n", st.ffA1 ? pm.module->design->twines.unescaped_str(st.ffA1->name.ref()) : "--");
	log_debug("ffB2:       %s\n", st.ffB2 ? pm.module->design->twines.unescaped_str(st.ffB2->name.ref()) : "--");
	log_debug("ffB1:       %s\n", st.ffB1 ? pm.module->design->twines.unescaped_str(st.ffB1->name.ref()) : "--");
	log_debug("ffD:        %s\n", st.ffD ? pm.module->design->twines.unescaped_str(st.ffD->name.ref()) : "--");
	log_debug("dsp:        %s\n", st.dsp ? pm.module->design->twines.unescaped_str(st.dsp->name.ref()) : "--");
	log_debug("ffM:        %s\n", st.ffM ? pm.module->design->twines.unescaped_str(st.ffM->name.ref()) : "--");
	log_debug("postAdd:    %s\n", st.postAdd ? pm.module->design->twines.unescaped_str(st.postAdd->name.ref()) : "--");
	log_debug("postAddMux: %s\n", st.postAddMux ? pm.module->design->twines.unescaped_str(st.postAddMux->name.ref()) : "--");
	log_debug("ffP:        %s\n", st.ffP ? pm.module->design->twines.unescaped_str(st.ffP->name.ref()) : "--");
	log_debug("overflow:   %s\n", st.overflow ? pm.module->design->twines.unescaped_str(st.overflow->name.ref()) : "--");

	Cell *cell = st.dsp;

	if (st.preAdd || st.preSub) {
		Cell* preAdder = st.preAdd ? st.preAdd : st.preSub;

		log("  preadder %s (%s)\n", preAdder, pm.module->design->twines.unescaped_str(preAdder->type_impl));
		bool A_SIGNED = preAdder->getParam(ID::A_SIGNED).as_bool();
		bool D_SIGNED = preAdder->getParam(ID::B_SIGNED).as_bool();
		if (st.sigA == preAdder->getPort(TW::B))
			std::swap(A_SIGNED, D_SIGNED);
		st.sigA.extend_u0(30, A_SIGNED);
		st.sigD.extend_u0(25, D_SIGNED);
		cell->setPort(TW::A, st.sigA);
		cell->setPort(TW::D, st.sigD);
		if (preAdder->type == TW($add))
			cell->setPort(TW::INMODE, Const::from_string("00100"));
		else
			cell->setPort(TW::INMODE, Const::from_string("01100"));

		if (st.ffAD) {
			if (st.ffAD->type.in(TW($dffe), TW($sdffe))) {
				bool pol = st.ffAD->getParam(ID::EN_POLARITY).as_bool();
				SigSpec S = st.ffAD->getPort(TW::EN);
				cell->setPort(TW::CEAD, pol ? S : pm.module->Not(NEW_TWINE, S));
			}
			else
				cell->setPort(TW::CEAD, State::S1);
			cell->setParam(ID(ADREG), 1);
		}

		cell->setParam(ID(USE_DPORT), Const("TRUE"));

		pm.autoremove(preAdder);
	}
	if (st.postAdd) {
		log("  postadder %s (%s)\n", st.postAdd, pm.module->design->twines.unescaped_str(st.postAdd->type_impl));

		SigSpec &opmode = cell->connections_.at(TW::OPMODE);
		if (st.postAddMux) {
			log_assert(st.ffP);
			opmode[4] = st.postAddMux->getPort(TW::S);
			pm.autoremove(st.postAddMux);
		}
		else if (st.ffP && st.sigC == st.sigP)
			opmode[4] = State::S0;
		else
			opmode[4] = State::S1;
		opmode[6] = State::S0;
		opmode[5] = State::S1;

		if (opmode[4] != State::S0) {
			if (st.postAddMuxAB == ID::A)
				st.sigC.extend_u0(48, st.postAdd->getParam(ID::B_SIGNED).as_bool());
			else
				st.sigC.extend_u0(48, st.postAdd->getParam(ID::A_SIGNED).as_bool());
			cell->setPort(TW::C, st.sigC);
		}

		pm.autoremove(st.postAdd);
	}
	if (st.overflow) {
		log("  overflow %s (%s)\n", st.overflow, pm.module->design->twines.unescaped_str(st.overflow->type_impl));
		cell->setParam(ID(USE_PATTERN_DETECT), Const("PATDET"));
		cell->setParam(ID(SEL_PATTERN), Const("PATTERN"));
		cell->setParam(ID(SEL_MASK), Const("MASK"));

		if (st.overflow->type == TW($ge)) {
			Const B = st.overflow->getPort(TW::B).as_const();
			log_assert(std::count(B.begin(), B.end(), State::S1) == 1);
			// Since B is an exact power of 2, subtract 1
			//   by inverting all bits up until hitting
			//   that one hi bit
			for (auto b : B)
				if (b == State::S0) b = State::S1;
				else if (b == State::S1) {
					b = State::S0;
					break;
				}
			B.extu(48);

			cell->setParam(ID(MASK), B);
			cell->setParam(ID(PATTERN), Const(0, 48));
			cell->setPort(TW::OVERFLOW, st.overflow->getPort(TW::Y));
		}
		else log_abort();

		pm.autoremove(st.overflow);
	}

	if (st.clock != SigBit())
	{
		cell->setPort(TW::CLK, st.clock);

		auto f = [&pm,cell](SigSpec &A, Cell* ff, TwineRef ceport, TwineRef rstport) {
			SigSpec D = ff->getPort(TW::D);
			SigSpec Q = (*pm.sigmap)(ff->getPort(TW::Q));
			if (!A.empty())
				A.replace(Q, D);
			if (rstport != Twine::Null) {
				if (ff->type.in(TW($sdff), TW($sdffe))) {
					SigSpec srst = ff->getPort(TW::SRST);
					bool rstpol = ff->getParam(ID::SRST_POLARITY).as_bool();
					cell->setPort(rstport, rstpol ? srst : pm.module->Not(NEW_TWINE, srst));
				} else {
					cell->setPort(rstport, State::S0);
				}
			}
			if (ff->type.in(TW($dffe), TW($sdffe))) {
				SigSpec ce = ff->getPort(TW::EN);
				bool cepol = ff->getParam(ID::EN_POLARITY).as_bool();
				cell->setPort(ceport, cepol ? ce : pm.module->Not(NEW_TWINE, ce));
			}
			else
				cell->setPort(ceport, State::S1);

			for (auto c : Q.chunks()) {
				auto it = c.wire->attributes.find(ID::init);
				if (it == c.wire->attributes.end())
					continue;
				for (int i = c.offset; i < c.offset+c.width; i++) {
					log_assert(it->second[i] == State::S0 || it->second[i] == State::Sx);
					it->second.set(i, State::Sx);
				}
			}
		};

		if (st.ffA2) {
			SigSpec A = cell->getPort(TW::A);
			f(A, st.ffA2, TW::CEA2, TW::RSTA);
			if (st.ffA1) {
				f(A, st.ffA1, TW::CEA1, Twine::Null);
				cell->setParam(ID(AREG), 2);
				cell->setParam(ID(ACASCREG), 2);
			}
			else {
				cell->setParam(ID(AREG), 1);
				cell->setParam(ID(ACASCREG), 1);
			}
			pm.add_siguser(A, cell);
			cell->setPort(TW::A, A);
		}
		if (st.ffB2) {
			SigSpec B = cell->getPort(TW::B);
			f(B, st.ffB2, TW::CEB2, TW::RSTB);
			if (st.ffB1) {
				f(B, st.ffB1, TW::CEB1, Twine::Null);
				cell->setParam(ID(BREG), 2);
				cell->setParam(ID(BCASCREG), 2);
			}
			else {
				cell->setParam(ID(BREG), 1);
				cell->setParam(ID(BCASCREG), 1);
			}
			pm.add_siguser(B, cell);
			cell->setPort(TW::B, B);
		}
		if (st.ffD) {
			SigSpec D = cell->getPort(TW::D);
			f(D, st.ffD, TW::CED, TW::RSTD);
			pm.add_siguser(D, cell);
			cell->setPort(TW::D, D);
			cell->setParam(ID(DREG), 1);
		}
		if (st.ffM) {
			SigSpec M; // unused
			f(M, st.ffM, TW::CEM, TW::RSTM);
			st.ffM->connections_.at(TW::Q).replace(st.sigM, pm.module->addWire(NEW_TWINE, GetSize(st.sigM)));
			cell->setParam(ID(MREG), State::S1);
		}
		if (st.ffP) {
			SigSpec P; // unused
			f(P, st.ffP, TW::CEP, TW::RSTP);
			st.ffP->connections_.at(TW::Q).replace(st.sigP, pm.module->addWire(NEW_TWINE, GetSize(st.sigP)));
			cell->setParam(ID(PREG), State::S1);
		}

		log("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffA2) {
			log(" ffA2:%s", st.ffA2);
			if (st.ffA1)
				log(" ffA1:%s", st.ffA1);
		}

		if (st.ffAD)
			log(" ffAD:%s", st.ffAD);

		if (st.ffB2) {
			log(" ffB2:%s", st.ffB2);
			if (st.ffB1)
				log(" ffB1:%s", st.ffB1);
		}

		if (st.ffD)
			log(" ffD:%s", st.ffD);

		if (st.ffM)
			log(" ffM:%s", st.ffM);

		if (st.ffP)
			log(" ffP:%s", st.ffP);
	}
	log("\n");

	SigSpec P = st.sigP;
	if (GetSize(P) < 48)
		P.append(pm.module->addWire(NEW_TWINE, 48-GetSize(P)));
	cell->setPort(TW::P, P);

	pm.blacklist(cell);
}

void xilinx_dsp48a_pack(xilinx_dsp48a_pm &pm)
{
	auto &st = pm.st_xilinx_dsp48a_pack;

	log("Analysing %s.%s for Xilinx DSP48A/DSP48A1 packing.\n", pm.module, st.dsp);

	log_debug("preAdd:     %s\n", st.preAdd ? pm.module->design->twines.unescaped_str(st.preAdd->name.ref()) : "--");
	log_debug("ffA1:       %s\n", st.ffA1 ? pm.module->design->twines.unescaped_str(st.ffA1->name.ref()) : "--");
	log_debug("ffA0:       %s\n", st.ffA0 ? pm.module->design->twines.unescaped_str(st.ffA0->name.ref()) : "--");
	log_debug("ffB1:       %s\n", st.ffB1 ? pm.module->design->twines.unescaped_str(st.ffB1->name.ref()) : "--");
	log_debug("ffB0:       %s\n", st.ffB0 ? pm.module->design->twines.unescaped_str(st.ffB0->name.ref()) : "--");
	log_debug("ffD:        %s\n", st.ffD ? pm.module->design->twines.unescaped_str(st.ffD->name.ref()) : "--");
	log_debug("dsp:        %s\n", st.dsp ? pm.module->design->twines.unescaped_str(st.dsp->name.ref()) : "--");
	log_debug("ffM:        %s\n", st.ffM ? pm.module->design->twines.unescaped_str(st.ffM->name.ref()) : "--");
	log_debug("postAdd:    %s\n", st.postAdd ? pm.module->design->twines.unescaped_str(st.postAdd->name.ref()) : "--");
	log_debug("postAddMux: %s\n", st.postAddMux ? pm.module->design->twines.unescaped_str(st.postAddMux->name.ref()) : "--");
	log_debug("ffP:        %s\n", st.ffP ? pm.module->design->twines.unescaped_str(st.ffP->name.ref()) : "--");

	Cell *cell = st.dsp;
	SigSpec &opmode = cell->connections_.at(TW::OPMODE);

	if (st.preAdd) {
		log("  preadder %s (%s)\n", st.preAdd, pm.module->design->twines.unescaped_str(st.preAdd->type_impl));
		bool D_SIGNED = st.preAdd->getParam(ID::A_SIGNED).as_bool();
		bool B_SIGNED = st.preAdd->getParam(ID::B_SIGNED).as_bool();
		st.sigB.extend_u0(18, B_SIGNED);
		st.sigD.extend_u0(18, D_SIGNED);
		cell->setPort(TW::B, st.sigB);
		cell->setPort(TW::D, st.sigD);
		opmode[4] = State::S1;
		if (st.preAdd->type == TW($add))
			opmode[6] = State::S0;
		else if (st.preAdd->type == TW($sub))
			opmode[6] = State::S1;
		else
			log_assert(!"strange pre-adder type");

		pm.autoremove(st.preAdd);
	}
	if (st.postAdd) {
		log("  postadder %s (%s)\n", st.postAdd, pm.module->design->twines.unescaped_str(st.postAdd->type_impl));

		if (st.postAddMux) {
			log_assert(st.ffP);
			opmode[2] = st.postAddMux->getPort(TW::S);
			pm.autoremove(st.postAddMux);
		}
		else if (st.ffP && st.sigC == st.sigP)
			opmode[2] = State::S0;
		else
			opmode[2] = State::S1;
		opmode[3] = State::S1;

		if (opmode[2] != State::S0) {
			if (st.postAddMuxAB == ID::A)
				st.sigC.extend_u0(48, st.postAdd->getParam(ID::B_SIGNED).as_bool());
			else
				st.sigC.extend_u0(48, st.postAdd->getParam(ID::A_SIGNED).as_bool());
			cell->setPort(TW::C, st.sigC);
		}

		pm.autoremove(st.postAdd);
	}

	if (st.clock != SigBit())
	{
		cell->setPort(TW::CLK, st.clock);

		auto f = [&pm,cell](SigSpec &A, Cell* ff, TwineRef ceport, TwineRef rstport) {
			SigSpec D = ff->getPort(TW::D);
			SigSpec Q = (*pm.sigmap)(ff->getPort(TW::Q));
			if (!A.empty())
				A.replace(Q, D);
			if (rstport != Twine::Null) {
				if (ff->type.in(TW($sdff), TW($sdffe))) {
					SigSpec srst = ff->getPort(TW::SRST);
					bool rstpol = ff->getParam(ID::SRST_POLARITY).as_bool();
					cell->setPort(rstport, rstpol ? srst : pm.module->Not(NEW_TWINE, srst));
				} else {
					cell->setPort(rstport, State::S0);
				}
			}
			if (ff->type.in(TW($dffe), TW($sdffe))) {
				SigSpec ce = ff->getPort(TW::EN);
				bool cepol = ff->getParam(ID::EN_POLARITY).as_bool();
				cell->setPort(ceport, cepol ? ce : pm.module->Not(NEW_TWINE, ce));
			}
			else
				cell->setPort(ceport, State::S1);

			for (auto c : Q.chunks()) {
				auto it = c.wire->attributes.find(ID::init);
				if (it == c.wire->attributes.end())
					continue;
				for (int i = c.offset; i < c.offset+c.width; i++) {
					log_assert(it->second[i] == State::S0 || it->second[i] == State::Sx);
					it->second.set(i, State::Sx);
				}
			}
		};

		if (st.ffA0 || st.ffA1) {
			SigSpec A = cell->getPort(TW::A);
			if (st.ffA1) {
				f(A, st.ffA1, TW::CEA, TW::RSTA);
				cell->setParam(ID(A1REG), 1);
			}
			if (st.ffA0) {
				f(A, st.ffA0, TW::CEA, TW::RSTA);
				cell->setParam(ID(A0REG), 1);
			}
			pm.add_siguser(A, cell);
			cell->setPort(TW::A, A);
		}
		if (st.ffB0 || st.ffB1) {
			SigSpec B = cell->getPort(TW::B);
			if (st.ffB1) {
				f(B, st.ffB1, TW::CEB, TW::RSTB);
				cell->setParam(ID(B1REG), 1);
			}
			if (st.ffB0) {
				f(B, st.ffB0, TW::CEB, TW::RSTB);
				cell->setParam(ID(B0REG), 1);
			}
			pm.add_siguser(B, cell);
			cell->setPort(TW::B, B);
		}
		if (st.ffD) {
			SigSpec D = cell->getPort(TW::D);
			f(D, st.ffD, TW::CED, TW::RSTD);
			pm.add_siguser(D, cell);
			cell->setPort(TW::D, D);
			cell->setParam(ID(DREG), 1);
		}
		if (st.ffM) {
			SigSpec M; // unused
			f(M, st.ffM, TW::CEM, TW::RSTM);
			st.ffM->connections_.at(TW::Q).replace(st.sigM, pm.module->addWire(NEW_TWINE, GetSize(st.sigM)));
			cell->setParam(ID(MREG), State::S1);
		}
		if (st.ffP) {
			SigSpec P; // unused
			f(P, st.ffP, TW::CEP, TW::RSTP);
			st.ffP->connections_.at(TW::Q).replace(st.sigP, pm.module->addWire(NEW_TWINE, GetSize(st.sigP)));
			cell->setParam(ID(PREG), State::S1);
		}

		log("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffA0)
			log(" ffA0:%s", st.ffA0);
		if (st.ffA1)
			log(" ffA1:%s", st.ffA1);

		if (st.ffB0)
			log(" ffB0:%s", st.ffB0);
		if (st.ffB1)
			log(" ffB1:%s", st.ffB1);

		if (st.ffD)
			log(" ffD:%s", st.ffD);

		if (st.ffM)
			log(" ffM:%s", st.ffM);

		if (st.ffP)
			log(" ffP:%s", st.ffP);
	}
	log("\n");

	SigSpec P = st.sigP;
	if (GetSize(P) < 48)
		P.append(pm.module->addWire(NEW_TWINE, 48-GetSize(P)));
	cell->setPort(TW::P, P);

	pm.blacklist(cell);
}

void xilinx_dsp_packC(xilinx_dsp_CREG_pm &pm)
{
	auto &st = pm.st_xilinx_dsp_packC;

	log_debug("Analysing %s.%s for Xilinx DSP packing (CREG).\n", pm.module, st.dsp);
	log_debug("ffC:        %s\n", st.ffC ? pm.module->design->twines.unescaped_str(st.ffC->name.ref()) : "--");

	Cell *cell = st.dsp;

	if (st.clock != SigBit())
	{
		cell->setPort(TW::CLK, st.clock);

		auto f = [&pm,cell](SigSpec &A, Cell* ff, TwineRef ceport, TwineRef rstport) {
			SigSpec D = ff->getPort(TW::D);
			SigSpec Q = (*pm.sigmap)(ff->getPort(TW::Q));
			if (!A.empty())
				A.replace(Q, D);
			if (rstport != Twine::Null) {
				if (ff->type.in(TW($sdff), TW($sdffe))) {
					SigSpec srst = ff->getPort(TW::SRST);
					bool rstpol = ff->getParam(ID::SRST_POLARITY).as_bool();
					cell->setPort(rstport, rstpol ? srst : pm.module->Not(NEW_TWINE, srst));
				} else {
					cell->setPort(rstport, State::S0);
				}
			}
			if (ff->type.in(TW($dffe), TW($sdffe))) {
				SigSpec ce = ff->getPort(TW::EN);
				bool cepol = ff->getParam(ID::EN_POLARITY).as_bool();
				cell->setPort(ceport, cepol ? ce : pm.module->Not(NEW_TWINE, ce));
			}
			else
				cell->setPort(ceport, State::S1);

			for (auto c : Q.chunks()) {
				auto it = c.wire->attributes.find(ID::init);
				if (it == c.wire->attributes.end())
					continue;
				for (int i = c.offset; i < c.offset+c.width; i++) {
					log_assert(it->second[i] == State::S0 || it->second[i] == State::Sx);
					it->second.set(i, State::Sx);
				}
			}
		};

		if (st.ffC) {
			SigSpec C = cell->getPort(TW::C);
			f(C, st.ffC, TW::CEC, TW::RSTC);
			pm.add_siguser(C, cell);
			cell->setPort(TW::C, C);
			cell->setParam(ID(CREG), 1);
		}

		log("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffC)
			log(" ffC:%s", st.ffC);
		log("\n");
	}

	pm.blacklist(cell);
}

struct XilinxDspPass : public Pass {
	XilinxDspPass() : Pass("xilinx_dsp", "Xilinx: pack resources into DSPs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_dsp [options] [selection]\n");
		log("\n");
		log("Pack input registers (A2, A1, B2, B1, C, D, AD; with optional enable/reset),\n");
		log("pipeline registers (M; with optional enable/reset), output registers (P; with\n");
		log("optional enable/reset), pre-adder and/or post-adder into Xilinx DSP resources.\n");
		log("\n");
		log("Multiply-accumulate operations using the post-adder with feedback on the 'C'\n");
		log("input will be folded into the DSP. In this scenario only, the 'C' input can be\n");
		log("used to override the current accumulation result with a new value, which will\n");
		log("be added to the multiplier result to form the next accumulation result.\n");
		log("\n");
		log("Use of the dedicated 'PCOUT' -> 'PCIN' cascade path is detected for 'P' -> 'C'\n");
		log("connections (optionally, where 'P' is right-shifted by 17-bits and used as an\n");
		log("input to the post-adder -- a pattern common for summing partial products to\n");
		log("implement wide multipliers). Limited support also exists for similar cascading\n");
		log("for A and B using '[AB]COUT' -> '[AB]CIN'. Currently, cascade chains are limited\n");
		log("to a maximum length of 20 cells, corresponding to the smallest Xilinx 7 Series\n");
		log("device.\n");
		log("\n");
		log("This pass is a no-op if the scratchpad variable 'xilinx_dsp.multonly' is set\n");
		log("to 1.\n");
		log("\n");
		log("\n");
		log("Experimental feature: addition/subtractions less than 12 or 24 bits with the\n");
		log("'(* use_dsp=\"simd\" *)' attribute attached to the output wire or attached to\n");
		log("the add/subtract operator will cause those operations to be implemented using\n");
		log("the 'SIMD' feature of DSPs.\n");
		log("\n");
		log("Experimental feature: the presence of a `$ge' cell attached to the registered\n");
		log("P output implementing the operation \"(P >= <power-of-2>)\" will be transformed\n");
		log("into using the DSP48E1's pattern detector feature for overflow detection.\n");
		log("\n");
		log("    -family {xcup|xcu|xc7|xc6v|xc5v|xc4v|xc6s|xc3sda}\n");
		log("        select the family to target\n");
		log("        default: xc7\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing XILINX_DSP pass (pack resources into DSPs).\n");

		std::string family = "xc7";
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if ((args[argidx] == "-family" || args[argidx] == "-arch") && argidx+1 < args.size()) {
				family = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Don't bother distinguishing between those.
		if (family == "xc6v")
			family = "xc7";
		if (family == "xcup")
			family = "xcu";

		for (auto module : design->selected_modules()) {

			if (design->scratchpad_get_bool("xilinx_dsp.multonly"))
				continue;

			SigMap sigmap(module);
			// Experimental feature: pack $add/$sub cells with
			//   (* use_dsp48="simd" *) into DSP48E1's using its
			//   SIMD feature
			if (family == "xc7")
				xilinx_simd_pack(module, &sigmap, module->selected_cells());

			// Match for all features ([ABDMP][12]?REG, pre-adder,
			// post-adder, pattern detector, etc.) except for CREG
			if (family == "xc7") {
				xilinx_dsp_pm pm(module, &sigmap, module->selected_cells());
				pm.run_xilinx_dsp_pack(xilinx_dsp_pack);
			} else if (family == "xc6s" || family == "xc3sda") {
				xilinx_dsp48a_pm pm(module, &sigmap, module->selected_cells());
				pm.run_xilinx_dsp48a_pack(xilinx_dsp48a_pack);
			}
			// Separating out CREG packing is necessary since there
			//   is no guarantee that the cell ordering corresponds
			//   to the "expected" case (i.e. the order in which
			//   they appear in the source) thus the possiblity
			//   existed that a register got packed as a CREG into a
			//   downstream DSP that should have otherwise been a
			//   PREG of an upstream DSP that had not been visited
			//   yet
			{
				xilinx_dsp_CREG_pm pm(module, &sigmap, module->selected_cells());
				pm.run_xilinx_dsp_packC(xilinx_dsp_packC);
			}
			// Lastly, identify and utilise PCOUT -> PCIN,
			//   ACOUT -> ACIN, and BCOUT-> BCIN dedicated cascade
			//   chains
			{
				xilinx_dsp_cascade_pm pm(module, &sigmap, module->selected_cells());
				pm.run_xilinx_dsp_cascade();
			}
		}
	}
} XilinxDspPass;

PRIVATE_NAMESPACE_END
