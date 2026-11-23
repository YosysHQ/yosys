#ifndef XILINX_DSP_CASCADE_H
#define XILINX_DSP_CASCADE_H

#include "techlibs/xilinx/xilinx_dsp_common.h"

YOSYS_NAMESPACE_BEGIN

// This file describes the third of three pattern matcher setups that
//   forms the `xilinx_dsp` pass described in xilinx_dsp.cc
// At a high level, it works as follows:
//   (1) Starting from a DSP48E1 cell that (a) has the Z multiplexer
//       (controlled by OPMODE[6:4]) set to zero and (b) doesn't already
//       use the 'PCOUT' port
//   (2.1) Match another DSP48E1 cell that (a) does not have the CREG enabled,
//         (b) has its Z multiplexer output set to the 'C' port, which is
//         driven by the 'P' output of the previous DSP cell, and (c) has its
//         'PCIN' port unused
//   (2.2) Same as (2.1) but with the 'C' port driven by the 'P' output of the
//         previous DSP cell right-shifted by 17 bits
//   (3) For this subequent DSP48E1 match (i.e. PCOUT -> PCIN cascade exists)
//       if (a) the previous DSP48E1 uses either the A2REG or A1REG, (b) this
//       DSP48 does not use A2REG nor A1REG, (c) this DSP48E1 does not already
//       have an ACOUT -> ACIN cascade, (d) the previous DSP does not already
//       use its ACOUT port, then examine if an ACOUT -> ACIN cascade
//       opportunity exists by matching for a $dff-with-optional-clock-enable-
//       or-reset and checking that the 'D' input of this register is the same
//       as the 'A' input of the previous DSP
//   (4) Same as (3) but for BCOUT -> BCIN cascade
//   (5) Recursively go to (2.1) until no more matches possible, keeping track
//       of the longest possible chain found
//   (6) The longest chain is then divided into chunks of no more than
//       MAX_DSP_CASCADE in length (to prevent long cascades that exceed the
//       height of a DSP column) with each DSP in each chunk being rewritten
//       to use [ABP]COUT -> [ABP]CIN cascading as appropriate
// Notes:
//   - Currently, [AB]COUT -> [AB]COUT cascades (3 or 4) are only considered
//     if a PCOUT -> PCIN cascade is (2.1 or 2.2) first identified; this need
//     not be the case --- [AB] cascades can exist independently of a P cascade
//     (though all three cascades must come from the same DSP). This situation
//     is not handled currently.
//   - In addition, [AB]COUT -> [AB]COUT cascades (3 or 4) are currently
//     conservative in that they examine the situation where (a) the previous
//     DSP has [AB]2REG or [AB]1REG enabled, (b) that the downstream DSP has no
//     registers enabled, and (c) that there exists only one additional register
//     between the upstream and downstream DSPs. This can certainly be relaxed
//     to identify situations ranging from (i) neither DSP uses any registers,
//     to (ii) upstream DSP has 2 registers, downstream DSP has 2 registers, and
//     there exists a further 2 registers between them. This remains a TODO
//     item.

struct XilinxDspCascadeMatch
{
	Cell *next = nullptr;
	int AREG = {};
	int BREG = {};
	Cell *first = nullptr;
	Cell *nextP = nullptr;
	Cell *nextP_shift17 = nullptr;
};

struct XilinxDspCascade : MatchPattern<XilinxDspCascade, XilinxDspCascadeMatch>
{
	static constexpr int MAX_DSP_CASCADE = 20;

	vector<std::tuple<Cell*,int,int,int>> chain = {};
	vector<std::tuple<Cell*,int,int,int>> longest_chain = {};

	vector<Cell*> first_cells = {};
	MatchIndex<SigBit> nextP_index = {};
	MatchIndex<SigBit> nextP_shift17_index = {};
	XilinxDspFfIndex ff_index = {};

	XilinxDspCascade(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &XilinxDspCascade::match_first)
	{
		for (auto cell : cells) {
			if (((cell->type.in(ID::DSP48A, ID::DSP48A1) && port(cell, ID::OPMODE, Const(0, 8)).extract(2,2) == Const::from_string("00")) || (cell->type.in(ID::DSP48E1) && port(cell, ID::OPMODE, Const(0, 7)).extract(4,3) == Const::from_string("000"))) &&
					nusers(port(cell, ID::PCOUT, SigSpec())) <= 1)
				first_cells.push_back(cell);
			if ((!cell->type.in(ID::DSP48E1) || !param(cell, ID::CREG).as_bool()) &&
					((cell->type.in(ID::DSP48A, ID::DSP48A1) && port(cell, ID::OPMODE, Const(0, 8)).extract(2,2) == Const::from_string("11")) || (cell->type.in(ID::DSP48E1) && port(cell, ID::OPMODE, Const(0, 7)).extract(4,3) == Const::from_string("011"))) &&
					nusers(port(cell, ID::C, SigSpec())) > 1 &&
					nusers(port(cell, ID::PCIN, SigSpec())) == 0)
				nextP_index.add(port(cell, ID::C)[0], cell);
			if (cell->type.in(ID::DSP48E1) &&
					!param(cell, ID::CREG).as_bool() &&
					port(cell, ID::OPMODE, Const(0, 7)).extract(4,3) == Const::from_string("011") &&
					nusers(port(cell, ID::C, SigSpec())) > 1 &&
					nusers(port(cell, ID::PCIN, SigSpec())) == 0)
				nextP_shift17_index.add(port(cell, ID::C)[0], cell);
			ff_index.add_input(*this, cell);
		}
	}

	bool acascade_dff_compatible(const XilinxDspFf &dff, Cell *prev) const
	{
		if (!dff.cell->type.in(ID($sdff), ID($sdffe)) && port(prev, ID::RSTA, State::S0) != State::S0)
			return false;
		if (dff.cell->type.in(ID($sdff), ID($sdffe)) && (port(dff.cell, ID::SRST) != port(prev, ID::RSTA, State::S0) || !param(dff.cell, ID::SRST_POLARITY).as_bool()))
			return false;
		IdString CEA = {};
		if (param(prev, ID::AREG) == 1)
			CEA = ID::CEA2;
		else if (param(prev, ID::AREG) == 2)
			CEA = ID::CEA1;
		else log_abort();
		if (!dff.cell->type.in(ID($dffe), ID($sdffe)) && port(prev, CEA, State::S0) != State::S1)
			return false;
		if (dff.cell->type.in(ID($dffe), ID($sdffe)) && (port(dff.cell, ID::EN) != port(prev, CEA, State::S0) || !param(dff.cell, ID::EN_POLARITY).as_bool()))
			return false;
		return dff.sig == xilinx_dsp_unextend(port(prev, ID::A));
	}

	bool bcascade_dff_compatible(const XilinxDspFf &dff, Cell *next, Cell *prev) const
	{
		if (!dff.cell->type.in(ID($sdff), ID($sdffe)) && port(prev, ID::RSTB, State::S0) != State::S0)
			return false;
		if (dff.cell->type.in(ID($sdff), ID($sdffe)) && (port(dff.cell, ID::SRST) != port(prev, ID::RSTB, State::S0) || !param(dff.cell, ID::SRST_POLARITY).as_bool()))
			return false;
		IdString CEB = {};
		if (next->type.in(ID::DSP48A, ID::DSP48A1))
			CEB = ID::CEB;
		else if (next->type.in(ID::DSP48E1)) {
			if (param(prev, ID::BREG) == 1)
				CEB = ID::CEB2;
			else if (param(prev, ID::BREG) == 2)
				CEB = ID::CEB1;
			else log_abort();
		}
		else log_abort();
		if (!dff.cell->type.in(ID($dffe), ID($sdffe)) && port(prev, CEB, State::S0) != State::S1)
			return false;
		if (dff.cell->type.in(ID($dffe), ID($sdffe)) && (port(dff.cell, ID::EN) != port(prev, CEB, State::S0) || !param(dff.cell, ID::EN_POLARITY).as_bool()))
			return false;
		if (dff.sig == xilinx_dsp_unextend(port(prev, ID::B))) {
			if (next->type.in(ID::DSP48A, ID::DSP48A1) && param(prev, ID::B0REG) != 0)
				return false;
			return true;
		}
		return false;
	}

	// (1) Starting from a DSP48* cell that (a) has the Z multiplexer
	//     (controlled by OPMODE[3:2] for DSP48A*, by OPMODE[6:4] for DSP48E1)
	//     set to zero and (b) doesn't already use the 'PCOUT' port
	void match_first(const Match &m)
	{
		match_each(m, first_cells, &Match::first, &XilinxDspCascade::code_chain);
	}

	// (6) The longest chain is then divided into chunks of no more than
	//     MAX_DSP_CASCADE in length (to prevent long cascades that exceed the
	//     height of a DSP column) with each DSP in each chunk being rewritten
	//     to use [ABP]COUT -> [ABP]CIN cascading as appropriate
	void code_chain(const Match &m)
	{
		longest_chain.clear();
		chain.emplace_back(m.first, -1, -1, -1);
		tail(m);

		chain.pop_back();
		log_assert(chain.empty());
		if (GetSize(longest_chain) > 1) {
			Cell *dsp = std::get<0>(longest_chain.front());

			Cell *dsp_pcin = nullptr;
			int P = {}, AREG = {}, BREG = {};
			for (int i = 1; i < GetSize(longest_chain); i++) {
				std::tie(dsp_pcin,P,AREG,BREG) = longest_chain[i];

				if (i % MAX_DSP_CASCADE > 0) {
					if (P >= 0) {
						Wire *cascade = module->addWire(NEW_ID, 48);
						dsp_pcin->setPort(ID::C, Const(0, 48));
						dsp_pcin->setPort(ID::PCIN, cascade);
						dsp->setPort(ID::PCOUT, cascade);
						add_siguser(cascade, dsp_pcin);
						add_siguser(cascade, dsp);

						SigSpec opmode = port(dsp_pcin, ID::OPMODE, Const(0, 7));
						if (dsp->type.in(ID::DSP48A, ID::DSP48A1)) {
							log_assert(P == 0);
							opmode[3] = State::S0;
							opmode[2] = State::S1;
						}
						else if (dsp->type.in(ID::DSP48E1)) {
							if (P == 17)
								opmode[6] = State::S1;
							else if (P == 0)
								opmode[6] = State::S0;
							else log_abort();

							opmode[5] = State::S0;
							opmode[4] = State::S1;
						}
						dsp_pcin->setPort(ID::OPMODE, opmode);

						log_debug("PCOUT -> PCIN cascade for %s -> %s\n", dsp, dsp_pcin);
					}
					if (AREG >= 0) {
						Wire *cascade = module->addWire(NEW_ID, 30);
						dsp_pcin->setPort(ID::A, Const(0, 30));
						dsp_pcin->setPort(ID::ACIN, cascade);
						dsp->setPort(ID::ACOUT, cascade);
						add_siguser(cascade, dsp_pcin);
						add_siguser(cascade, dsp);

						if (dsp->type.in(ID::DSP48E1))
							dsp->setParam(ID::ACASCREG, AREG);
						dsp_pcin->setParam(ID::A_INPUT, Const("CASCADE"));

						log_debug("ACOUT -> ACIN cascade for %s -> %s\n", dsp, dsp_pcin);
					}
					if (BREG >= 0) {
						Wire *cascade = module->addWire(NEW_ID, 18);
						if (dsp->type.in(ID::DSP48A, ID::DSP48A1)) {
							// According to UG389 p9 [https://www.xilinx.com/support/documentation/user_guides/ug389.pdf]
							// "The DSP48A1 component uses this input when cascading
							//   BCOUT from an adjacent DSP48A1 slice. The tools then
							//   translate BCOUT cascading to the dedicated BCIN input
							//   and set the B_INPUT attribute for implementation."
							dsp_pcin->setPort(ID::B, cascade);
						}
						else {
							dsp_pcin->setPort(ID::B, Const(0, 18));
							dsp_pcin->setPort(ID::BCIN, cascade);
						}
						dsp->setPort(ID::BCOUT, cascade);
						add_siguser(cascade, dsp_pcin);
						add_siguser(cascade, dsp);

						if (dsp->type.in(ID::DSP48E1)) {
							dsp->setParam(ID::BCASCREG, BREG);
							// According to UG389 p13 [https://www.xilinx.com/support/documentation/user_guides/ug389.pdf]
							// "The attribute is only used by place and route tools and
							//   is not necessary for the users to set for synthesis. The
							//   attribute is determined by the connection to the B port
							//   of the DSP48A1 slice. If the B port is connected to the
							//   BCOUT of another DSP48A1 slice, then the tools automatically
							//   set the attribute to 'CASCADE', otherwise it is set to
							//   'DIRECT'".
							dsp_pcin->setParam(ID::B_INPUT, Const("CASCADE"));
						}

						log_debug("BCOUT -> BCIN cascade for %s -> %s\n", dsp, dsp_pcin);
					}
				}
				else {
					log_debug("  Blocking %s -> %s cascade (exceeds max: %d)\n", dsp, dsp_pcin, MAX_DSP_CASCADE);
				}

				dsp = dsp_pcin;
			}

			accept(m);
		}
	}

	// ------------------------------------------------------------------

	// (2.1) Match another DSP48* cell that (a) does not have the CREG enabled,
	//       (b) has its Z multiplexer output set to the 'C' port, which is
	//       driven by the 'P' output of the previous DSP cell, and (c) has its
	//       'PCIN' port unused
	void tail(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *nextP : candidates(nextP_index.find(port(std::get<0>(chain.back()), ID::P)[0]))) {
			found_any_match = true;
			Match n = m;
			n.nextP = nextP;
			if (descend(frame, nextP, &XilinxDspCascade::tail_match_nextP_shift17, n))
				return;
		}
		if (!found_any_match) {
			Match n = m;
			n.nextP = nullptr;
			tail_match_nextP_shift17(n);
		}
	}

	// (2.2) For DSP48E1 only, same as (2.1) but with the 'C' port driven
	//       by the 'P' output of the previous DSP cell right-shifted by 17 bits
	void tail_match_nextP_shift17(const Match &m)
	{
		if (m.nextP) {
			Match n = m;
			n.nextP_shift17 = nullptr;
			tail_code_next(n);
			return;
		}
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *nextP_shift17 : candidates(nextP_shift17_index.find(port(std::get<0>(chain.back()), ID::P)[17]))) {
			found_any_match = true;
			Match n = m;
			n.nextP_shift17 = nextP_shift17;
			if (descend(frame, nextP_shift17, &XilinxDspCascade::tail_code_next, n))
				return;
		}
		if (!found_any_match) {
			Match n = m;
			n.nextP_shift17 = nullptr;
			tail_code_next(n);
		}
	}

	void tail_code_next(const Match &m)
	{
		Match n = m;
		n.next = n.nextP;
		if (!n.nextP)
			n.next = n.nextP_shift17;
		if (n.next && n.next->type != n.first->type)
			return;
		tail_code_AREG(n);
	}

	// (3) For this subequent DSP48E1 match (i.e. PCOUT -> PCIN cascade exists)
	//     if (a) this DSP48E1 does not already have an ACOUT -> ACIN cascade,
	//     (b) the previous DSP does  not already use its ACOUT port, then
	//     examine if an ACOUT -> ACIN cascade  opportunity exists if
	//     (i) A ports are identical, or (ii) separated by a
	//     $dff-with-optional-clock-enable-or-reset and checking that the 'D' input
	//     of this register is the same as the 'A' input of the previous DSP
	//     TODO: Check for two levels of flops, instead of just one
	void tail_code_AREG(const Match &m)
	{
		Match n = m;
		n.AREG = -1;
		if (n.next && n.next->type.in(ID::DSP48E1)) {
			Cell *prev = std::get<0>(chain.back());

			if (param(n.next, ID::A_INPUT).decode_string() == "DIRECT" &&
					port(n.next, ID::ACIN, SigSpec()).is_fully_zero() &&
					nusers(port(prev, ID::ACOUT, SigSpec())) <= 1) {
				if (param(prev, ID::AREG) == 0) {
					if (port(prev, ID::A) == port(n.next, ID::A))
						n.AREG = 0;
				}
				else {
					SigSpec argQ = xilinx_dsp_unextend(port(n.next, ID::A));
					SigBit clock = port(prev, ID::CLK);
					XilinxDspFf areg = ff_index.in_dffe(*this, argQ, clock);
					if (areg.cell && acascade_dff_compatible(areg, prev))
						n.AREG = 1;
				}
			}
		}
		tail_code_BREG(n);
	}

	// (4) Same as (3) but for BCOUT -> BCIN cascade
	void tail_code_BREG(const Match &m)
	{
		Match n = m;
		n.BREG = -1;
		if (n.next) {
			Cell *prev = std::get<0>(chain.back());
			if ((n.next->type != ID::DSP48E1 || param(n.next, ID::B_INPUT).decode_string() == "DIRECT") &&
					port(n.next, ID::BCIN, SigSpec()).is_fully_zero() &&
					nusers(port(prev, ID::BCOUT, SigSpec())) <= 1) {
				if ((n.next->type.in(ID::DSP48A, ID::DSP48A1) && param(prev, ID::B0REG) == 0 && param(prev, ID::B1REG) == 0) ||
					(n.next->type.in(ID::DSP48E1) && param(prev, ID::BREG) == 0)) {
					if (port(prev, ID::B) == port(n.next, ID::B))
						n.BREG = 0;
				}
				else {
					SigSpec argQ = xilinx_dsp_unextend(port(n.next, ID::B));
					SigBit clock = port(prev, ID::CLK);
					XilinxDspFf breg = ff_index.in_dffe(*this, argQ, clock);
					if (breg.cell && bcascade_dff_compatible(breg, n.next, prev))
						n.BREG = 1;
				}
			}
		}
		tail_code_chain(n);
	}

	// (5) Recursively go to (2.1) until no more matches possible, recording the
	//     longest possible chain
	void tail_code_chain(const Match &m)
	{
		if (m.next) {
			chain.emplace_back(m.next, m.nextP_shift17 ? 17 : m.nextP ? 0 : -1, m.AREG, m.BREG);

			SigSpec sigC = xilinx_dsp_unextend(port(m.next, ID::C));

			if (m.nextP_shift17) {
				if (GetSize(sigC)+17 <= GetSize(port(std::get<0>(chain.back()), ID::P)) &&
						port(std::get<0>(chain.back()), ID::P).extract(17, GetSize(sigC)) != sigC)
					tail(m);
			}
			else {
				if (GetSize(sigC) <= GetSize(port(std::get<0>(chain.back()), ID::P)) &&
						port(std::get<0>(chain.back()), ID::P).extract(0, GetSize(sigC)) != sigC)
					tail(m);

			}
		} else {
			if (GetSize(chain) > GetSize(longest_chain))
				longest_chain = chain;
		}

		if (m.next)
			chain.pop_back();
	}
};

YOSYS_NAMESPACE_END

#endif
