#ifndef XILINX_DSP_STAGES_H
#define XILINX_DSP_STAGES_H

#include "techlibs/common/dsp_ff.h"

YOSYS_NAMESPACE_BEGIN

// Stages shared by the DSP48E1 and DSP48A patterns

template <typename Pattern>
void xilinx_dsp_code_ffM(Pattern &pm, const typename Pattern::Match &m)
{
	using Match = typename Pattern::Match;
	Match n = m;
	if (pm.param(n.dsp, ID::MREG).as_int() == 0 && pm.nusers(n.sigM) == 2) {
		pm.ff_index.absorb_out(pm, n, &Match::ffM, &Match::sigM);
	}
	n.sigP = n.sigM;
	pm.match_postAdd(n);
}

template <typename Pattern>
void xilinx_dsp_match_postAdd(Pattern &pm, const typename Pattern::Match &m, bool z_mux_unused)
{
	using Match = typename Pattern::Match;
	if (z_mux_unused) {
		MatchFrame frame(pm.ctx);
		for (auto &[postAdd, AB] : pm.candidates(pm.postAdd_index.find(m.sigP[0]))) {
			if (GetSize(pm.port(postAdd, AB)) < GetSize(m.sigP))
				continue;
			if (pm.port(postAdd, AB).extract(0, GetSize(m.sigP)) != m.sigP)
				continue;
			// Check that remainder of AB is a sign- or zero-extension
			if (!dsp_is_extension_of(pm.port(postAdd, AB), m.sigP))
				continue;
			Match n = m;
			n.postAdd = postAdd;
			n.postAddAB = AB;
			if (pm.descend(frame, postAdd, &Pattern::code_postAdd, n))
				return;
		}
	}
	pm.match_none(m, &Match::postAdd, &Pattern::code_postAdd);
}

template <typename Pattern>
void xilinx_dsp_code_postAdd(Pattern &pm, const typename Pattern::Match &m)
{
	typename Pattern::Match n = m;
	if (n.postAdd) {
		n.sigC = pm.port(n.postAdd, n.postAddAB == ID::A ? ID::B : ID::A);
		n.sigP = pm.port(n.postAdd, ID::Y);
	}
	pm.code_ffP(n);
}

template <typename Pattern>
void xilinx_dsp_code_ffP(Pattern &pm, const typename Pattern::Match &m)
{
	using Match = typename Pattern::Match;
	Match n = m;
	if (pm.param(n.dsp, ID::PREG).as_int() == 0) {
		if (pm.nusers(n.sigP) == 2) {
			pm.ff_index.absorb_out(pm, n, &Match::ffP, &Match::sigP);
		}
	}
	pm.match_postAddMux(n);
}

template <typename Pattern>
void xilinx_dsp_match_postAddMux(Pattern &pm, const typename Pattern::Match &m)
{
	using Match = typename Pattern::Match;
	if (m.postAdd && m.ffP) {
		MatchFrame frame(pm.ctx);
		for (auto &[postAddMux, AB] : pm.candidates(pm.postAddMux_index.find({m.sigP, m.sigC}))) {
			Match n = m;
			n.postAddMux = postAddMux;
			n.postAddMuxAB = AB;
			if (pm.descend(frame, postAddMux, &Pattern::code_postAddMux, n))
				return;
		}
	}
	pm.match_none(m, &Match::postAddMux, &Pattern::code_postAddMux);
}

YOSYS_NAMESPACE_END

#endif
