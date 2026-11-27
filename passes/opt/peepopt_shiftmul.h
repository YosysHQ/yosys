#ifndef PEEPOPT_SHIFTMUL_H
#define PEEPOPT_SHIFTMUL_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

// Strip a signed shift amount down to its significant bits, counting the
// trailing zeros into log2scale. Returns false when the pattern does not apply.
inline bool peepopt_shiftmul_normalize(SigSpec &shift_amount, int &log2scale)
{
	// at this point shift_amount is signed, make
	// sure we can never go negative
	if (shift_amount.bits().back() != State::S0)
		return false;

	while (shift_amount.bits().back() == State::S0) {
		shift_amount.remove(GetSize(shift_amount) - 1);
		if (shift_amount.empty()) return false;
	}

	log2scale = 0;
	while (shift_amount[0] == State::S0) {
		shift_amount.remove(0);
		if (shift_amount.empty()) return false;
		log2scale++;
	}

	if (GetSize(shift_amount) > 20)
		return false;

	return true;
}

template <typename Pattern>
void peepopt_shiftmul_match_mul(Pattern &pm, const typename Pattern::Match &m)
{
	MatchFrame frame(pm.ctx);
	for (auto &[mul, constport, varport] : pm.candidates(pm.mul_index.find(m.shift_amount))) {
		if (pm.param(mul, ID::A_SIGNED).as_bool())
			continue;
		if (!pm.port(mul, constport).is_fully_const())
			continue;
		typename Pattern::Match n = m;
		n.mul = mul;
		n.mul_const = SigSpec({pm.port(mul, constport), SigSpec(State::S0, n.log2scale)}).as_const();
		// get mul_din unmapped (so no `port()` shorthand)
		// because we will be using it to set the \A port
		// on the shift cell, and we want to stay close
		// to the original design
		n.mul_din = mul->getPort(varport);
		if (pm.descend(frame, mul, &Pattern::code_rewrite, n))
			return;
	}
}

YOSYS_NAMESPACE_END

#endif
