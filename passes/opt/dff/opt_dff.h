/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
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

#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "kernel/qcsat.h"
#include "kernel/modtools.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"

#ifndef OPT_DFF_H
#define OPT_DFF_H

YOSYS_NAMESPACE_BEGIN

struct OptDffOptions
{
	bool nosdff;
	bool nodffe;
	bool simple_dffe;
	bool sat;
	bool keepdc;
};

struct OptDffWorker
{
	const OptDffOptions &opt;
	Module *module;

	SigMap sigmap;                    // Signal aliasing
	FfInitVals initvals;

	SatEffortBudget sat_budget;
	bool sat_warned = false;

	// modwalker is expensive to build, so share one lazily between constbits and eqbits
	std::unique_ptr<ModWalker> modwalker_ptr;

	OptDffWorker(const OptDffOptions &opt, Module *mod);

	ModWalker &get_modwalker()
	{
		if (!modwalker_ptr)
			modwalker_ptr = std::make_unique<ModWalker>(module->design, module);
		return *modwalker_ptr;
	}

	bool warn_if_budget_spent()
	{
		if (!sat_budget.spent())
			return false;
		if (!sat_warned)
			log_warning("opt_dff -sat: solver effort budget for module %s is exhausted, leaving the "
					"remaining FFs un-optimized. Raise or clear the limit with the scratchpad "
					"option 'opt_dff.sat_effort' (0 disables it).\n", log_id(module));
		sat_warned = true;
		return true;
	}


	bool is_active(SigBit sig, bool pol) const {
		return sig == (pol ? State::S1 : State::S0);
	}

	bool is_inactive(SigBit sig, bool pol) const {
		return sig == (pol ? State::S0 : State::S1);
	}

	bool is_always_active(SigBit sig, bool pol) const {
		return is_active(sig, pol) || (!opt.keepdc && sig == State::Sx);
	}

	bool is_always_inactive(SigBit sig, bool pol) const {
		return is_inactive(sig, pol) || (!opt.keepdc && sig == State::Sx);
	}

	void remove_ff_bits(Cell *cell, const pool<int> &drop);

	bool run();
	bool run_constbits();
	bool run_eqbits();
};

YOSYS_NAMESPACE_END

#endif /* OPT_DFF_H */
