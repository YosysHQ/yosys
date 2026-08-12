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
#include "kernel/ff.h"
#include "kernel/pattern.h"

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

	// Cell to port bit index
	typedef std::pair<RTLIL::Cell*, int> cell_int_t;

	SigMap sigmap;                    // Signal aliasing
	FfInitVals initvals;
	dict<SigBit, int> bitusers;       // Signal sink count
	dict<SigBit, cell_int_t> bit2mux; // Signal bit to driving MUX

	std::vector<Cell *> dff_cells;

	// opt_dff -sat rebuilds the solver in batches of at most this many imported
	// cells, so one pathological module can't grow a single giant solver
	static constexpr int sat_batch_cells = 10000;

	SatEffortBudget sat_budget;
	bool sat_warned = false;

	// modwalker is expensive to build, so share one lazily between constbits and eqbits
	std::unique_ptr<ModWalker> modwalker_ptr;

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

	OptDffWorker(const OptDffOptions &opt, Module *mod);

	void remove_ff_bits(Cell *cell, const pool<int> &drop);

	SigSpec create_not(SigSpec a, bool is_fine);
	SigSpec create_and(SigSpec a, SigSpec b, bool is_fine);
	void create_mux_to_output(SigSpec a, SigSpec b, SigSpec sel, SigSpec y, bool pol, bool is_fine);
	void maybe_simplemap(Cell *c, bool make_gates);
	patterns_t find_muxtree_feedback_patterns(RTLIL::SigBit d, RTLIL::SigBit q, pattern_t path);
	ctrl_t make_patterns_logic(const patterns_t &patterns, const ctrls_t &ctrls, bool make_gates);
	ctrl_t combine_resets(const ctrls_t &ctrls, bool make_gates);
	bool signal_all_same(const SigSpec &sig);
	bool optimize_sr(FfData &ff, Cell *cell, bool &changed);
	bool optimize_aload(FfData &ff, Cell *cell, bool &changed);
	bool optimize_arst(FfData &ff, Cell *cell, bool &changed);
	void optimize_srst(FfData &ff, Cell *cell, bool &changed);
	void optimize_ce(FfData &ff, Cell *cell, bool &changed);
	void optimize_const_clk(FfData &ff, Cell *cell, bool &changed);
	void optimize_d_equals_q(FfData &ff, Cell *cell, bool &changed);
	bool try_merge_srst(FfData &ff, Cell *cell, bool &changed);
	bool try_merge_ce(FfData &ff, Cell *cell, bool &changed);
	bool run();

	struct ConstObligation;
	struct ConstWatchList;
	State combine_const(State a, State b);
	State check_constbit(FfData &ff, int i);
	void commit_const(dict<Cell *, pool<int>> &const_bits, const ConstObligation &ob);
	bool add_const_target(ConstObligation &ob, SigBit sig);
	bool resolve_const_obligation(QuickConeSat &qcsat, int64_t cap, ConstObligation &ob,
			const ConstWatchList &watches);
	std::vector<ConstObligation> gather_const_obligations();
	int build_const_batch(QuickConeSat &qcsat, std::vector<ConstObligation> &obligations, int batch_begin);
	void sweep_const_batch(QuickConeSat &qcsat, std::vector<ConstObligation> &obligations,
			int batch_begin, int batch_end, int64_t screen_cap);
	void solve_const_obligations(std::vector<ConstObligation> &obligations);
	bool run_constbits();

	struct EqBit;
	struct SigKey;
	struct EqCandidates;
	EqCandidates gather_initial_eq_classes();
	void filter_classes_sim(EqCandidates &cand);
	void drop_all_classes(EqCandidates &cand);
	void filter_classes_sat(EqCandidates &cand);
	bool apply_eq_merges(const EqCandidates &cand);
	bool run_eqbits();
};

YOSYS_NAMESPACE_END

#endif /* OPT_DFF_H */
