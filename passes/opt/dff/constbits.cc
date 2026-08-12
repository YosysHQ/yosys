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

#include "passes/opt/dff/opt_dff.h"

USING_YOSYS_NAMESPACE

YOSYS_NAMESPACE_BEGIN

// lattice join of candidate constants: Sx is the identity (unless -keepdc
// pins it), equal values join, Sm marks a conflict
State OptDffWorker::combine_const(State a, State b) {
	if (a == State::Sx && !opt.keepdc) return b;
	if (b == State::Sx && !opt.keepdc) return a;
	if (a == b) return a;
	return State::Sm;
}

// candidate stuck-at value of ff bit i, joined over every non-D way the bit
// can acquire a value: init, arst, srst and sr (a clr/set that can ever
// fire forces 0/1)
// returns S0/S1 as the candidate, Sx if unconstrained, Sm on conflict
// the candidate doubles as the induction base case
State OptDffWorker::check_constbit(FfData &ff, int i)
{
	State val = ff.val_init[i];
	if (ff.has_arst) val = combine_const(val, ff.val_arst[i]);
	if (ff.has_srst) val = combine_const(val, ff.val_srst[i]);
	if (ff.has_sr) {
		if (!is_inactive(sigmap(ff.sig_clr[i]), ff.pol_clr))
			val = combine_const(val, State::S0);
		if (!is_inactive(sigmap(ff.sig_set[i]), ff.pol_set))
			val = combine_const(val, State::S1);
	}

	return val;
}

// one suspected-constant ff bit: q (output of cell at bit idx) looks stuck
// at val, and sat must show that every target feeds val back into the bit
struct OptDffWorker::ConstObligation {
	enum Status { Pending, Proven, Dropped };

	Cell *cell;
	int idx;
	State val;
	SigBit q;
	std::vector<SigBit> targets; // non-const inputs (D, AD), must be shown to be eq
	Status status = Pending;

	int q_lit = -1;              // valid within the current batch
	int differ_lit = -1;         // some target differs from the candidate value
};

// the solver model captures (differ, q) of every pending obligation so one
// counterexample can disprove many at once
struct OptDffWorker::ConstWatchList {
	// interleaved pairs, exprs[2k] = differ_lit and exprs[2k + 1] = q_lit of obs[k]
	std::vector<int> exprs;
	std::vector<ConstObligation *> obs;

	void watch(ConstObligation &ob) {
		exprs.push_back(ob.differ_lit);
		exprs.push_back(ob.q_lit);
		obs.push_back(&ob);
	}

	// drop every obligation whose q holds its constant while some target differs
	void drop_disproven(const std::vector<bool> &model) const {
		for (int k = 0; k < GetSize(obs); k++) {
			bool want = (obs[k]->val == State::S1);
			if (model[2*k + 1] == want && model[2*k])
				obs[k]->status = ConstObligation::Dropped;
		}
	}
};

void OptDffWorker::commit_const(dict<Cell *, pool<int>> &const_bits, const ConstObligation &ob)
{
	log("Setting constant %d-bit at position %d on %s (%s) from module %s.\n",
			ob.val == State::S1 ? 1 : 0, ob.idx, ob.cell, ob.cell->type.unescape(), module);
	initvals.remove_init(ob.q);
	module->connect(ob.q, ob.val);
	const_bits[ob.cell].insert(ob.idx);
}

bool OptDffWorker::add_const_target(ConstObligation &ob, SigBit sig)
{
	if (!opt.sat || (ob.val != State::S0 && ob.val != State::S1))
		return false;
	if (!get_modwalker().has_drivers(sig))
		return false;
	ob.targets.push_back(sig);
	return true;
}

// try to decide obligation ob under the given per-query effort cap
bool OptDffWorker::resolve_const_obligation(QuickConeSat &qcsat, int64_t cap, ConstObligation &ob,
		const ConstWatchList &watches)
{
	// induction step: assuming q already holds the candidate value, the values
	// fed through the targets must equal it again, since check_constbit provides the
	// base case, so unsat makes the constant an inductive invariant
	int vlit = qcsat.ez->value(ob.val == State::S1);
	std::vector<int> assumptions;
	assumptions.push_back(qcsat.ez->IFF(ob.q_lit, vlit));
	assumptions.push_back(ob.differ_lit);

	std::vector<bool> model;
	auto res = sat_budget.solve(qcsat, cap, watches.exprs, model, assumptions);

	if (res == SatEffortBudget::Result::LimitReached)
		return false;
	if (res == SatEffortBudget::Result::Unsat) {
		ob.status = ConstObligation::Proven;
		return true;
	}

	watches.drop_disproven(model);
	ob.status = ConstObligation::Dropped;
	return true;
}

// fold constant D/AD inputs into the candidate value; bits with remaining
// wire inputs get sat proof targets (only when -sat is in effect), bits
// with none are trivially proven
std::vector<OptDffWorker::ConstObligation> OptDffWorker::gather_const_obligations()
{
	std::vector<ConstObligation> obligations;

	for (auto cell : module->selected_cells()) {
		if (!cell->is_builtin_ff())
			continue;

		FfData ff(&initvals, cell);

		for (int i = 0; i < ff.width; i++) {
			State val = check_constbit(ff, i);
			if (val == State::Sm)
				continue;

			bool has_d = ff.has_clk || ff.has_gclk;
			SigBit d = has_d ? sigmap(ff.sig_d[i]) : SigBit();
			SigBit ad = ff.has_aload ? sigmap(ff.sig_ad[i]) : SigBit();

			// fold all const inputs first, so the sat targets are checked
			// against the final candidate
			if (has_d && !d.wire)
				val = combine_const(val, d.data);
			if (ff.has_aload && !ad.wire)
				val = combine_const(val, ad.data);
			if (val == State::Sm)
				continue;

			ConstObligation ob;
			ob.cell = cell;
			ob.idx = i;
			ob.val = val;
			ob.q = ff.sig_q[i];

			bool feasible = true;
			if (has_d && d.wire)
				feasible = add_const_target(ob, d);
			if (feasible && ff.has_aload && ad.wire)
				feasible = add_const_target(ob, ad);
			if (!feasible)
				continue;

			if (ob.targets.empty())
				ob.status = ConstObligation::Proven;
			obligations.push_back(std::move(ob));
		}
	}

	return obligations;
}

int OptDffWorker::build_const_batch(QuickConeSat &qcsat, std::vector<ConstObligation> &obligations, int batch_begin)
{
	int64_t cells_charged = 0;
	int batch_end = batch_begin;

	while (batch_end < GetSize(obligations) && !warn_if_budget_spent()) {
		auto &ob = obligations[batch_end];
		if (ob.status != ConstObligation::Pending) {
			batch_end++;
			continue;
		}
		if (batch_end > batch_begin && GetSize(qcsat.imported_cells) >= sat_batch_cells)
			break;
		ob.q_lit = qcsat.importSigBit(ob.q);
		int vlit = qcsat.ez->value(ob.val == State::S1);
		std::vector<int> differ;
		for (auto sig : ob.targets)
			differ.push_back(qcsat.ez->NOT(qcsat.ez->IFF(qcsat.importSigBit(sig), vlit)));
		ob.differ_lit = qcsat.ez->expression(ezSAT::OpOr, differ);
		qcsat.prepare();
		sat_budget.charge_import(qcsat, cells_charged);
		batch_end++;
	}

	return batch_end;
}

// sweep the batch under the cheap screening cap first, then re-sweep the
// still-undecided obligations with the full remaining budget
void OptDffWorker::sweep_const_batch(QuickConeSat &qcsat, std::vector<ConstObligation> &obligations,
		int batch_begin, int batch_end, int64_t screen_cap)
{
	for (int64_t cap : {screen_cap, (int64_t)0}) {
		bool all_resolved = true;

		// watch every pending obligation in the batch
		ConstWatchList watches;
		for (int obi = batch_begin; obi < batch_end; obi++) {
			auto &ob = obligations[obi];
			if (ob.status == ConstObligation::Pending)
				watches.watch(ob);
		}

		for (int obi = batch_begin; obi < batch_end; obi++) {
			auto &ob = obligations[obi];
			if (ob.status != ConstObligation::Pending)
				continue;
			if (warn_if_budget_spent())
				return;
			if (!resolve_const_obligation(qcsat, cap, ob, watches))
				all_resolved = false;
		}

		if (all_resolved)
			return;
	}
}

// sat: prove or drop the still-pending obligations in place
void OptDffWorker::solve_const_obligations(std::vector<ConstObligation> &obligations)
{
	int64_t num_queries = 0;
	for (auto &ob : obligations)
		num_queries += (ob.status == ConstObligation::Pending);
	if (num_queries == 0)
		return;

	ModWalker &modwalker = get_modwalker();

	// screening cap
	int64_t screen_cap = 0;
	if (sat_budget.enabled()) {
		// scale down when we can't afford a full screening round
		screen_cap = max((int64_t)20000, min((int64_t)200000, sat_budget.total / (4 * num_queries)));
	}

	// NOTE: each obligation is proven independently, so processing obligations in
	// batches and stopping early on an exhausted budget should be safe
	for (int batch_begin = 0; batch_begin < GetSize(obligations) && !warn_if_budget_spent(); ) {
		QuickConeSat qcsat(modwalker);
		int batch_end = build_const_batch(qcsat, obligations, batch_begin);
		sweep_const_batch(qcsat, obligations, batch_begin, batch_end, screen_cap);
		batch_begin = batch_end;
	}
}

bool OptDffWorker::run_constbits()
{
	std::vector<ConstObligation> obligations = gather_const_obligations();

	solve_const_obligations(obligations);

	dict<Cell *, pool<int>> const_bits;
	for (auto &ob : obligations)
		if (ob.status == ConstObligation::Proven)
			commit_const(const_bits, ob);

	for (auto &[cell, drop] : const_bits)
		remove_ff_bits(cell, drop);

	return !const_bits.empty();
}

YOSYS_NAMESPACE_END
