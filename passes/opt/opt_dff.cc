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
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/qcsat.h"
#include "kernel/modtools.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"
#include "passes/techmap/simplemap.h"
#include <stdio.h>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

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

	// Eattern matching for clock enable
	typedef std::map<RTLIL::SigBit, bool> pattern_t; // Control signal -> required vals
	typedef std::set<pattern_t> patterns_t;          // Alternative patterns (OR)
	typedef std::pair<RTLIL::SigBit, bool> ctrl_t;   // Control signal
	typedef std::set<ctrl_t> ctrls_t;                // Control signals (AND)

	std::vector<Cell *> dff_cells;

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

	SigSpec create_not(SigSpec a, bool is_fine) {
		if (is_fine)
			return module->NotGate(NEW_ID, a);
		else
			return module->Not(NEW_ID, a);
	}

	SigSpec create_and(SigSpec a, SigSpec b, bool is_fine) {
		if (is_fine)
			return module->AndGate(NEW_ID, a, b);
		else
			return module->And(NEW_ID, a, b);
	}

	void create_mux_to_output(SigSpec a, SigSpec b, SigSpec sel, SigSpec y, bool pol, bool is_fine) {
		if (is_fine) {
			if (pol)
				module->addMuxGate(NEW_ID, a, b, sel, y);
			else
				module->addMuxGate(NEW_ID, b, a, sel, y);
		} else {
			if (pol)
				module->addMux(NEW_ID, a, b, sel, y);
			else
				module->addMux(NEW_ID, b, a, sel, y);
		}
	}

	void maybe_simplemap(Cell *c, bool make_gates) {
		if (make_gates) {
			simplemap(module, c);
			module->remove(c);
		}
	}

	OptDffWorker(const OptDffOptions &opt, Module *mod)
		: opt(opt), module(mod), sigmap(mod), initvals(&sigmap, mod)
	{
		// Gathering two kinds of information here for every sigmapped SigBit:
		// - bitusers: how many users it has (muxes will only be merged into FFs if the FF is the only user)
		// - bit2mux: the mux cell and bit index that drives it, if any

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					bitusers[bit]++;

		for (auto cell : module->cells()) {
			if (cell->type.in(ID($mux), ID($pmux), ID($_MUX_))) {
				RTLIL::SigSpec sig_y = sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < GetSize(sig_y); i++)
					bit2mux[sig_y[i]] = cell_int_t(cell, i);
			}

			for (auto conn : cell->connections()) {
				bool is_output = cell->output(conn.first);
				if (!is_output || !cell->known())
					for (auto bit : sigmap(conn.second))
						bitusers[bit]++;
			}

			if (module->design->selected(module, cell) && cell->is_builtin_ff())
				dff_cells.push_back(cell);
		}
	}

	State combine_const(State a, State b) {
		// Combine constants: returns Sm if values conflict
		if (a == State::Sx && !opt.keepdc) return b;
		if (b == State::Sx && !opt.keepdc) return a;
		if (a == b) return a;
		return State::Sm;
	}

	patterns_t find_muxtree_feedback_patterns(RTLIL::SigBit d, RTLIL::SigBit q, pattern_t path)
	{
		// Find feedback paths D->Q through mux tree, replacing found paths with Sx
		patterns_t ret;

		if (d == q) {
			ret.insert(path);
			return ret; // Feedback found
		}

		if (bit2mux.count(d) == 0 || bitusers[d] > 1)
			return ret; // D not driven by MUX / MUX drives multiple loads

		cell_int_t mbit = bit2mux.at(d);
		RTLIL::SigSpec sig_a = sigmap(mbit.first->getPort(ID::A));
		RTLIL::SigSpec sig_b = sigmap(mbit.first->getPort(ID::B));
		RTLIL::SigSpec sig_s = sigmap(mbit.first->getPort(ID::S));
		int width = GetSize(sig_a), index = mbit.second;

		// Traverse MUX tree
		for (int i = 0; i < GetSize(sig_s); i++) {
			if (path.count(sig_s[i]) && path.at(sig_s[i])) {
				ret = find_muxtree_feedback_patterns(sig_b[i*width + index], q, path);
				if (sig_b[i*width + index] == q) {
					RTLIL::SigSpec s = mbit.first->getPort(ID::B);
					s[i*width + index] = RTLIL::Sx;
					mbit.first->setPort(ID::B, s);
				}

				return ret;
			}
		}

		// Specific path wasn't forced, explore the 0 branch
		pattern_t path_else = path;
		for (int i = 0; i < GetSize(sig_s); i++) {
			if (path.count(sig_s[i]))
				continue;

			pattern_t path_this = path;
			path_else[sig_s[i]] = false; // Assume S=0 for 'else' path
			path_this[sig_s[i]] = true;  // Assume S=1 for 'this' path

			// Selected when S=1
			for (auto &pat : find_muxtree_feedback_patterns(sig_b[i*width + index], q, path_this))
				ret.insert(pat);

			if (sig_b[i*width + index] == q) {
				RTLIL::SigSpec s = mbit.first->getPort(ID::B);
				s[i*width + index] = RTLIL::Sx;
				mbit.first->setPort(ID::B, s);
			}
		}

		// Selected when S=0
		for (auto &pat : find_muxtree_feedback_patterns(sig_a[index], q, path_else))
			ret.insert(pat);

		if (sig_a[index] == q) {
			RTLIL::SigSpec s = mbit.first->getPort(ID::A);
			s[index] = RTLIL::Sx;
			mbit.first->setPort(ID::A, s);
		}

		return ret;
	}

	void simplify_patterns(patterns_t& patterns)
	{
		auto new_patterns = patterns;

		auto find_comp = [](const auto& left, const auto& right) -> std::optional<RTLIL::SigBit> {
			std::optional<RTLIL::SigBit> ret;
			for (const auto &pt: left) {
				if (right.count(pt.first) == 0) return {};
				if (right.at(pt.first) == pt.second) continue;
				if (ret) return {};
				ret = pt.first;
			}
			return ret;
		};

		// Remove complimentary patterns
		bool optimized;
		do {
			optimized = false;
			for (auto i = patterns.begin(); i != patterns.end(); i++) {
				for (auto j = std::next(i, 1); j != patterns.end(); j++) {
					const auto& left = (GetSize(*j) <= GetSize(*i)) ? *j : *i;
					auto right = (GetSize(*i) < GetSize(*j)) ? *j : *i;
					const auto complimentary_var = find_comp(left, right);

					if (complimentary_var && new_patterns.count(right)) {
						new_patterns.erase(right);
						right.erase(complimentary_var.value());
						new_patterns.insert(right);
						optimized = true;
					}
				}
			}
			patterns = new_patterns;
		} while(optimized);

		// Remove redundant patterns
		for (auto i = patterns.begin(); i != patterns.end(); ++i) {
			for (auto j = std::next(i, 1); j != patterns.end(); ++j) {
				const auto& left = (GetSize(*j) <= GetSize(*i)) ? *j : *i;
				const auto& right = (GetSize(*i) < GetSize(*j)) ? *j : *i;
				bool redundant = true;

				for (const auto& pt : left)
					if (right.count(pt.first) == 0 || right.at(pt.first) != pt.second)
						redundant = false;
				if (redundant)
					new_patterns.erase(right);
			}
		}

		patterns = std::move(new_patterns);
	}

	ctrl_t make_patterns_logic(const patterns_t &patterns, const ctrls_t &ctrls, bool make_gates)
	{
		if (patterns.empty() && GetSize(ctrls) == 1)
			return *ctrls.begin();

		RTLIL::SigSpec or_input;

		// Build logic for each feedback pattern
		for (auto pat : patterns) {
			RTLIL::SigSpec s1, s2;

			for (auto it : pat) {
				s1.append(it.first);
				s2.append(it.second);
			}

			RTLIL::SigSpec y = module->addWire(NEW_ID);
			RTLIL::Cell *c = module->addNe(NEW_ID, s1, s2, y);
			maybe_simplemap(c, make_gates);
			or_input.append(y);
		}

		// Add existing control signals
		for (auto item : ctrls) {
			if (item.second)
				or_input.append(item.first);
			else
				or_input.append(create_not(item.first, make_gates));
		}

		if (GetSize(or_input) == 0) return ctrl_t(State::S1, true);
		if (GetSize(or_input) == 1) return ctrl_t(or_input, true);

		RTLIL::SigSpec y = module->addWire(NEW_ID);
		RTLIL::Cell *c = module->addReduceAnd(NEW_ID, or_input, y);
		maybe_simplemap(c, make_gates);
		return ctrl_t(y, true);
	}

	ctrl_t combine_resets(const ctrls_t &ctrls, bool make_gates)
	{
		if (GetSize(ctrls) == 1)
			return *ctrls.begin();

		bool final_pol = false;
		for (auto item : ctrls)
			if (item.second)
				final_pol = true;

		RTLIL::SigSpec or_input;
		for (auto item : ctrls) {
			if (item.second == final_pol)
				or_input.append(item.first);
			else
				or_input.append(create_not(item.first, make_gates));
		}

		RTLIL::SigSpec y = module->addWire(NEW_ID);
		RTLIL::Cell *c = final_pol
			? module->addReduceOr(NEW_ID, or_input, y)
			: module->addReduceAnd(NEW_ID, or_input, y);
		maybe_simplemap(c, make_gates);
		return ctrl_t(y, final_pol);
	}

	bool signal_all_same(const SigSpec &sig) {
		for (int i = 1; i < GetSize(sig); i++)
			if (sig[i] != sig[0])
				return false;
		return true;
	}

	bool optimize_sr(FfData &ff, Cell *cell, bool &changed)
	{
		// Removes SR if CLR/SET are always active
		// Converts SR to ARST if one pin is never active
		// Converts SR to ARST if SET/CLR are inverses of eachother
		bool sr_removed = false;
		std::vector<int> keep_bits;

		// Check for constant Set/Clear inputs
		for (int i = 0; i < ff.width; i++) {
			if (is_always_active(ff.sig_clr[i], ff.pol_clr)) {
				initvals.remove_init(ff.sig_q[i]);
				module->connect(ff.sig_q[i], State::S0);
				log("Handling always-active CLR at position %d on %s (%s) from module %s (changing to const driver).\n",
						i, log_id(cell), log_id(cell->type), log_id(module));
				sr_removed = true;
			} else if (is_always_active(ff.sig_set[i], ff.pol_set)) {
				initvals.remove_init(ff.sig_q[i]);
				if (!ff.pol_clr)
					module->connect(ff.sig_q[i], ff.sig_clr[i]);
				else if (ff.is_fine)
					module->addNotGate(NEW_ID, ff.sig_clr[i], ff.sig_q[i]);
				else
					module->addNot(NEW_ID, ff.sig_clr[i], ff.sig_q[i]);
				log("Handling always-active SET at position %d on %s (%s) from module %s (changing to combinatorial circuit).\n",
						i, log_id(cell), log_id(cell->type), log_id(module));
				sr_removed = true;
			} else {
				keep_bits.push_back(i);
			}
		}

		if (sr_removed) {
			if (keep_bits.empty()) {
				module->remove(cell);
				return true; // FF fully removed
			}
			ff = ff.slice(keep_bits);
			ff.cell = cell;
			changed = true;
		}

		// Try SR -> ARST conversion
		bool clr_inactive = ff.pol_clr ? ff.sig_clr.is_fully_zero() : ff.sig_clr.is_fully_ones();
		bool set_inactive = ff.pol_set ? ff.sig_set.is_fully_zero() : ff.sig_set.is_fully_ones();

		if (clr_inactive && signal_all_same(ff.sig_set)) {
			log("Removing never-active CLR on %s (%s) from module %s.\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_sr = false;
			ff.has_arst = true;
			ff.pol_arst = ff.pol_set;
			ff.sig_arst = ff.sig_set[0];
			ff.val_arst = Const(State::S1, ff.width);
			changed = true;
		} else if (set_inactive && signal_all_same(ff.sig_clr)) {
			log("Removing never-active SET on %s (%s) from module %s.\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_sr = false;
			ff.has_arst = true;
			ff.pol_arst = ff.pol_clr;
			ff.sig_arst = ff.sig_clr[0];
			ff.val_arst = Const(State::S0, ff.width);
			changed = true;
		} else if (ff.pol_clr == ff.pol_set) {
			State val_neutral = ff.pol_set ? State::S0 : State::S1;
			SigBit sig_arst = (ff.sig_clr[0] == val_neutral) ? ff.sig_set[0] : ff.sig_clr[0];

			bool failed = false;
			Const::Builder val_arst_builder(ff.width);
			for (int i = 0; i < ff.width; i++) {
				if (ff.sig_clr[i] == sig_arst && ff.sig_set[i] == val_neutral)
					val_arst_builder.push_back(State::S0);
				else if (ff.sig_set[i] == sig_arst && ff.sig_clr[i] == val_neutral)
					val_arst_builder.push_back(State::S1);
				else {
					failed = true;
					break;
				}
			}

			if (!failed) {
				log("Converting CLR/SET to ARST on %s (%s) from module %s.\n",
						log_id(cell), log_id(cell->type), log_id(module));
				ff.has_sr = false;
				ff.has_arst = true;
				ff.val_arst = val_arst_builder.build();
				ff.sig_arst = sig_arst;
				ff.pol_arst = ff.pol_clr;
				changed = true;
			}
		}

		return false;
	}

	bool optimize_aload(FfData &ff, Cell *cell, bool &changed)
	{
		// Removes unused Async Load
		// Converts constant Async Load to ARST
		if (is_always_inactive(ff.sig_aload, ff.pol_aload)) {
			log("Removing never-active async load on %s (%s) from module %s.\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_aload = false;
			changed = true;
			return false;
		}

		if (is_active(ff.sig_aload, ff.pol_aload)) {
			// ALOAD always active
			log("Handling always-active async load on %s (%s) from module %s (changing to combinatorial circuit).\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.remove();

			if (ff.has_sr) {
				SigSpec tmp;
				if (ff.is_fine) {
					tmp = ff.pol_set
						? module->MuxGate(NEW_ID, ff.sig_ad, State::S1, ff.sig_set)
						: module->MuxGate(NEW_ID, State::S1, ff.sig_ad, ff.sig_set);

					if (ff.pol_clr)
						module->addMuxGate(NEW_ID, tmp, State::S0, ff.sig_clr, ff.sig_q);
					else
						module->addMuxGate(NEW_ID, State::S0, tmp, ff.sig_clr, ff.sig_q);
				} else {
					tmp = ff.pol_set
						? module->Or(NEW_ID, ff.sig_ad, ff.sig_set)
						: module->Or(NEW_ID, ff.sig_ad, module->Not(NEW_ID, ff.sig_set));

					if (ff.pol_clr)
						module->addAnd(NEW_ID, tmp, module->Not(NEW_ID, ff.sig_clr), ff.sig_q);
					else
						module->addAnd(NEW_ID, tmp, ff.sig_clr, ff.sig_q);
				}
			} else if (ff.has_arst) {
				create_mux_to_output(ff.sig_ad, ff.val_arst, ff.sig_arst, ff.sig_q, ff.pol_arst, ff.is_fine);
			} else {
				module->connect(ff.sig_q, ff.sig_ad);
			}
			return true;
		}

		// AD is constant -> ARST
		if (ff.sig_ad.is_fully_const() && !ff.has_arst && !ff.has_sr) {
			log("Changing const-value async load to async reset on %s (%s) from module %s.\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_arst = true;
			ff.has_aload = false;
			ff.sig_arst = ff.sig_aload;
			ff.pol_arst = ff.pol_aload;
			ff.val_arst = ff.sig_ad.as_const();
			changed = true;
		}

		return false;
	}

	bool optimize_arst(FfData &ff, Cell *cell, bool &changed)
	{
		// Removes ARST if never active or replaces FF if always active
		if (is_inactive(ff.sig_arst, ff.pol_arst)) {
			log("Removing never-active ARST on %s (%s) from module %s.\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_arst = false;
			changed = true;
		} else if (is_always_active(ff.sig_arst, ff.pol_arst)) {
			log("Handling always-active ARST on %s (%s) from module %s (changing to const driver).\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.remove();
			module->connect(ff.sig_q, ff.val_arst);
			return true;
		}

		return false;
	}

	void optimize_srst(FfData &ff, Cell *cell, bool &changed)
	{
		// Removes SRST if never active or forces D to reset value if always active
		if (is_inactive(ff.sig_srst, ff.pol_srst)) {
			log("Removing never-active SRST on %s (%s) from module %s.\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_srst = false;
			changed = true;
		} else if (is_always_active(ff.sig_srst, ff.pol_srst)) {
			log("Handling always-active SRST on %s (%s) from module %s (changing to const D).\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_srst = false;
			if (!ff.ce_over_srst)
				ff.has_ce = false;

			ff.sig_d = ff.val_srst;
			changed = true;
		}
	}

	void optimize_ce(FfData &ff, Cell *cell, bool &changed)
	{
		if (is_always_inactive(ff.sig_ce, ff.pol_ce)) {
			if (ff.has_srst && !ff.ce_over_srst) {
				log("Handling never-active EN on %s (%s) from module %s (connecting SRST instead).\n",
						log_id(cell), log_id(cell->type), log_id(module));
				ff.pol_ce = ff.pol_srst;
				ff.sig_ce = ff.sig_srst;
				ff.has_srst = false;
				ff.sig_d = ff.val_srst;
				changed = true;
			} else if (!opt.keepdc || ff.val_init.is_fully_def()) {
				log("Handling never-active EN on %s (%s) from module %s (removing D path).\n",
						log_id(cell), log_id(cell->type), log_id(module));
				ff.has_ce = ff.has_clk = ff.has_srst = false;
				changed = true;
			} else {
				ff.sig_d = ff.sig_q;
				ff.has_ce = ff.has_srst = false;
				changed = true;
			}
		} else if (is_active(ff.sig_ce, ff.pol_ce)) {
			log("Removing always-active EN on %s (%s) from module %s.\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_ce = false;
			changed = true;
		}
	}

	void optimize_const_clk(FfData &ff, Cell *cell, bool &changed)
	{
		if (!opt.keepdc || ff.val_init.is_fully_def()) {
			log("Handling const CLK on %s (%s) from module %s (removing D path).\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_ce = ff.has_clk = ff.has_srst = false;
			changed = true;
		} else if (ff.has_ce || ff.has_srst || ff.sig_d != ff.sig_q) {
			ff.sig_d = ff.sig_q;
			ff.has_ce = ff.has_srst = false;
			changed = true;
		}
	}

	void optimize_d_equals_q(FfData &ff, Cell *cell, bool &changed)
	{
		// Detect feedback loops where D is hardwired to Q
		if (ff.has_clk && ff.has_srst) {
			log("Handling D = Q on %s (%s) from module %s (conecting SRST instead).\n",
					log_id(cell), log_id(cell->type), log_id(module));
			if (ff.has_ce && ff.ce_over_srst) {
				SigSpec ce = ff.pol_ce ? ff.sig_ce : create_not(ff.sig_ce, ff.is_fine);
				SigSpec srst = ff.pol_srst ? ff.sig_srst : create_not(ff.sig_srst, ff.is_fine);
				ff.sig_ce = create_and(ce, srst, ff.is_fine);
				ff.pol_ce = true;
			} else {
				ff.pol_ce = ff.pol_srst;
				ff.sig_ce = ff.sig_srst;
			}

			ff.has_ce = true;
			ff.has_srst = false;
			ff.sig_d = ff.val_srst;
			changed = true;
		} else if (!opt.keepdc || ff.val_init.is_fully_def()) {
			log("Handling D = Q on %s (%s) from module %s (removing D path).\n",
					log_id(cell), log_id(cell->type), log_id(module));
			ff.has_gclk = ff.has_clk = ff.has_ce = false;
			changed = true;
		}
	}

	bool try_merge_srst(FfData &ff, Cell *cell, bool &changed)
	{
		std::map<ctrls_t, std::vector<int>> groups;
		std::vector<int> remaining_indices;
		Const::Builder val_srst_builder(ff.width);

		for (int i = 0; i < ff.width; i++) {
			ctrls_t resets;
			State reset_val = ff.has_srst ? ff.val_srst[i] : State::Sx;

			while (bit2mux.count(ff.sig_d[i]) && bitusers[ff.sig_d[i]] == 1) {
				cell_int_t mbit = bit2mux.at(ff.sig_d[i]);
				if (GetSize(mbit.first->getPort(ID::S)) != 1)
					break;

				SigBit s = mbit.first->getPort(ID::S);
				SigBit a = mbit.first->getPort(ID::A)[mbit.second];
				SigBit b = mbit.first->getPort(ID::B)[mbit.second];

				if ((a == State::S0 || a == State::S1) && (b == State::S0 || b == State::S1))
					break;

				bool b_const = (b == State::S0 || b == State::S1);
				bool a_const = (a == State::S0 || a == State::S1);

				if (b_const && (b == reset_val || reset_val == State::Sx) && a != ff.sig_q[i]) {
					reset_val = b.data;
					resets.insert(ctrl_t(s, true));
					ff.sig_d[i] = a;
				} else if (a_const && (a == reset_val || reset_val == State::Sx) && b != ff.sig_q[i]) {
					reset_val = a.data;
					resets.insert(ctrl_t(s, false));
					ff.sig_d[i] = b;
				} else {
					break;
				}
			}

			if (!resets.empty()) {
				if (ff.has_srst)
					resets.insert(ctrl_t(ff.sig_srst, ff.pol_srst));

				groups[resets].push_back(i);
			} else {
				remaining_indices.push_back(i);
			}

			val_srst_builder.push_back(reset_val);
		}

		Const val_srst = val_srst_builder.build();

		for (auto &it : groups) {
			FfData new_ff = ff.slice(it.second);
			Const::Builder new_val_srst_builder(new_ff.width);
			for (int i = 0; i < new_ff.width; i++)
				new_val_srst_builder.push_back(val_srst[it.second[i]]);

			new_ff.val_srst = new_val_srst_builder.build();

			ctrl_t srst = combine_resets(it.first, ff.is_fine);
			new_ff.has_srst = true;
			new_ff.sig_srst = srst.first;
			new_ff.pol_srst = srst.second;
			if (new_ff.has_ce)
				new_ff.ce_over_srst = true;

			Cell *new_cell = new_ff.emit();
			if (new_cell)
				dff_cells.push_back(new_cell);

			log("Adding SRST signal on %s (%s) from module %s (D = %s, Q = %s, rval = %s).\n",
					log_id(cell), log_id(cell->type), log_id(module),
					log_signal(new_ff.sig_d), log_signal(new_ff.sig_q), log_signal(new_ff.val_srst));
		}

		if (remaining_indices.empty()) {
			module->remove(cell);
			return true;
		}

		if (GetSize(remaining_indices) != ff.width) {
			ff = ff.slice(remaining_indices);
			ff.cell = cell;
			changed = true;
		}

		return false;
	}

	bool try_merge_ce(FfData &ff, Cell *cell, bool &changed)
	{
		std::map<std::pair<patterns_t, ctrls_t>, std::vector<int>> groups;
		std::vector<int> remaining_indices;

		for (int i = 0; i < ff.width; i++) {
			ctrls_t enables;

			while (bit2mux.count(ff.sig_d[i]) && bitusers[ff.sig_d[i]] == 1) {
				cell_int_t mbit = bit2mux.at(ff.sig_d[i]);
				if (GetSize(mbit.first->getPort(ID::S)) != 1)
					break;

				SigBit s = mbit.first->getPort(ID::S);
				SigBit a = mbit.first->getPort(ID::A)[mbit.second];
				SigBit b = mbit.first->getPort(ID::B)[mbit.second];

				if (a == ff.sig_q[i]) {
					enables.insert(ctrl_t(s, true));
					ff.sig_d[i] = b;
				} else if (b == ff.sig_q[i]) {
					enables.insert(ctrl_t(s, false));
					ff.sig_d[i] = a;
				} else {
					break;
				}
			}

			patterns_t patterns;
			if (!opt.simple_dffe)
				patterns = find_muxtree_feedback_patterns(ff.sig_d[i], ff.sig_q[i], pattern_t());

			if (!patterns.empty() || !enables.empty()) {
				if (ff.has_ce)
					enables.insert(ctrl_t(ff.sig_ce, ff.pol_ce));
				simplify_patterns(patterns);
				groups[std::make_pair(patterns, enables)].push_back(i);
			} else {
				remaining_indices.push_back(i);
			}
		}

		for (auto &it : groups) {
			FfData new_ff = ff.slice(it.second);
			ctrl_t en = make_patterns_logic(it.first.first, it.first.second, ff.is_fine);

			new_ff.has_ce = true;
			new_ff.sig_ce = en.first;
			new_ff.pol_ce = en.second;
			new_ff.ce_over_srst = false;

			Cell *new_cell = new_ff.emit();
			if (new_cell)
				dff_cells.push_back(new_cell);

			log("Adding EN signal on %s (%s) from module %s (D = %s, Q = %s).\n",
					log_id(cell), log_id(cell->type), log_id(module),
					log_signal(new_ff.sig_d), log_signal(new_ff.sig_q));
		}

		if (remaining_indices.empty()) {
			module->remove(cell);
			return true;
		}

		if (GetSize(remaining_indices) != ff.width) {
			ff = ff.slice(remaining_indices);
			ff.cell = cell;
			changed = true;
		}

		return false;
	}

	bool run()
	{
		bool did_something = false;

		while (!dff_cells.empty()) {
			Cell *cell = dff_cells.back();
			dff_cells.pop_back();

			FfData ff(&initvals, cell);
			bool changed = false;

			if (!ff.width) {
				ff.remove();
				did_something = true;
				continue;
			}

			// Async control signal opt
			if (ff.has_sr && optimize_sr(ff, cell, changed)) {
				did_something = true;
				continue;
			}

			if (ff.has_aload && optimize_aload(ff, cell, changed)) {
				did_something = true;
				continue;
			}

			if (ff.has_arst && optimize_arst(ff, cell, changed)) {
				did_something = true;
				continue;
			}

			// Sync control signal opt
			if (ff.has_srst)
				optimize_srst(ff, cell, changed);

			if (ff.has_ce)
				optimize_ce(ff, cell, changed);

			if (ff.has_clk && ff.sig_clk.is_fully_const())
				optimize_const_clk(ff, cell, changed);

			// Feedback (D=Q) opt
			if ((ff.has_clk || ff.has_gclk) && ff.sig_d == ff.sig_q)
				optimize_d_equals_q(ff, cell, changed);

			if (ff.has_aload && !ff.has_clk && ff.sig_ad == ff.sig_q) {
				log("Handling AD = Q on %s (%s) from module %s (removing async load path).\n",
						log_id(cell), log_id(cell->type), log_id(module));
				ff.has_aload = false;
				changed = true;
			}

			// Mux merging
			if (ff.has_clk && ff.sig_d != ff.sig_q) {
				bool can_merge_srst = !ff.has_arst && !ff.has_sr &&
					(!ff.has_srst || !ff.has_ce || ff.ce_over_srst) && !opt.nosdff;

				if (can_merge_srst && try_merge_srst(ff, cell, changed)) {
					did_something = true;
					continue;
				}

				bool can_merge_ce = (!ff.has_srst || !ff.has_ce || !ff.ce_over_srst) && !opt.nodffe;

				if (can_merge_ce && try_merge_ce(ff, cell, changed)) {
					did_something = true;
					continue;
				}
			}

			if (changed) {
				ff.emit();
				did_something = true;
			}
		}

		return did_something;
	}

	bool prove_const_with_sat(QuickConeSat &qcsat, ModWalker &modwalker, SigBit q, SigBit d, State val)
	{
		// Trivial non-const cases
		if (!modwalker.has_drivers(d))
			return false;
		if (val != State::S0 && val != State::S1)
			return false;

		int init_sat_pi = qcsat.importSigBit(val);
		int q_sat_pi = qcsat.importSigBit(q);
		int d_sat_pi = qcsat.importSigBit(d);
		qcsat.prepare();

		// If no counterexample exists, FF is constant
		return !qcsat.ez->solve(
			qcsat.ez->IFF(q_sat_pi, init_sat_pi),
			qcsat.ez->NOT(qcsat.ez->IFF(d_sat_pi, init_sat_pi)));
	}

	State check_constbit(FfData &ff, int i)
	{
		State val = ff.val_init[i];
		if (ff.has_arst) val = combine_const(val, ff.val_arst[i]);
		if (ff.has_srst) val = combine_const(val, ff.val_srst[i]);
		if (ff.has_sr) {
			if (ff.sig_clr[i] != (ff.pol_clr ? State::S0 : State::S1))
				val = combine_const(val, State::S0);
			if (ff.sig_set[i] != (ff.pol_set ? State::S0 : State::S1))
				val = combine_const(val, State::S1);
		}

		return val;
	}

	bool run_constbits()
	{
		// Find FFs that are provably constant
		ModWalker modwalker(module->design, module);
		QuickConeSat qcsat(modwalker);

		std::vector<RTLIL::Cell*> cells_to_remove;
		std::vector<FfData> ffs_to_emit;
		bool did_something = false;

		for (auto cell : module->selected_cells()) {
			if (!cell->is_builtin_ff())
				continue;

			FfData ff(&initvals, cell);
			pool<int> removed_sigbits;

			for (int i = 0; i < ff.width; i++) {
				State val = check_constbit(ff, i);
				if (val == State::Sm)
					continue;

				// Check Synchronous input D
				if (ff.has_clk || ff.has_gclk) {
					if (!ff.sig_d[i].wire) {
						// D is already a constant
						val = combine_const(val, ff.sig_d[i].data);
						if (val == State::Sm) continue;
					} else if (opt.sat) {
						// Try SAT proof for non-constant D wires
						if (!prove_const_with_sat(qcsat, modwalker, ff.sig_q[i], ff.sig_d[i], val))
							continue;
					} else {
						continue;
					}
				}

				// Check Async Load input AD
				if (ff.has_aload) {
					if (!ff.sig_ad[i].wire) {
						val = combine_const(val, ff.sig_ad[i].data);
						if (val == State::Sm) continue;
					} else if (opt.sat) {
						if (!prove_const_with_sat(qcsat, modwalker, ff.sig_q[i], ff.sig_ad[i], val))
							continue;
					} else {
						continue;
					}
				}

				log("Setting constant %d-bit at position %d on %s (%s) from module %s.\n",
						val ? 1 : 0, i, log_id(cell), log_id(cell->type), log_id(module));

				// Replace the Q output with the constant value
				initvals.remove_init(ff.sig_q[i]);
				module->connect(ff.sig_q[i], val);
				removed_sigbits.insert(i);
			}

			// Reconstruct FF with constant bits removed
			if (!removed_sigbits.empty()) {
				std::vector<int> keep_bits;
				for (int i = 0; i < ff.width; i++)
					if (!removed_sigbits.count(i))
						keep_bits.push_back(i);

				if (keep_bits.empty()) {
					cells_to_remove.push_back(cell);
				} else {
					ff = ff.slice(keep_bits);
					ff.cell = cell;
					ffs_to_emit.push_back(ff);
				}
				did_something = true;
			}
		}

		for (auto* cell : cells_to_remove)
			module->remove(cell);

		for (auto& ff : ffs_to_emit)
			ff.emit();

		return did_something;
	}
};

struct OptDffPass : public Pass {
	OptDffPass() : Pass("opt_dff", "perform DFF optimizations") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_dff [-nodffe] [-nosdff] [-keepdc] [-sat] [selection]\n");
		log("\n");
		log("This pass converts flip-flops to a more suitable type by merging clock enables\n");
		log("and synchronous reset multiplexers, removing unused control inputs, or\n");
		log("potentially removes the flip-flop altogether, converting it to a constant\n");
		log("driver.\n");
		log("\n");
		log("    -nodffe\n");
		log("        disables dff -> dffe conversion, and other transforms recognizing clock\n");
		log("        enable\n");
		log("\n");
		log("    -nosdff\n");
		log("        disables dff -> sdff conversion, and other transforms recognizing sync\n");
		log("        resets\n");
		log("\n");
		log("    -simple-dffe\n");
		log("        only enables clock enable recognition transform for obvious cases\n");
		log("\n");
		log("    -sat\n");
		log("        additionally invoke SAT solver to detect and remove flip-flops (with\n");
		log("        non-constant inputs) that can also be replaced with a constant driver\n");
		log("\n");
		log("    -keepdc\n");
		log("        some optimizations change the behavior of the circuit with respect to\n");
		log("        don't-care bits. for example in 'a+0' a single x-bit in 'a' will cause\n");
		log("        all result bits to be set to x. this behavior changes when 'a+0' is\n");
		log("        replaced by 'a'. the -keepdc option disables all such optimizations.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_DFF pass (perform DFF optimizations).\n");

		OptDffOptions opt;
		opt.nodffe = false;
		opt.nosdff = false;
		opt.simple_dffe = false;
		opt.keepdc = false;
		opt.sat = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-nodffe") { opt.nodffe = true; continue; }
			if (args[argidx] == "-nosdff") { opt.nosdff = true; continue; }
			if (args[argidx] == "-simple-dffe") { opt.simple_dffe = true; continue; }
			if (args[argidx] == "-keepdc") { opt.keepdc = true; continue; }
			if (args[argidx] == "-sat") { opt.sat = true; continue; }
			break;
		}
		extra_args(args, argidx, design);

		bool did_something = false;
		for (auto mod : design->selected_modules()) {
			OptDffWorker worker(opt, mod);
			if (worker.run())
				did_something = true;
			if (worker.run_constbits())
				did_something = true;
		}

		if (did_something)
			design->scratchpad_set_bool("opt.did_something", true);
	}
} OptDffPass;

PRIVATE_NAMESPACE_END
