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

#include "kernel/ff.h"
#include "kernel/pattern.h"
#include "passes/opt/dff/opt_dff.h"
#include "passes/techmap/simplemap.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SimpleContext
{
	OptDffWorker &worker;

	// Cell to port bit index
	typedef std::pair<RTLIL::Cell*, int> cell_int_t;

	dict<SigBit, int> bitusers;       // Signal sink count
	dict<SigBit, cell_int_t> bit2mux; // Signal bit to driving MUX

	std::vector<Cell *> dff_cells;

	SimpleContext(OptDffWorker &worker) : worker(worker)
	{
		// Gathering two kinds of information here for every sigmapped SigBit:
		// - bitusers: how many users it has (muxes will only be merged into FFs if the FF is the only user)
		// - bit2mux: the mux cell and bit index that drives it, if any

		for (auto wire : worker.module->wires())
			if (wire->port_output)
				for (auto bit : worker.sigmap(wire))
					bitusers[bit]++;

		for (auto cell : worker.module->cells()) {
			if (cell->type.in(ID($mux), ID($pmux), ID($_MUX_))) {
				RTLIL::SigSpec sig_y = worker.sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < GetSize(sig_y); i++)
					bit2mux[sig_y[i]] = cell_int_t(cell, i);
			}

			for (auto conn : cell->connections()) {
				bool is_output = cell->output(conn.first);
				if (!is_output || !cell->known())
					for (auto bit : worker.sigmap(conn.second))
						bitusers[bit]++;
			}

			if (worker.module->design->selected(worker.module, cell) && cell->is_builtin_ff())
				dff_cells.push_back(cell);
		}
	}

	SigSpec create_not(SigSpec a, bool is_fine, Cell *cell) {
		if (is_fine)
			return worker.module->NotGate(NEW_ID2_SUFFIX("not"), a, cell->get_src_attribute());
		else
			return worker.module->Not(NEW_ID2_SUFFIX("not"), a, false, cell->get_src_attribute());
	}

	SigSpec create_and(SigSpec a, SigSpec b, bool is_fine, Cell *cell) {
		if (is_fine)
			return worker.module->AndGate(NEW_ID2_SUFFIX("and"), a, b, cell->get_src_attribute());
		else
			return worker.module->And(NEW_ID2_SUFFIX("and"), a, b, false, cell->get_src_attribute());
	}

	void create_mux_to_output(SigSpec a, SigSpec b, SigSpec sel, SigSpec y, bool pol, bool is_fine, Cell *cell) {
		if (is_fine) {
			if (pol)
				worker.module->addMuxGate(NEW_ID2_SUFFIX("mux"), a, b, sel, y, cell->get_src_attribute());
			else
				worker.module->addMuxGate(NEW_ID2_SUFFIX("mux"), b, a, sel, y, cell->get_src_attribute());
		} else {
			if (pol)
				worker.module->addMux(NEW_ID2_SUFFIX("mux"), a, b, sel, y, cell->get_src_attribute());
			else
				worker.module->addMux(NEW_ID2_SUFFIX("mux"), b, a, sel, y, cell->get_src_attribute());
		}
	}

	void maybe_simplemap(Cell *c, bool make_gates) {
		if (make_gates) {
			simplemap(worker.module, c);
			worker.module->remove(c);
		}
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
		RTLIL::SigSpec sig_a = worker.sigmap(mbit.first->getPort(ID::A));
		RTLIL::SigSpec sig_b = worker.sigmap(mbit.first->getPort(ID::B));
		RTLIL::SigSpec sig_s = worker.sigmap(mbit.first->getPort(ID::S));
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

	ctrl_t make_patterns_logic(const patterns_t &patterns, const ctrls_t &ctrls, bool make_gates, Cell *cell)
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

			RTLIL::SigSpec y = worker.module->addWire(NEW_ID2_SUFFIX("pat_y")); // SILIMATE: Improve the naming
			RTLIL::Cell *c = worker.module->addNe(NEW_ID2_SUFFIX("pat_ne"), s1, s2, y, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
			maybe_simplemap(c, make_gates);
			or_input.append(y);
		}

		// Add existing control signals
		for (auto item : ctrls) {
			if (item.second)
				or_input.append(item.first);
			else
				or_input.append(create_not(item.first, make_gates, cell));
		}

		if (GetSize(or_input) == 0) return ctrl_t(State::S1, true);
		if (GetSize(or_input) == 1) return ctrl_t(or_input, true);

		RTLIL::SigSpec y = worker.module->addWire(NEW_ID2_SUFFIX("pat_logic_y")); // SILIMATE: Improve the naming
		RTLIL::Cell *c = worker.module->addReduceAnd(NEW_ID2_SUFFIX("pat_logic_reduce_and"), or_input, y, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
		maybe_simplemap(c, make_gates);
		return ctrl_t(y, true);
	}

	ctrl_t combine_resets(const ctrls_t &ctrls, bool make_gates, Cell *cell)
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
				or_input.append(create_not(item.first, make_gates, cell));
		}

		RTLIL::SigSpec y = worker.module->addWire(NEW_ID2_SUFFIX("comb_rst_y")); // SILIMATE: Improve the naming
		RTLIL::Cell *c = final_pol
			? worker.module->addReduceOr(NEW_ID2_SUFFIX("comb_rst_reduce_or"), or_input, y, false, cell->get_src_attribute()) // SILIMATE: Improve the naming
			: worker.module->addReduceAnd(NEW_ID2_SUFFIX("comb_rst_reduce_and"), or_input, y, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
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
			if (worker.is_always_active(ff.sig_clr[i], ff.pol_clr)) {
				worker.initvals.remove_init(ff.sig_q[i]);
				worker.module->connect(ff.sig_q[i], State::S0);
				log("Handling always-active CLR at position %d on %s (%s) from module %s (changing to const driver).\n",
						i, cell, cell->type.unescape(), worker.module);
				sr_removed = true;
			} else if (worker.is_always_active(ff.sig_set[i], ff.pol_set)) {
				worker.initvals.remove_init(ff.sig_q[i]);
				if (!ff.pol_clr)
					worker.module->connect(ff.sig_q[i], ff.sig_clr[i]);
				else if (ff.is_fine)
					worker.module->addNotGate(NEW_ID2_SUFFIX("not"), ff.sig_clr[i], ff.sig_q[i], cell->get_src_attribute());
				else
					worker.module->addNot(NEW_ID2_SUFFIX("not"), ff.sig_clr[i], ff.sig_q[i], false, cell->get_src_attribute());
				log("Handling always-active SET at position %d on %s (%s) from module %s (changing to combinatorial circuit).\n",
						i, cell, cell->type.unescape(), worker.module);
				sr_removed = true;
			} else {
				keep_bits.push_back(i);
			}
		}

		if (sr_removed) {
			if (keep_bits.empty()) {
				worker.module->remove(cell);
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
					cell, cell->type.unescape(), worker.module);
			ff.has_sr = false;
			ff.has_arst = true;
			ff.pol_arst = ff.pol_set;
			ff.sig_arst = ff.sig_set[0];
			ff.val_arst = Const(State::S1, ff.width);
			changed = true;
		} else if (set_inactive && signal_all_same(ff.sig_clr)) {
			log("Removing never-active SET on %s (%s) from module %s.\n",
					cell, cell->type.unescape(), worker.module);
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
						cell, cell->type.unescape(), worker.module);
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
		if (worker.is_always_inactive(ff.sig_aload, ff.pol_aload)) {
			log("Removing never-active async load on %s (%s) from module %s.\n",
					cell, cell->type.unescape(), worker.module);
			ff.has_aload = false;
			changed = true;
			return false;
		}

		if (worker.is_active(ff.sig_aload, ff.pol_aload)) {
			// ALOAD always active
			log("Handling always-active async load on %s (%s) from module %s (changing to combinatorial circuit).\n",
					cell, cell->type.unescape(), worker.module);

			if (ff.has_sr) {
				SigSpec tmp;
				if (ff.is_fine) {
					tmp = ff.pol_set
						? worker.module->MuxGate(NEW_ID2_SUFFIX("mux"), ff.sig_ad, State::S1, ff.sig_set, cell->get_src_attribute())
						: worker.module->MuxGate(NEW_ID2_SUFFIX("mux"), State::S1, ff.sig_ad, ff.sig_set, cell->get_src_attribute());

					if (ff.pol_clr)
						worker.module->addMuxGate(NEW_ID2_SUFFIX("mux"), tmp, State::S0, ff.sig_clr, ff.sig_q, cell->get_src_attribute());
					else
						worker.module->addMuxGate(NEW_ID2_SUFFIX("mux"), State::S0, tmp, ff.sig_clr, ff.sig_q, cell->get_src_attribute());
				} else {
					tmp = ff.pol_set
						? worker.module->Or(NEW_ID2_SUFFIX("or"), ff.sig_ad, ff.sig_set, false, cell->get_src_attribute())
						: worker.module->Or(NEW_ID2_SUFFIX("or"), ff.sig_ad, worker.module->Not(NEW_ID2_SUFFIX("not"), ff.sig_set, false, cell->get_src_attribute()), false, cell->get_src_attribute());

					if (ff.pol_clr)
						worker.module->addAnd(NEW_ID2_SUFFIX("and"), tmp, worker.module->Not(NEW_ID2_SUFFIX("not"), ff.sig_clr, false, cell->get_src_attribute()), ff.sig_q, false, cell->get_src_attribute());
					else
						worker.module->addAnd(NEW_ID2_SUFFIX("and"), tmp, ff.sig_clr, ff.sig_q, false, cell->get_src_attribute());
				}
			} else if (ff.has_arst) {
				create_mux_to_output(ff.sig_ad, ff.val_arst, ff.sig_arst, ff.sig_q, ff.pol_arst, ff.is_fine, cell);
			} else {
				worker.module->connect(ff.sig_q, ff.sig_ad);
			}
			ff.remove();
			return true;
		}

		// AD is constant -> ARST
		if (ff.sig_ad.is_fully_const() && !ff.has_arst && !ff.has_sr) {
			log("Changing const-value async load to async reset on %s (%s) from module %s.\n",
					cell, cell->type.unescape(), worker.module);
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
		if (worker.is_inactive(ff.sig_arst, ff.pol_arst)) {
			log("Removing never-active ARST on %s (%s) from module %s.\n",
					cell, cell->type.unescape(), worker.module);
			ff.has_arst = false;
			changed = true;
		} else if (worker.is_always_active(ff.sig_arst, ff.pol_arst)) {
			log("Handling always-active ARST on %s (%s) from module %s (changing to const driver).\n",
					cell, cell->type.unescape(), worker.module);
			ff.remove();
			worker.module->connect(ff.sig_q, ff.val_arst);
			return true;
		}

		return false;
	}

	void optimize_srst(FfData &ff, Cell *cell, bool &changed)
	{
		// Removes SRST if never active or forces D to reset value if always active
		if (worker.is_inactive(ff.sig_srst, ff.pol_srst)) {
			log("Removing never-active SRST on %s (%s) from module %s.\n",
					cell, cell->type.unescape(), worker.module);
			ff.has_srst = false;
			changed = true;
		} else if (worker.is_always_active(ff.sig_srst, ff.pol_srst)) {
			log("Handling always-active SRST on %s (%s) from module %s (changing to const D).\n",
					cell, cell->type.unescape(), worker.module);
			ff.has_srst = false;
			if (!ff.ce_over_srst)
				ff.has_ce = false;

			ff.sig_d = ff.val_srst;
			changed = true;
		}
	}

	void optimize_ce(FfData &ff, Cell *cell, bool &changed)
	{
		if (worker.is_always_inactive(ff.sig_ce, ff.pol_ce)) {
			if (ff.has_srst && !ff.ce_over_srst) {
				log("Handling never-active EN on %s (%s) from module %s (connecting SRST instead).\n",
						cell, cell->type.unescape(), worker.module);
				ff.pol_ce = ff.pol_srst;
				ff.sig_ce = ff.sig_srst;
				ff.has_srst = false;
				ff.sig_d = ff.val_srst;
				changed = true;
			} else if (!worker.opt.keepdc || ff.val_init.is_fully_def()) {
				log("Handling never-active EN on %s (%s) from module %s (removing D path).\n",
						cell, cell->type.unescape(), worker.module);
				ff.has_ce = ff.has_clk = ff.has_srst = false;
				changed = true;
			} else {
				ff.sig_d = ff.sig_q;
				ff.has_ce = ff.has_srst = false;
				changed = true;
			}
		} else if (worker.is_active(ff.sig_ce, ff.pol_ce)) {
			log("Removing always-active EN on %s (%s) from module %s.\n",
					cell, cell->type.unescape(), worker.module);
			ff.has_ce = false;
			changed = true;
		}
	}

	void optimize_const_clk(FfData &ff, Cell *cell, bool &changed)
	{
		if (!worker.opt.keepdc || ff.val_init.is_fully_def()) {
			log("Handling const CLK on %s (%s) from module %s (removing D path).\n",
					cell, cell->type.unescape(), worker.module);
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
					cell, cell->type.unescape(), worker.module);
			if (ff.has_ce && ff.ce_over_srst) {
				SigSpec ce = ff.pol_ce ? ff.sig_ce : create_not(ff.sig_ce, ff.is_fine, cell);
				SigSpec srst = ff.pol_srst ? ff.sig_srst : create_not(ff.sig_srst, ff.is_fine, cell);
				ff.sig_ce = create_and(ce, srst, ff.is_fine, cell);
				ff.pol_ce = true;
			} else {
				ff.pol_ce = ff.pol_srst;
				ff.sig_ce = ff.sig_srst;
			}

			ff.has_ce = true;
			ff.has_srst = false;
			ff.sig_d = ff.val_srst;
			changed = true;
		} else if (!worker.opt.keepdc || ff.val_init.is_fully_def()) {
			log("Handling D = Q on %s (%s) from module %s (removing D path).\n",
					cell, cell->type.unescape(), worker.module);
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

			ctrl_t srst = combine_resets(it.first, ff.is_fine, cell);
			new_ff.has_srst = true;
			new_ff.sig_srst = srst.first;
			new_ff.pol_srst = srst.second;
			if (new_ff.has_ce)
				new_ff.ce_over_srst = true;

			Cell *new_cell = new_ff.emit();
			worker.module->swap_names(cell, new_cell);
			if (new_cell)
				dff_cells.push_back(new_cell);

			log("Adding SRST signal on %s (%s) from module %s (D = %s, Q = %s, rval = %s).\n",
					cell, cell->type.unescape(), worker.module,
					log_signal(new_ff.sig_d), log_signal(new_ff.sig_q), log_signal(new_ff.val_srst));
		}

		if (remaining_indices.empty()) {
			worker.module->remove(cell);
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
			if (!worker.opt.simple_dffe)
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
			ctrl_t en = make_patterns_logic(it.first.first, it.first.second, ff.is_fine, cell);

			new_ff.has_ce = true;
			new_ff.sig_ce = en.first;
			new_ff.pol_ce = en.second;
			new_ff.ce_over_srst = false;

			Cell *new_cell = new_ff.emit();
			worker.module->swap_names(cell, new_cell);
			if (new_cell)
				dff_cells.push_back(new_cell);

			log_debug("Adding EN signal on %s (%s) from module %s (D = %s, Q = %s).\n",
					cell, cell->type.unescape(), worker.module,
					log_signal(new_ff.sig_d), log_signal(new_ff.sig_q));
		}

		if (remaining_indices.empty()) {
			worker.module->remove(cell);
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

			FfData ff(&worker.initvals, cell);
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
				log_debug("Handling AD = Q on %s (%s) from module %s (removing async load path).\n",
						cell, cell->type.unescape(), worker.module);
				ff.has_aload = false;
				changed = true;
			}

			// Mux merging
			if (ff.has_clk && ff.sig_d != ff.sig_q) {
				bool can_merge_srst = !ff.has_arst && !ff.has_sr &&
					(!ff.has_srst || !ff.has_ce || ff.ce_over_srst) && !worker.opt.nosdff;

				if (can_merge_srst && try_merge_srst(ff, cell, changed)) {
					did_something = true;
					continue;
				}

				bool can_merge_ce = (!ff.has_srst || !ff.has_ce || !ff.ce_over_srst) && !worker.opt.nodffe;

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
};

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN

bool OptDffWorker::run()
{
	return SimpleContext(*this).run();
}

YOSYS_NAMESPACE_END
