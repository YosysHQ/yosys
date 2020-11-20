/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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
#include "kernel/satgen.h"
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
	typedef std::pair<RTLIL::Cell*, int> cell_int_t;
	SigMap sigmap;
	FfInitVals initvals;
	dict<SigBit, int> bitusers;
	dict<SigBit, cell_int_t> bit2mux;
	dict<SigBit, RTLIL::Cell*> bit2driver;

	typedef std::map<RTLIL::SigBit, bool> pattern_t;
	typedef std::set<pattern_t> patterns_t;
	typedef std::pair<RTLIL::SigBit, bool> ctrl_t;
	typedef std::set<ctrl_t> ctrls_t;

	ezSatPtr ez;
	SatGen satgen;
	pool<Cell*> sat_cells;

	// Used as a queue.
	std::vector<Cell *> dff_cells;

	OptDffWorker(const OptDffOptions &opt, Module *mod) : opt(opt), module(mod), sigmap(mod), initvals(&sigmap, mod), ez(), satgen(ez.get(), &sigmap) {
		// Gathering three kinds of information here for every sigmapped SigBit:
		//
		// - bitusers: how many users it has (muxes will only be merged into FFs if this is 1, making the FF the only user)
		// - bit2mux: the mux cell and bit index that drives it, if any
		// - bit2driver: the cell driving it, if any

		for (auto wire : module->wires())
		{
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					bitusers[bit]++;
		}

		for (auto cell : module->cells()) {
			if (cell->type.in(ID($mux), ID($pmux), ID($_MUX_))) {
				RTLIL::SigSpec sig_y = sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < GetSize(sig_y); i++)
					bit2mux[sig_y[i]] = cell_int_t(cell, i);
			}

			for (auto conn : cell->connections()) {
				bool is_output = cell->output(conn.first);
				if (is_output) {
					for (auto bit : sigmap(conn.second))
						bit2driver[bit] = cell;
				}
				if (!is_output || !cell->known()) {
					for (auto bit : sigmap(conn.second))
						bitusers[bit]++;
				}
			}

			if (module->design->selected(module, cell) && RTLIL::builtin_ff_cell_types().count(cell->type))
				dff_cells.push_back(cell);
		}

	}

	std::function<void(Cell*)> sat_import_cell = [&](Cell *c) {
		if (!sat_cells.insert(c).second)
			return;
		if (!satgen.importCell(c))
			return;
		for (auto &conn : c->connections()) {
			if (!c->input(conn.first))
				continue;
			for (auto bit : sigmap(conn.second))
				if (bit2driver.count(bit))
					sat_import_cell(bit2driver.at(bit));
		}
	};

	State combine_const(State a, State b) {
		if (a == State::Sx && !opt.keepdc)
			return b;
		if (b == State::Sx && !opt.keepdc)
			return a;
		if (a == b)
			return a;
		return State::Sm;
	}

	patterns_t find_muxtree_feedback_patterns(RTLIL::SigBit d, RTLIL::SigBit q, pattern_t path)
	{
		patterns_t ret;

		if (d == q) {
			ret.insert(path);
			return ret;
		}

		if (bit2mux.count(d) == 0 || bitusers[d] > 1)
			return ret;

		cell_int_t mbit = bit2mux.at(d);
		RTLIL::SigSpec sig_a = sigmap(mbit.first->getPort(ID::A));
		RTLIL::SigSpec sig_b = sigmap(mbit.first->getPort(ID::B));
		RTLIL::SigSpec sig_s = sigmap(mbit.first->getPort(ID::S));
		int width = GetSize(sig_a), index = mbit.second;

		for (int i = 0; i < GetSize(sig_s); i++)
			if (path.count(sig_s[i]) && path.at(sig_s[i]))
			{
				ret = find_muxtree_feedback_patterns(sig_b[i*width + index], q, path);

				if (sig_b[i*width + index] == q) {
					RTLIL::SigSpec s = mbit.first->getPort(ID::B);
					s[i*width + index] = RTLIL::Sx;
					mbit.first->setPort(ID::B, s);
				}

				return ret;
			}

		pattern_t path_else = path;

		for (int i = 0; i < GetSize(sig_s); i++)
		{
			if (path.count(sig_s[i]))
				continue;

			pattern_t path_this = path;
			path_else[sig_s[i]] = false;
			path_this[sig_s[i]] = true;

			for (auto &pat : find_muxtree_feedback_patterns(sig_b[i*width + index], q, path_this))
				ret.insert(pat);

			if (sig_b[i*width + index] == q) {
				RTLIL::SigSpec s = mbit.first->getPort(ID::B);
				s[i*width + index] = RTLIL::Sx;
				mbit.first->setPort(ID::B, s);
			}
		}

		for (auto &pat : find_muxtree_feedback_patterns(sig_a[index], q, path_else))
			ret.insert(pat);

		if (sig_a[index] == q) {
			RTLIL::SigSpec s = mbit.first->getPort(ID::A);
			s[index] = RTLIL::Sx;
			mbit.first->setPort(ID::A, s);
		}

		return ret;
	}

	void simplify_patterns(patterns_t&)
	{
		// TBD
	}

	ctrl_t make_patterns_logic(const patterns_t &patterns, const ctrls_t &ctrls, bool make_gates)
	{
		if (patterns.empty() && GetSize(ctrls) == 1) {
			return *ctrls.begin();
		}

		RTLIL::SigSpec or_input;

		for (auto pat : patterns)
		{
			RTLIL::SigSpec s1, s2;
			for (auto it : pat) {
				s1.append(it.first);
				s2.append(it.second);
			}

			RTLIL::SigSpec y = module->addWire(NEW_ID);
			RTLIL::Cell *c = module->addNe(NEW_ID, s1, s2, y);

			if (make_gates) {
				simplemap(module, c);
				module->remove(c);
			}

			or_input.append(y);
		}
		for (auto item : ctrls) {
			if (item.second)
				or_input.append(item.first);
			else if (make_gates)
				or_input.append(module->NotGate(NEW_ID, item.first));
			else
				or_input.append(module->Not(NEW_ID, item.first));
		}

		if (GetSize(or_input) == 0)
			return ctrl_t(State::S1, true);

		if (GetSize(or_input) == 1)
			return ctrl_t(or_input, true);

		RTLIL::SigSpec y = module->addWire(NEW_ID);
		RTLIL::Cell *c = module->addReduceAnd(NEW_ID, or_input, y);

		if (make_gates) {
			simplemap(module, c);
			module->remove(c);
		}

		return ctrl_t(y, true);
	}

	ctrl_t combine_resets(const ctrls_t &ctrls, bool make_gates)
	{
		if (GetSize(ctrls) == 1) {
			return *ctrls.begin();
		}

		RTLIL::SigSpec or_input;

		bool final_pol = false;
		for (auto item : ctrls) {
			if (item.second)
				final_pol = true;
		}

		for (auto item : ctrls) {
			if (item.second == final_pol)
				or_input.append(item.first);
			else if (make_gates)
				or_input.append(module->NotGate(NEW_ID, item.first));
			else
				or_input.append(module->Not(NEW_ID, item.first));
		}

		RTLIL::SigSpec y = module->addWire(NEW_ID);
		RTLIL::Cell *c = final_pol ? module->addReduceOr(NEW_ID, or_input, y) : module->addReduceAnd(NEW_ID, or_input, y);

		if (make_gates) {
			simplemap(module, c);
			module->remove(c);
		}

		return ctrl_t(y, final_pol);
	}

	bool run() {
		// We have all the information we need, and the list of FFs to process as well.  Do it.
		bool did_something = false;
		while (!dff_cells.empty()) {
			Cell *cell = dff_cells.back();
			dff_cells.pop_back();
			// Break down the FF into pieces.
			FfData ff(&initvals, cell);
			bool changed = false;

			if (!ff.width) {
				module->remove(cell);
				did_something = true;
				continue;
			}

			if (ff.has_sr) {
				bool sr_removed = false;
				std::vector<int> keep_bits;
				// Check for always-active S/R bits.
				for (int i = 0; i < ff.width; i++) {
					if (ff.sig_clr[i] == (ff.pol_clr ? State::S1 : State::S0) || (!opt.keepdc && ff.sig_clr[i] == State::Sx)) {
						// Always-active clear — connect Q bit to 0.
						initvals.remove_init(ff.sig_q[i]);
						module->connect(ff.sig_q[i], State::S0);
						log("Handling always-active CLR at position %d on %s (%s) from module %s (changing to const driver).\n",
								i, log_id(cell), log_id(cell->type), log_id(module));
						sr_removed = true;
					} else if (ff.sig_set[i] == (ff.pol_set ? State::S1 : State::S0) || (!opt.keepdc && ff.sig_set[i] == State::Sx)) {
						// Always-active set — connect Q bit to 1 if clear inactive, 0 if reset active.
						initvals.remove_init(ff.sig_q[i]);
						if (!ff.pol_clr) {
							module->connect(ff.sig_q[i], ff.sig_clr[i]);
						} else if (ff.is_fine) {
							module->addNotGate(NEW_ID, ff.sig_q[i], ff.sig_clr[i]);
						} else {
							module->addNot(NEW_ID, ff.sig_q[i], ff.sig_clr[i]);
						}
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
						did_something = true;
						continue;
					}
					ff = ff.slice(keep_bits);
					changed = true;
				}

				if (ff.pol_clr ? ff.sig_clr.is_fully_zero() : ff.sig_clr.is_fully_ones()) {
					// CLR is useless, try to kill it.
					bool failed = false;
					for (int i = 0; i < ff.width; i++)
						if (ff.sig_set[i] != ff.sig_set[0])
							failed = true;
					if (!failed) {
						log("Removing never-active CLR on %s (%s) from module %s.\n",
								log_id(cell), log_id(cell->type), log_id(module));
						ff.has_sr = false;
						ff.has_arst = true;
						ff.pol_arst = ff.pol_set;
						ff.sig_arst = ff.sig_set[0];
						ff.val_arst = Const(State::S1, ff.width);
						changed = true;
					}
				} else if (ff.pol_set ? ff.sig_set.is_fully_zero() : ff.sig_set.is_fully_ones()) {
					// SET is useless, try to kill it.
					bool failed = false;
					for (int i = 0; i < ff.width; i++)
						if (ff.sig_clr[i] != ff.sig_clr[0])
							failed = true;
					if (!failed) {
						log("Removing never-active SET on %s (%s) from module %s.\n",
								log_id(cell), log_id(cell->type), log_id(module));
						ff.has_sr = false;
						ff.has_arst = true;
						ff.pol_arst = ff.pol_clr;
						ff.sig_arst = ff.sig_clr[0];
						ff.val_arst = Const(State::S0, ff.width);
						changed = true;
					}
				} else if (ff.pol_clr == ff.pol_set) {
					// Try a more complex conversion to plain async reset.
					State val_neutral = ff.pol_set ? State::S0 : State::S1;
					Const val_arst;
					SigSpec sig_arst;
					if (ff.sig_clr[0] == val_neutral)
						sig_arst = ff.sig_set[0];
					else
						sig_arst = ff.sig_clr[0];
					bool failed = false;
					for (int i = 0; i < ff.width; i++) {
						if (ff.sig_clr[i] == sig_arst && ff.sig_set[i] == val_neutral)
							val_arst.bits.push_back(State::S0);
						else if (ff.sig_set[i] == sig_arst && ff.sig_clr[i] == val_neutral)
							val_arst.bits.push_back(State::S1);
						else
							failed = true;
					}
					if (!failed) {
						log("Converting CLR/SET to ARST on %s (%s) from module %s.\n",
								log_id(cell), log_id(cell->type), log_id(module));
						ff.has_sr = false;
						ff.has_arst = true;
						ff.val_arst = val_arst;
						ff.sig_arst = sig_arst;
						ff.pol_arst = ff.pol_clr;
						changed = true;
					}
				}
			}

			if (ff.has_arst) {
				if (ff.sig_arst == (ff.pol_arst ? State::S0 : State::S1)) {
					// Always-inactive reset — remove.
					log("Removing never-active ARST on %s (%s) from module %s.\n",
							log_id(cell), log_id(cell->type), log_id(module));
					ff.has_arst = false;
					changed = true;
				} else if (ff.sig_arst == (ff.pol_arst ? State::S1 : State::S0) || (!opt.keepdc && ff.sig_arst == State::Sx)) {
					// Always-active async reset — change to const driver.
					log("Handling always-active ARST on %s (%s) from module %s (changing to const driver).\n",
							log_id(cell), log_id(cell->type), log_id(module));
					initvals.remove_init(ff.sig_q);
					module->remove(cell);
					module->connect(ff.sig_q, ff.val_arst);
					did_something = true;
					continue;
				}
			}

			if (ff.has_srst) {
				if (ff.sig_srst == (ff.pol_srst ? State::S0 : State::S1)) {
					// Always-inactive reset — remove.
					log("Removing never-active SRST on %s (%s) from module %s.\n",
							log_id(cell), log_id(cell->type), log_id(module));
					ff.has_srst = false;
					changed = true;
				} else if (ff.sig_srst == (ff.pol_srst ? State::S1 : State::S0) || (!opt.keepdc && ff.sig_srst == State::Sx)) {
					// Always-active sync reset — connect to D instead.
					log("Handling always-active SRST on %s (%s) from module %s (changing to const D).\n",
							log_id(cell), log_id(cell->type), log_id(module));
					ff.has_srst = false;
					if (!ff.ce_over_srst)
						ff.has_en = false;
					ff.sig_d = ff.val_d = ff.val_srst;
					ff.d_is_const = true;
					changed = true;
				}
			}

			if (ff.has_en) {
				if (ff.sig_en == (ff.pol_en ? State::S0 : State::S1) || (!opt.keepdc && ff.sig_en == State::Sx)) {
					// Always-inactive enable — remove.
					if (ff.has_clk && ff.has_srst && !ff.ce_over_srst) {
						log("Handling never-active EN on %s (%s) from module %s (connecting SRST instead).\n",
								log_id(cell), log_id(cell->type), log_id(module));
						// FF with sync reset — connect the sync reset to D instead.
						ff.pol_en = ff.pol_srst;
						ff.sig_en = ff.sig_srst;
						ff.has_srst = false;
						ff.sig_d = ff.val_d = ff.val_srst;
						ff.d_is_const = true;
						changed = true;
					} else {
						log("Handling never-active EN on %s (%s) from module %s (removing D path).\n",
								log_id(cell), log_id(cell->type), log_id(module));
						// The D input path is effectively useless, so remove it (this will be a const-input D latch, SR latch, or a const driver).
						ff.has_d = ff.has_en = ff.has_clk = false;
						changed = true;
					}
				} else if (ff.sig_en == (ff.pol_en ? State::S1 : State::S0)) {
					// Always-active enable.
					if (ff.has_clk) {
						// For FF, just remove the useless enable.
						log("Removing always-active EN on %s (%s) from module %s.\n",
								log_id(cell), log_id(cell->type), log_id(module));
						ff.has_en = false;
						changed = true;
					} else {
						// For latches, make a comb circuit, nuke the latch.
						log("Handling always-active EN on %s (%s) from module %s (changing to combinatorial circuit).\n",
								log_id(cell), log_id(cell->type), log_id(module));
						initvals.remove_init(ff.sig_q);
						module->remove(cell);
						if (ff.has_sr) {
							SigSpec tmp;
							if (ff.is_fine) {
								if (ff.pol_set)
									tmp = module->MuxGate(NEW_ID, ff.sig_d, State::S1, ff.sig_set);
								else
									tmp = module->MuxGate(NEW_ID, State::S1, ff.sig_d, ff.sig_set);
								if (ff.pol_clr)
									module->addMuxGate(NEW_ID, tmp, State::S0, ff.sig_clr, ff.sig_q);
								else
									module->addMuxGate(NEW_ID, State::S0, tmp, ff.sig_clr, ff.sig_q);
							} else {
								if (ff.pol_set)
									tmp = module->Or(NEW_ID, ff.sig_d, ff.sig_set);
								else
									tmp = module->Or(NEW_ID, ff.sig_d, module->Not(NEW_ID, ff.sig_set));
								if (ff.pol_clr)
									module->addAnd(NEW_ID, tmp, module->Not(NEW_ID, ff.sig_clr), ff.sig_q);
								else
									module->addAnd(NEW_ID, tmp, ff.sig_clr, ff.sig_q);
							}
						} else if (ff.has_arst) {
							if (ff.is_fine) {
								if (ff.pol_arst)
									module->addMuxGate(NEW_ID, ff.sig_d, ff.val_arst[0], ff.sig_arst, ff.sig_q);
								else
									module->addMuxGate(NEW_ID, ff.val_arst[0], ff.sig_d, ff.sig_arst, ff.sig_q);
							} else {
								if (ff.pol_arst)
									module->addMux(NEW_ID, ff.sig_d, ff.val_arst, ff.sig_arst, ff.sig_q);
								else
									module->addMux(NEW_ID, ff.val_arst, ff.sig_d, ff.sig_arst, ff.sig_q);
							}
						} else {
							module->connect(ff.sig_q, ff.sig_d);
						}
						did_something = true;
						continue;
					}
				}
			}

			if (ff.has_clk) {
				if (ff.sig_clk.is_fully_const()) {
					// Const clock — the D input path is effectively useless, so remove it (this will be a const-input D latch, SR latch, or a const driver).
					log("Handling const CLK on %s (%s) from module %s (removing D path).\n",
							log_id(cell), log_id(cell->type), log_id(module));
					ff.has_d = ff.has_en = ff.has_clk = ff.has_srst = false;
					changed = true;
				}
			}

			if (ff.has_d && ff.sig_d == ff.sig_q) {
				// Q wrapped back to D, can be removed.
				if (ff.has_clk && ff.has_srst) {
					// FF with sync reset — connect the sync reset to D instead.
					log("Handling D = Q on %s (%s) from module %s (conecting SRST instead).\n",
							log_id(cell), log_id(cell->type), log_id(module));
					if (ff.has_en && ff.ce_over_srst) {
						if (!ff.pol_en) {
							if (ff.is_fine)
								ff.sig_en = module->NotGate(NEW_ID, ff.sig_en);
							else
								ff.sig_en = module->Not(NEW_ID, ff.sig_en);
						}
						if (!ff.pol_srst) {
							if (ff.is_fine)
								ff.sig_srst = module->NotGate(NEW_ID, ff.sig_srst);
							else
								ff.sig_srst = module->Not(NEW_ID, ff.sig_srst);
						}
						if (ff.is_fine)
							ff.sig_en = module->AndGate(NEW_ID, ff.sig_en, ff.sig_srst);
						else
							ff.sig_en = module->And(NEW_ID, ff.sig_en, ff.sig_srst);
						ff.pol_en = true;
					} else {
						ff.pol_en = ff.pol_srst;
						ff.sig_en = ff.sig_srst;
					}
					ff.has_en = true;
					ff.has_srst = false;
					ff.sig_d = ff.val_d = ff.val_srst;
					ff.d_is_const = true;
					changed = true;
				} else {
					// The D input path is effectively useless, so remove it (this will be a const-input D latch, SR latch, or a const driver).
					log("Handling D = Q on %s (%s) from module %s (removing D path).\n",
							log_id(cell), log_id(cell->type), log_id(module));
					ff.has_d = ff.has_en = ff.has_clk = false;
					changed = true;
				}
			}

			// Now check if any bit can be replaced by a constant.
			pool<int> removed_sigbits;
			for (int i = 0; i < ff.width; i++) {
				State val = ff.val_init[i];
				if (ff.has_arst)
					val = combine_const(val, ff.val_arst[i]);
				if (ff.has_srst)
					val = combine_const(val, ff.val_srst[i]);
				if (ff.has_sr) {
					if (ff.sig_clr[i] != (ff.pol_clr ? State::S0 : State::S1))
						val = combine_const(val, State::S0);
					if (ff.sig_set[i] != (ff.pol_set ? State::S0 : State::S1))
						val = combine_const(val, State::S1);
				}
				if (val == State::Sm)
					continue;
				if (ff.has_d) {
					if (!ff.sig_d[i].wire) {
						val = combine_const(val, ff.sig_d[i].data);
						if (val == State::Sm)
							continue;
					} else {
						if (!opt.sat)
							continue;
						// For each register bit, try to prove that it cannot change from the initial value. If so, remove it
						if (!bit2driver.count(ff.sig_d[i]))
							continue;
						if (val != State::S0 && val != State::S1)
							continue;

						sat_import_cell(bit2driver.at(ff.sig_d[i]));

						int init_sat_pi = satgen.importSigSpec(val).front();
						int q_sat_pi = satgen.importSigBit(ff.sig_q[i]);
						int d_sat_pi = satgen.importSigBit(ff.sig_d[i]);

						// Try to find out whether the register bit can change under some circumstances
						bool counter_example_found = ez->solve(ez->IFF(q_sat_pi, init_sat_pi), ez->NOT(ez->IFF(d_sat_pi, init_sat_pi)));

						// If the register bit cannot change, we can replace it with a constant
						if (counter_example_found)
							continue;
					}
				}
				log("Setting constant %d-bit at position %d on %s (%s) from module %s.\n", val ? 1 : 0,
						i, log_id(cell), log_id(cell->type), log_id(module));

				initvals.remove_init(ff.sig_q[i]);
				module->connect(ff.sig_q[i], val);
				removed_sigbits.insert(i);
			}
			if (!removed_sigbits.empty()) {
				std::vector<int> keep_bits;
				for (int i = 0; i < ff.width; i++)
					if (!removed_sigbits.count(i))
						keep_bits.push_back(i);
				if (keep_bits.empty()) {
					module->remove(cell);
					did_something = true;
					continue;
				}
				ff = ff.slice(keep_bits);
				changed = true;
			}

			// The cell has been simplified as much as possible already.  Now try to spice it up with enables / sync resets.
			if (ff.has_clk) {
				if (!ff.has_arst && !ff.has_sr && (!ff.has_srst || !ff.has_en || ff.ce_over_srst) && !opt.nosdff) {
					// Try to merge sync resets.
					std::map<ctrls_t, std::vector<int>> groups;
					std::vector<int> remaining_indices;
					Const val_srst;

					for (int i = 0 ; i < ff.width; i++) {
						ctrls_t resets;
						State reset_val = State::Sx;
						if (ff.has_srst)
							reset_val = ff.val_srst[i];
						while (bit2mux.count(ff.sig_d[i]) && bitusers[ff.sig_d[i]] == 1) {
							cell_int_t mbit = bit2mux.at(ff.sig_d[i]);
							if (GetSize(mbit.first->getPort(ID::S)) != 1)
								break;
							SigBit s = mbit.first->getPort(ID::S);
							SigBit a = mbit.first->getPort(ID::A)[mbit.second];
							SigBit b = mbit.first->getPort(ID::B)[mbit.second];
							// Workaround for funny memory WE pattern.
							if ((a == State::S0 || a == State::S1) && (b == State::S0 || b == State::S1))
								break;
							if ((b == State::S0 || b == State::S1) && (b == reset_val || reset_val == State::Sx)) {
								// This is better handled by CE pattern.
								if (a == ff.sig_q[i])
									break;
								reset_val = b.data;
								resets.insert(ctrl_t(s, true));
								ff.sig_d[i] = a;
							} else if ((a == State::S0 || a == State::S1) && (a == reset_val || reset_val == State::Sx)) {
								// This is better handled by CE pattern.
								if (b == ff.sig_q[i])
									break;
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
						} else
							remaining_indices.push_back(i);
						val_srst.bits.push_back(reset_val);
					}

					for (auto &it : groups) {
						FfData new_ff = ff.slice(it.second);
						new_ff.val_srst = Const();
						for (int i = 0; i < new_ff.width; i++) {
							int j = it.second[i];
							new_ff.val_srst.bits.push_back(val_srst[j]);
						}
						ctrl_t srst = combine_resets(it.first, ff.is_fine);

						new_ff.has_srst = true;
						new_ff.sig_srst = srst.first;
						new_ff.pol_srst = srst.second;
						if (new_ff.has_en)
							new_ff.ce_over_srst = true;
						Cell *new_cell = new_ff.emit(module, NEW_ID);
						if (new_cell)
							dff_cells.push_back(new_cell);
						log("Adding SRST signal on %s (%s) from module %s (D = %s, Q = %s, rval = %s).\n",
								log_id(cell), log_id(cell->type), log_id(module), log_signal(new_ff.sig_d), log_signal(new_ff.sig_q), log_signal(new_ff.val_srst));
					}

					if (remaining_indices.empty()) {
						module->remove(cell);
						did_something = true;
						continue;
					} else if (GetSize(remaining_indices) != ff.width) {
						ff = ff.slice(remaining_indices);
						changed = true;
					}
				}
				if ((!ff.has_srst || !ff.has_en || !ff.ce_over_srst) && !opt.nodffe) {
					// Try to merge enables.
					std::map<std::pair<patterns_t, ctrls_t>, std::vector<int>> groups;
					std::vector<int> remaining_indices;

					for (int i = 0 ; i < ff.width; i++) {
						// First, eat up as many simple muxes as possible.
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
							if (ff.has_en)
								enables.insert(ctrl_t(ff.sig_en, ff.pol_en));
							simplify_patterns(patterns);
							groups[std::make_pair(patterns, enables)].push_back(i);
						} else
							remaining_indices.push_back(i);
					}

					for (auto &it : groups) {
						FfData new_ff = ff.slice(it.second);
						ctrl_t en = make_patterns_logic(it.first.first, it.first.second, ff.is_fine);

						new_ff.has_en = true;
						new_ff.sig_en = en.first;
						new_ff.pol_en = en.second;
						new_ff.ce_over_srst = false;
						Cell *new_cell = new_ff.emit(module, NEW_ID);
						if (new_cell)
							dff_cells.push_back(new_cell);
						log("Adding EN signal on %s (%s) from module %s (D = %s, Q = %s).\n",
								log_id(cell), log_id(cell->type), log_id(module), log_signal(new_ff.sig_d), log_signal(new_ff.sig_q));
					}

					if (remaining_indices.empty()) {
						module->remove(cell);
						did_something = true;
						continue;
					} else if (GetSize(remaining_indices) != ff.width) {
						ff = ff.slice(remaining_indices);
						changed = true;
					}
				}
			}

			if (changed) {
				// Rebuild the FF.
				IdString name = cell->name;
				module->remove(cell);
				ff.emit(module, name);
				did_something = true;
			}
		}
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
		log("and synchronous reset multiplexers, removing unused control inputs, or potentially\n");
		log("removes the flip-flop altogether, converting it to a constant driver.\n");
		log("\n");
		log("    -nodffe\n");
		log("        disables dff -> dffe conversion, and other transforms recognizing clock enable\n");
		log("\n");
		log("    -nosdff\n");
		log("        disables dff -> sdff conversion, and other transforms recognizing sync resets\n");
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
			if (args[argidx] == "-nodffe") {
				opt.nodffe = true;
				continue;
			}
			if (args[argidx] == "-nosdff") {
				opt.nosdff = true;
				continue;
			}
			if (args[argidx] == "-simple-dffe") {
				opt.simple_dffe = true;
				continue;
			}
			if (args[argidx] == "-keepdc") {
				opt.keepdc = true;
				continue;
			}
			if (args[argidx] == "-sat") {
				opt.sat = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		bool did_something = false;
		for (auto mod : design->selected_modules()) {
			OptDffWorker worker(opt, mod);
			if (worker.run())
				did_something = true;
		}

		if (did_something)
			design->scratchpad_set_bool("opt.did_something", true);
	}
} OptDffPass;

PRIVATE_NAMESPACE_END
