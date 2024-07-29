/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
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

#include "kernel/ffmerge.h"

USING_YOSYS_NAMESPACE

bool FfMergeHelper::is_output_unused(RTLIL::SigSpec sig) {
	for (auto bit : (*sigmap)(sig))
		if (sigbit_users_count[bit] != 0)
			return false;
	return true;
}

bool FfMergeHelper::find_output_ff(RTLIL::SigSpec sig, FfData &ff, pool<std::pair<Cell *, int>> &bits) {
	ff = FfData(module, initvals, NEW_ID);
	sigmap->apply(sig);

	bool found = false;

	for (auto bit : sig)
	{
		if (bit.wire == NULL || sigbit_users_count[bit] == 0) {
			ff.width++;
			ff.sig_q.append(bit);
			ff.sig_d.append(bit);
			ff.sig_clr.append(State::Sx);
			ff.sig_set.append(State::Sx);
			ff.val_init.bits().push_back(State::Sx);
			ff.val_srst.bits().push_back(State::Sx);
			ff.val_arst.bits().push_back(State::Sx);
			continue;
		}

		if (sigbit_users_count[bit] != 1)
			return false;

		auto &sinks = dff_sink[bit];
		if (sinks.size() != 1)
			return false;

		Cell *cell;
		int idx;
		std::tie(cell, idx) = *sinks.begin();
		bits.insert(std::make_pair(cell, idx));

		FfData cur_ff(initvals, cell);

		// Reject latches and $ff.
		if (!cur_ff.has_clk)
			return false;

		log_assert((*sigmap)(cur_ff.sig_d[idx]) == bit);

		if (!found) {
			ff.sig_clk = cur_ff.sig_clk;
			ff.sig_ce = cur_ff.sig_ce;
			ff.sig_aload = cur_ff.sig_aload;
			ff.sig_srst = cur_ff.sig_srst;
			ff.sig_arst = cur_ff.sig_arst;
			ff.has_clk = cur_ff.has_clk;
			ff.has_ce = cur_ff.has_ce;
			ff.has_aload = cur_ff.has_aload;
			ff.has_srst = cur_ff.has_srst;
			ff.has_arst = cur_ff.has_arst;
			ff.has_sr = cur_ff.has_sr;
			ff.ce_over_srst = cur_ff.ce_over_srst;
			ff.pol_clk = cur_ff.pol_clk;
			ff.pol_ce = cur_ff.pol_ce;
			ff.pol_aload = cur_ff.pol_aload;
			ff.pol_arst = cur_ff.pol_arst;
			ff.pol_srst = cur_ff.pol_srst;
			ff.pol_clr = cur_ff.pol_clr;
			ff.pol_set = cur_ff.pol_set;
		} else {
			if (ff.has_clk != cur_ff.has_clk)
				return false;
			if (ff.has_ce != cur_ff.has_ce)
				return false;
			if (ff.has_aload != cur_ff.has_aload)
				return false;
			if (ff.has_srst != cur_ff.has_srst)
				return false;
			if (ff.has_arst != cur_ff.has_arst)
				return false;
			if (ff.has_sr != cur_ff.has_sr)
				return false;
			if (ff.has_clk) {
				if (ff.sig_clk != cur_ff.sig_clk)
					return false;
				if (ff.pol_clk != cur_ff.pol_clk)
					return false;
			}
			if (ff.has_ce) {
				if (ff.sig_ce != cur_ff.sig_ce)
					return false;
				if (ff.pol_ce != cur_ff.pol_ce)
					return false;
			}
			if (ff.has_aload) {
				if (ff.sig_aload != cur_ff.sig_aload)
					return false;
				if (ff.pol_aload != cur_ff.pol_aload)
					return false;
			}
			if (ff.has_srst) {
				if (ff.sig_srst != cur_ff.sig_srst)
					return false;
				if (ff.pol_srst != cur_ff.pol_srst)
					return false;
				if (ff.has_ce && ff.ce_over_srst != cur_ff.ce_over_srst)
					return false;
			}
			if (ff.has_arst) {
				if (ff.sig_arst != cur_ff.sig_arst)
					return false;
				if (ff.pol_arst != cur_ff.pol_arst)
					return false;
			}
			if (ff.has_sr) {
				if (ff.pol_clr != cur_ff.pol_clr)
					return false;
				if (ff.pol_set != cur_ff.pol_set)
					return false;
			}
		}

		ff.width++;
		ff.sig_d.append(cur_ff.sig_d[idx]);
		ff.sig_ad.append(ff.has_aload ? cur_ff.sig_ad[idx] : State::Sx);
		ff.sig_q.append(cur_ff.sig_q[idx]);
		ff.sig_clr.append(ff.has_sr ? cur_ff.sig_clr[idx] : State::S0);
		ff.sig_set.append(ff.has_sr ? cur_ff.sig_set[idx] : State::S0);
		ff.val_arst.bits().push_back(ff.has_arst ? cur_ff.val_arst[idx] : State::Sx);
		ff.val_srst.bits().push_back(ff.has_srst ? cur_ff.val_srst[idx] : State::Sx);
		ff.val_init.bits().push_back(cur_ff.val_init[idx]);
		found = true;
	}

	return found;
}

bool FfMergeHelper::find_input_ff(RTLIL::SigSpec sig, FfData &ff, pool<std::pair<Cell *, int>> &bits) {
	ff = FfData(module, initvals, NEW_ID);
	sigmap->apply(sig);

	bool found = false;

	pool<int> const_bits;

	for (auto bit : sig)
	{
		if (bit.wire == NULL) {
			const_bits.insert(ff.width);
			ff.width++;
			ff.sig_q.append(bit);
			ff.sig_d.append(bit);
			// These two will be fixed up later.
			ff.sig_clr.append(State::Sx);
			ff.sig_set.append(State::Sx);
			ff.val_init.bits().push_back(bit.data);
			ff.val_srst.bits().push_back(bit.data);
			ff.val_arst.bits().push_back(bit.data);
			continue;
		}

		if (!dff_driver.count(bit))
			return false;

		Cell *cell;
		int idx;
		std::tie(cell, idx) = dff_driver[bit];
		bits.insert(std::make_pair(cell, idx));

		FfData cur_ff(initvals, cell);

		log_assert((*sigmap)(cur_ff.sig_q[idx]) == bit);

		if (!found) {
			ff.sig_clk = cur_ff.sig_clk;
			ff.sig_ce = cur_ff.sig_ce;
			ff.sig_aload = cur_ff.sig_aload;
			ff.sig_srst = cur_ff.sig_srst;
			ff.sig_arst = cur_ff.sig_arst;
			ff.has_clk = cur_ff.has_clk;
			ff.has_gclk = cur_ff.has_gclk;
			ff.has_ce = cur_ff.has_ce;
			ff.has_aload = cur_ff.has_aload;
			ff.has_srst = cur_ff.has_srst;
			ff.has_arst = cur_ff.has_arst;
			ff.has_sr = cur_ff.has_sr;
			ff.ce_over_srst = cur_ff.ce_over_srst;
			ff.pol_clk = cur_ff.pol_clk;
			ff.pol_ce = cur_ff.pol_ce;
			ff.pol_aload = cur_ff.pol_aload;
			ff.pol_arst = cur_ff.pol_arst;
			ff.pol_srst = cur_ff.pol_srst;
			ff.pol_clr = cur_ff.pol_clr;
			ff.pol_set = cur_ff.pol_set;
		} else {
			if (ff.has_gclk != cur_ff.has_gclk)
				return false;
			if (ff.has_clk != cur_ff.has_clk)
				return false;
			if (ff.has_ce != cur_ff.has_ce)
				return false;
			if (ff.has_aload != cur_ff.has_aload)
				return false;
			if (ff.has_srst != cur_ff.has_srst)
				return false;
			if (ff.has_arst != cur_ff.has_arst)
				return false;
			if (ff.has_sr != cur_ff.has_sr)
				return false;
			if (ff.has_clk) {
				if (ff.sig_clk != cur_ff.sig_clk)
					return false;
				if (ff.pol_clk != cur_ff.pol_clk)
					return false;
			}
			if (ff.has_ce) {
				if (ff.sig_ce != cur_ff.sig_ce)
					return false;
				if (ff.pol_ce != cur_ff.pol_ce)
					return false;
			}
			if (ff.has_aload) {
				if (ff.sig_aload != cur_ff.sig_aload)
					return false;
				if (ff.pol_aload != cur_ff.pol_aload)
					return false;
			}
			if (ff.has_srst) {
				if (ff.sig_srst != cur_ff.sig_srst)
					return false;
				if (ff.pol_srst != cur_ff.pol_srst)
					return false;
				if (ff.has_ce && ff.ce_over_srst != cur_ff.ce_over_srst)
					return false;
			}
			if (ff.has_arst) {
				if (ff.sig_arst != cur_ff.sig_arst)
					return false;
				if (ff.pol_arst != cur_ff.pol_arst)
					return false;
			}
			if (ff.has_sr) {
				if (ff.pol_clr != cur_ff.pol_clr)
					return false;
				if (ff.pol_set != cur_ff.pol_set)
					return false;
			}
		}

		ff.width++;
		ff.sig_d.append((ff.has_clk || ff.has_gclk) ? cur_ff.sig_d[idx] : State::Sx);
		ff.sig_ad.append(ff.has_aload ? cur_ff.sig_ad[idx] : State::Sx);
		ff.sig_q.append(cur_ff.sig_q[idx]);
		ff.sig_clr.append(ff.has_sr ? cur_ff.sig_clr[idx] : State::S0);
		ff.sig_set.append(ff.has_sr ? cur_ff.sig_set[idx] : State::S0);
		ff.val_arst.bits().push_back(ff.has_arst ? cur_ff.val_arst[idx] : State::Sx);
		ff.val_srst.bits().push_back(ff.has_srst ? cur_ff.val_srst[idx] : State::Sx);
		ff.val_init.bits().push_back(cur_ff.val_init[idx]);
		found = true;
	}

	if (found && ff.has_sr) {
		for (auto i: const_bits) {
			if (ff.sig_d[i] == State::S0) {
				ff.sig_set[i] = ff.pol_set ? State::S0 : State::S1;
			} else if (ff.sig_d[i] == State::S1) {
				ff.sig_clr[i] = ff.pol_clr ? State::S0 : State::S1;
			}
		}
	}

	return found;
}


void FfMergeHelper::remove_output_ff(const pool<std::pair<Cell *, int>> &bits) {
	for (auto &it : bits) {
		Cell *cell = it.first;
		int idx = it.second;
		SigSpec q = cell->getPort(ID::Q);
		initvals->remove_init(q[idx]);
		dff_driver.erase((*sigmap)(q[idx]));
		q[idx] = module->addWire(stringf("$ffmerge_disconnected$%d", autoidx++));
		cell->setPort(ID::Q, q);
	}
}

void FfMergeHelper::mark_input_ff(const pool<std::pair<Cell *, int>> &bits) {
	for (auto &it : bits) {
		Cell *cell = it.first;
		int idx = it.second;
		if (cell->hasPort(ID::D)) {
			SigSpec d = cell->getPort(ID::D);
			// The user count was already at least 1
			// (for the D port).  Bump it as it is now connected
			// to the merged-to cell as well.  This suffices for
			// it to not be considered for output merging.
			sigbit_users_count[d[idx]]++;
		}
	}
}

void FfMergeHelper::set(FfInitVals *initvals_, RTLIL::Module *module_)
{
	clear();
	initvals = initvals_;
	sigmap = initvals->sigmap;
	module = module_;

	for (auto wire : module->wires()) {
		if (wire->port_output)
			for (auto bit : (*sigmap)(wire))
				sigbit_users_count[bit]++;
	}

	for (auto cell : module->cells()) {
		if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
			if (cell->hasPort(ID::D)) {
				SigSpec d = (*sigmap)(cell->getPort(ID::D));
				for (int i = 0; i < GetSize(d); i++)
					dff_sink[d[i]].insert(std::make_pair(cell, i));
			}
			SigSpec q = (*sigmap)(cell->getPort(ID::Q));
			for (int i = 0; i < GetSize(q); i++)
				dff_driver[q[i]] = std::make_pair(cell, i);
		}
		for (auto &conn : cell->connections())
			if (!cell->known() || cell->input(conn.first))
				for (auto bit : (*sigmap)(conn.second))
					sigbit_users_count[bit]++;
	}
}

void FfMergeHelper::clear() {
	dff_driver.clear();
	dff_sink.clear();
	sigbit_users_count.clear();
}
