/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
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

USING_YOSYS_NAMESPACE

FfData::FfData(FfInitVals *initvals, Cell *cell_) : FfData(cell_->module, initvals, cell_->name)
{
	cell = cell_;
	sig_q = cell->getPort(ID::Q);
	width = GetSize(sig_q);
	attributes = cell->attributes;

	if (initvals)
		val_init = (*initvals)(sig_q);

	std::string type_str = cell->type.str();

	if (cell->type.in(ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($dffsre), ID($adff), ID($adffe), ID($aldff), ID($aldffe), ID($sdff), ID($sdffe), ID($sdffce), ID($dlatch), ID($adlatch), ID($dlatchsr), ID($sr))) {
		if (cell->type == ID($ff)) {
			has_gclk = true;
			sig_d = cell->getPort(ID::D);
		} else if (cell->type == ID($sr)) {
			// No data input at all.
		} else if (cell->type.in(ID($dlatch), ID($adlatch), ID($dlatchsr))) {
			has_aload = true;
			sig_aload = cell->getPort(ID::EN);
			pol_aload = cell->getParam(ID::EN_POLARITY).as_bool();
			sig_ad = cell->getPort(ID::D);
		} else {
			has_clk = true;
			sig_clk = cell->getPort(ID::CLK);
			pol_clk = cell->getParam(ID::CLK_POLARITY).as_bool();
			sig_d = cell->getPort(ID::D);
		}
		if (cell->type.in(ID($dffe), ID($dffsre), ID($adffe), ID($aldffe), ID($sdffe), ID($sdffce))) {
			has_ce = true;
			sig_ce = cell->getPort(ID::EN);
			pol_ce = cell->getParam(ID::EN_POLARITY).as_bool();
		}
		if (cell->type.in(ID($dffsr), ID($dffsre), ID($dlatchsr), ID($sr))) {
			has_sr = true;
			sig_clr = cell->getPort(ID::CLR);
			sig_set = cell->getPort(ID::SET);
			pol_clr = cell->getParam(ID::CLR_POLARITY).as_bool();
			pol_set = cell->getParam(ID::SET_POLARITY).as_bool();
		}
		if (cell->type.in(ID($aldff), ID($aldffe))) {
			has_aload = true;
			sig_aload = cell->getPort(ID::ALOAD);
			pol_aload = cell->getParam(ID::ALOAD_POLARITY).as_bool();
			sig_ad = cell->getPort(ID::AD);
		}
		if (cell->type.in(ID($adff), ID($adffe), ID($adlatch))) {
			has_arst = true;
			sig_arst = cell->getPort(ID::ARST);
			pol_arst = cell->getParam(ID::ARST_POLARITY).as_bool();
			val_arst = cell->getParam(ID::ARST_VALUE);
		}
		if (cell->type.in(ID($sdff), ID($sdffe), ID($sdffce))) {
			has_srst = true;
			sig_srst = cell->getPort(ID::SRST);
			pol_srst = cell->getParam(ID::SRST_POLARITY).as_bool();
			val_srst = cell->getParam(ID::SRST_VALUE);
			ce_over_srst = cell->type == ID($sdffce);
		}
	} else if (cell->type == ID($_FF_)) {
		is_fine = true;
		has_gclk = true;
		sig_d = cell->getPort(ID::D);
	} else if (type_str.substr(0, 5) == "$_SR_") {
		is_fine = true;
		has_sr = true;
		pol_set = type_str[5] == 'P';
		pol_clr = type_str[6] == 'P';
		sig_set = cell->getPort(ID::S);
		sig_clr = cell->getPort(ID::R);
	} else if (type_str.substr(0, 6) == "$_DFF_" && type_str.size() == 8) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[6] == 'P';
		sig_clk = cell->getPort(ID::C);
	} else if (type_str.substr(0, 7) == "$_DFFE_" && type_str.size() == 10) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[7] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_ce = true;
		pol_ce = type_str[8] == 'P';
		sig_ce = cell->getPort(ID::E);
	} else if (type_str.substr(0, 6) == "$_DFF_" && type_str.size() == 10) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[6] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_arst = true;
		pol_arst = type_str[7] == 'P';
		sig_arst = cell->getPort(ID::R);
		val_arst = type_str[8] == '1' ? State::S1 : State::S0;
	} else if (type_str.substr(0, 7) == "$_DFFE_" && type_str.size() == 12) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[7] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_arst = true;
		pol_arst = type_str[8] == 'P';
		sig_arst = cell->getPort(ID::R);
		val_arst = type_str[9] == '1' ? State::S1 : State::S0;
		has_ce = true;
		pol_ce = type_str[10] == 'P';
		sig_ce = cell->getPort(ID::E);
	} else if (type_str.substr(0, 8) == "$_ALDFF_" && type_str.size() == 11) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[8] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_aload = true;
		pol_aload = type_str[9] == 'P';
		sig_aload = cell->getPort(ID::L);
		sig_ad = cell->getPort(ID::AD);
	} else if (type_str.substr(0, 9) == "$_ALDFFE_" && type_str.size() == 13) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[9] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_aload = true;
		pol_aload = type_str[10] == 'P';
		sig_aload = cell->getPort(ID::L);
		sig_ad = cell->getPort(ID::AD);
		has_ce = true;
		pol_ce = type_str[11] == 'P';
		sig_ce = cell->getPort(ID::E);
	} else if (type_str.substr(0, 8) == "$_DFFSR_" && type_str.size() == 12) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[8] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_sr = true;
		pol_set = type_str[9] == 'P';
		pol_clr = type_str[10] == 'P';
		sig_set = cell->getPort(ID::S);
		sig_clr = cell->getPort(ID::R);
	} else if (type_str.substr(0, 9) == "$_DFFSRE_" && type_str.size() == 14) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[9] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_sr = true;
		pol_set = type_str[10] == 'P';
		pol_clr = type_str[11] == 'P';
		sig_set = cell->getPort(ID::S);
		sig_clr = cell->getPort(ID::R);
		has_ce = true;
		pol_ce = type_str[12] == 'P';
		sig_ce = cell->getPort(ID::E);
	} else if (type_str.substr(0, 7) == "$_SDFF_" && type_str.size() == 11) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[7] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_srst = true;
		pol_srst = type_str[8] == 'P';
		sig_srst = cell->getPort(ID::R);
		val_srst = type_str[9] == '1' ? State::S1 : State::S0;
	} else if (type_str.substr(0, 8) == "$_SDFFE_" && type_str.size() == 13) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[8] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_srst = true;
		pol_srst = type_str[9] == 'P';
		sig_srst = cell->getPort(ID::R);
		val_srst = type_str[10] == '1' ? State::S1 : State::S0;
		has_ce = true;
		pol_ce = type_str[11] == 'P';
		sig_ce = cell->getPort(ID::E);
	} else if (type_str.substr(0, 9) == "$_SDFFCE_" && type_str.size() == 14) {
		is_fine = true;
		sig_d = cell->getPort(ID::D);
		has_clk = true;
		pol_clk = type_str[9] == 'P';
		sig_clk = cell->getPort(ID::C);
		has_srst = true;
		pol_srst = type_str[10] == 'P';
		sig_srst = cell->getPort(ID::R);
		val_srst = type_str[11] == '1' ? State::S1 : State::S0;
		has_ce = true;
		pol_ce = type_str[12] == 'P';
		sig_ce = cell->getPort(ID::E);
		ce_over_srst = true;
	} else if (type_str.substr(0, 9) == "$_DLATCH_" && type_str.size() == 11) {
		is_fine = true;
		has_aload = true;
		sig_ad = cell->getPort(ID::D);
		has_aload = true;
		pol_aload = type_str[9] == 'P';
		sig_aload = cell->getPort(ID::E);
	} else if (type_str.substr(0, 9) == "$_DLATCH_" && type_str.size() == 13) {
		is_fine = true;
		has_aload = true;
		sig_ad = cell->getPort(ID::D);
		has_aload = true;
		pol_aload = type_str[9] == 'P';
		sig_aload = cell->getPort(ID::E);
		has_arst = true;
		pol_arst = type_str[10] == 'P';
		sig_arst = cell->getPort(ID::R);
		val_arst = type_str[11] == '1' ? State::S1 : State::S0;
	} else if (type_str.substr(0, 11) == "$_DLATCHSR_" && type_str.size() == 15) {
		is_fine = true;
		has_aload = true;
		sig_ad = cell->getPort(ID::D);
		has_aload = true;
		pol_aload = type_str[11] == 'P';
		sig_aload = cell->getPort(ID::E);
		has_sr = true;
		pol_set = type_str[12] == 'P';
		pol_clr = type_str[13] == 'P';
		sig_set = cell->getPort(ID::S);
		sig_clr = cell->getPort(ID::R);
	} else {
		log_assert(0);
	}
	if (has_aload && !has_clk && !has_sr && !has_arst && sig_ad.is_fully_const()) {
		// Plain D latches with const D treated specially.
		has_aload = false;
		has_arst = true;
		sig_arst = sig_aload;
		pol_arst = pol_aload;
		val_arst = sig_ad.as_const();
	}
}

FfData FfData::slice(const std::vector<int> &bits) {
	FfData res(module, initvals, NEW_ID);
	res.sig_clk = sig_clk;
	res.sig_ce = sig_ce;
	res.sig_aload = sig_aload;
	res.sig_arst = sig_arst;
	res.sig_srst = sig_srst;
	res.has_clk = has_clk;
	res.has_gclk = has_gclk;
	res.has_ce = has_ce;
	res.has_aload = has_aload;
	res.has_arst = has_arst;
	res.has_srst = has_srst;
	res.has_sr = has_sr;
	res.ce_over_srst = ce_over_srst;
	res.is_fine = is_fine;
	res.pol_clk = pol_clk;
	res.pol_ce = pol_ce;
	res.pol_aload = pol_aload;
	res.pol_arst = pol_arst;
	res.pol_srst = pol_srst;
	res.pol_clr = pol_clr;
	res.pol_set = pol_set;
	res.attributes = attributes;
	for (int i : bits) {
		res.sig_q.append(sig_q[i]);
		if (has_clk || has_gclk)
			res.sig_d.append(sig_d[i]);
		if (has_aload)
			res.sig_ad.append(sig_ad[i]);
		if (has_sr) {
			res.sig_clr.append(sig_clr[i]);
			res.sig_set.append(sig_set[i]);
		}
		if (has_arst)
			res.val_arst.bits.push_back(val_arst[i]);
		if (has_srst)
			res.val_srst.bits.push_back(val_srst[i]);
		if (initvals)
			res.val_init.bits.push_back(val_init[i]);
	}
	res.width = GetSize(res.sig_q);
	return res;
}

void FfData::unmap_ce() {
	if (!has_ce)
		return;
	log_assert(has_clk);
	if (has_srst && ce_over_srst)
		unmap_srst();

	if (!is_fine) {
		if (pol_ce)
			sig_d = module->Mux(NEW_ID, sig_q, sig_d, sig_ce);
		else
			sig_d = module->Mux(NEW_ID, sig_d, sig_q, sig_ce);
	} else {
		if (pol_ce)
			sig_d = module->MuxGate(NEW_ID, sig_q, sig_d, sig_ce);
		else
			sig_d = module->MuxGate(NEW_ID, sig_d, sig_q, sig_ce);
	}
	has_ce = false;
}

void FfData::unmap_srst() {
	if (!has_srst)
		return;
	if (has_ce && !ce_over_srst)
		unmap_ce();

	if (!is_fine) {
		if (pol_srst)
			sig_d = module->Mux(NEW_ID, sig_d, val_srst, sig_srst);
		else
			sig_d = module->Mux(NEW_ID, val_srst, sig_d, sig_srst);
	} else {
		if (pol_srst)
			sig_d = module->MuxGate(NEW_ID, sig_d, val_srst[0], sig_srst);
		else
			sig_d = module->MuxGate(NEW_ID, val_srst[0], sig_d, sig_srst);
	}
	has_srst = false;
}

Cell *FfData::emit() {
	remove();
	if (!width)
		return nullptr;
	if (!has_aload && !has_clk && !has_gclk && !has_sr) {
		if (has_arst) {
			// Convert this case to a D latch.
			has_aload = true;
			has_arst = false;
			sig_ad = val_arst;
			sig_aload = sig_arst;
			pol_aload = pol_arst;
		} else {
			// No control inputs left.  Turn into a const driver.
			module->connect(sig_q, val_init);
			return nullptr;
		}
	}
	if (initvals)
		initvals->set_init(sig_q, val_init);
	if (!is_fine) {
		if (has_gclk) {
			log_assert(!has_clk);
			log_assert(!has_ce);
			log_assert(!has_aload);
			log_assert(!has_arst);
			log_assert(!has_srst);
			log_assert(!has_sr);
			cell = module->addFf(name, sig_d, sig_q);
		} else if (!has_aload && !has_clk) {
			log_assert(has_sr);
			cell = module->addSr(name, sig_set, sig_clr, sig_q, pol_set, pol_clr);
		} else if (!has_clk) {
			log_assert(!has_srst);
			if (has_sr)
				cell = module->addDlatchsr(name, sig_aload, sig_set, sig_clr, sig_ad, sig_q, pol_aload, pol_set, pol_clr);
			else if (has_arst)
				cell = module->addAdlatch(name, sig_aload, sig_arst, sig_ad, sig_q, val_arst, pol_aload, pol_arst);
			else
				cell = module->addDlatch(name, sig_aload, sig_ad, sig_q, pol_aload);
		} else {
			if (has_sr) {
				if (has_ce)
					cell = module->addDffsre(name, sig_clk, sig_ce, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_ce, pol_set, pol_clr);
				else
					cell = module->addDffsr(name, sig_clk, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_set, pol_clr);
			} else if (has_arst) {
				if (has_ce)
					cell = module->addAdffe(name, sig_clk, sig_ce, sig_arst, sig_d, sig_q, val_arst, pol_clk, pol_ce, pol_arst);
				else
					cell = module->addAdff(name, sig_clk, sig_arst, sig_d, sig_q, val_arst, pol_clk, pol_arst);
			} else if (has_aload) {
				if (has_ce)
					cell = module->addAldffe(name, sig_clk, sig_ce, sig_aload, sig_d, sig_q, sig_ad, pol_clk, pol_ce, pol_aload);
				else
					cell = module->addAldff(name, sig_clk, sig_aload, sig_d, sig_q, sig_ad, pol_clk, pol_aload);
			} else if (has_srst) {
				if (has_ce)
					if (ce_over_srst)
						cell = module->addSdffce(name, sig_clk, sig_ce, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_ce, pol_srst);
					else
						cell = module->addSdffe(name, sig_clk, sig_ce, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_ce, pol_srst);
				else
					cell = module->addSdff(name, sig_clk, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_srst);
			} else {
				if (has_ce)
					cell = module->addDffe(name, sig_clk, sig_ce, sig_d, sig_q, pol_clk, pol_ce);
				else
					cell = module->addDff(name, sig_clk, sig_d, sig_q, pol_clk);
			}
		}
	} else {
		if (has_gclk) {
			log_assert(!has_clk);
			log_assert(!has_ce);
			log_assert(!has_aload);
			log_assert(!has_arst);
			log_assert(!has_srst);
			log_assert(!has_sr);
			cell = module->addFfGate(name, sig_d, sig_q);
		} else if (!has_aload && !has_clk) {
			log_assert(has_sr);
			cell = module->addSrGate(name, sig_set, sig_clr, sig_q, pol_set, pol_clr);
		} else if (!has_clk) {
			log_assert(!has_srst);
			if (has_sr)
				cell = module->addDlatchsrGate(name, sig_aload, sig_set, sig_clr, sig_ad, sig_q, pol_aload, pol_set, pol_clr);
			else if (has_arst)
				cell = module->addAdlatchGate(name, sig_aload, sig_arst, sig_ad, sig_q, val_arst.as_bool(), pol_aload, pol_arst);
			else
				cell = module->addDlatchGate(name, sig_aload, sig_ad, sig_q, pol_aload);
		} else {
			if (has_sr) {
				if (has_ce)
					cell = module->addDffsreGate(name, sig_clk, sig_ce, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_ce, pol_set, pol_clr);
				else
					cell = module->addDffsrGate(name, sig_clk, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_set, pol_clr);
			} else if (has_arst) {
				if (has_ce)
					cell = module->addAdffeGate(name, sig_clk, sig_ce, sig_arst, sig_d, sig_q, val_arst.as_bool(), pol_clk, pol_ce, pol_arst);
				else
					cell = module->addAdffGate(name, sig_clk, sig_arst, sig_d, sig_q, val_arst.as_bool(), pol_clk, pol_arst);
			} else if (has_aload) {
				if (has_ce)
					cell = module->addAldffeGate(name, sig_clk, sig_ce, sig_aload, sig_d, sig_q, sig_ad, pol_clk, pol_ce, pol_aload);
				else
					cell = module->addAldffGate(name, sig_clk, sig_aload, sig_d, sig_q, sig_ad, pol_clk, pol_aload);
			} else if (has_srst) {
				if (has_ce)
					if (ce_over_srst)
						cell = module->addSdffceGate(name, sig_clk, sig_ce, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_ce, pol_srst);
					else
						cell = module->addSdffeGate(name, sig_clk, sig_ce, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_ce, pol_srst);
				else
					cell = module->addSdffGate(name, sig_clk, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_srst);
			} else {
				if (has_ce)
					cell = module->addDffeGate(name, sig_clk, sig_ce, sig_d, sig_q, pol_clk, pol_ce);
				else
					cell = module->addDffGate(name, sig_clk, sig_d, sig_q, pol_clk);
			}
		}
	}
	cell->attributes = attributes;
	return cell;
}

void FfData::remove() {
	if (cell) {
		remove_init();
		module->remove(cell);
		cell = nullptr;
	}
}

namespace {
	State invert(State s) {
		switch (s) {
			case State::S0: return State::S1;
			case State::S1: return State::S0;
			default: return s;
		}
	}
}

void FfData::flip_bits(const pool<int> &bits) {
	if (!bits.size())
		return;

	remove_init();

	Wire *new_q = module->addWire(NEW_ID, width);

	for (auto bit: bits) {
		if (has_arst)
			val_arst[bit] = invert(val_arst[bit]);
		if (has_srst)
			val_srst[bit] = invert(val_srst[bit]);
		val_init[bit] = invert(val_init[bit]);
	}

	if (has_sr && cell) {
		log_warning("Flipping D/Q/init and inserting priority fixup to legalize %s.%s [%s].", log_id(module->name), log_id(cell->name), log_id(cell->type));
	}

	if (is_fine) {
		if (has_sr) {
			bool new_pol_clr = pol_set;
			SigSpec new_sig_clr;
			if (pol_set) {
				if (pol_clr) {
					new_sig_clr = module->AndnotGate(NEW_ID, sig_set, sig_clr);
				} else {
					new_sig_clr = module->AndGate(NEW_ID, sig_set, sig_clr);
				}
			} else {
				if (pol_clr) {
					new_sig_clr = module->OrGate(NEW_ID, sig_set, sig_clr);
				} else {
					new_sig_clr = module->OrnotGate(NEW_ID, sig_set, sig_clr);
				}
			}
			pol_set = pol_clr;
			sig_set = sig_clr;
			pol_clr = new_pol_clr;
			sig_clr = new_sig_clr;
		}
		if (has_clk || has_gclk)
			sig_d = module->NotGate(NEW_ID, sig_d);
		if (has_aload)
			sig_ad = module->NotGate(NEW_ID, sig_ad);
		module->addNotGate(NEW_ID, new_q, sig_q);
	}
	else
	{
		if (has_sr) {
			SigSpec not_clr;
			if (!pol_clr) {
				not_clr = sig_clr;
				sig_clr = module->Not(NEW_ID, sig_clr);
				pol_clr = true;
			} else {
				not_clr = module->Not(NEW_ID, sig_clr);
			}
			if (!pol_set) {
				sig_set = module->Not(NEW_ID, sig_set);
				pol_set = true;
			}

			SigSpec masked_set = module->And(NEW_ID, sig_set, not_clr);
			for (auto bit: bits) {
				sig_set[bit] = sig_clr[bit];
				sig_clr[bit] = masked_set[bit];
			}
		}

		Const mask = Const(State::S0, width);
		for (auto bit: bits)
			mask.bits[bit] = State::S1;

		if (has_clk || has_gclk)
			sig_d = module->Xor(NEW_ID, sig_d, mask);
		if (has_aload)
			sig_ad = module->Xor(NEW_ID, sig_ad, mask);
		module->addXor(NEW_ID, new_q, mask, sig_q);
	}

	sig_q = new_q;
}
