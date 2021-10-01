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

#ifndef FF_H
#define FF_H

#include "kernel/yosys.h"
#include "kernel/ffinit.h"

YOSYS_NAMESPACE_BEGIN

// Describes a flip-flop or a latch.
//
// If has_gclk, this is a formal verification FF with implicit global clock:
// Q is simply previous cycle's D.
//
// Otherwise, the FF/latch can have any number of features selected by has_*
// attributes that determine Q's value (in order of decreasing priority):
//
// - on start, register is initialized to val_init
// - if has_sr is present:
//   - sig_clr is per-bit async clear, and sets the corresponding bit to 0
//     if active
//   - sig_set is per-bit async set, and sets the corresponding bit to 1
//     if active
// - if has_arst is present:
//   - sig_arst is whole-reg async reset, and sets the whole register to val_arst
// - if has_aload is present:
//   - sig_aload is whole-reg async load (aka latch gate enable), and sets the whole
//     register to sig_ad
// - if has_clk is present, and we're currently on a clock edge:
//   - if has_ce is present and ce_over_srst is true:
//     - ignore clock edge (don't change value) unless sig_ce is active
//   - if has_srst is present:
//     - sig_srst is whole-reg sync reset and sets the register to val_srst
//   - if has_ce is present and ce_over_srst is false:
//     - ignore clock edge (don't change value) unless sig_ce is active
//   - set whole reg to sig_d
// - if nothing of the above applies, the reg value remains unchanged
//
// Since the yosys FF cell library isn't fully generic, not all combinations
// of the features above can be supported:
//
// - only one of has_srst, has_arst, has_sr can be used
// - if has_clk is used together with has_aload, then has_srst, has_arst,
//   has_sr cannot be used
//
// The valid feature combinations are thus:
//
// - has_clk + optional has_ce [dff/dffe]
// - has_clk + optional has_ce + has_arst [adff/adffe]
// - has_clk + optional has_ce + has_aload [aldff/aldffe]
// - has_clk + optional has_ce + has_sr [dffsr/dffsre]
// - has_clk + optional has_ce + has_srst [sdff/sdffe/sdffce]
// - has_aload [dlatch]
// - has_aload + has_arst [adlatch]
// - has_aload + has_sr [dlatchsr]
// - has_sr [sr]
// - has_arst [does not correspond to a native cell, represented as dlatch with const D input]
// - empty set [not a cell — will be emitted as a simple direct connection]

struct FfData {
	FfInitVals *initvals;
	// The FF output.
	SigSpec sig_q;
	// The sync data input, present if has_clk or has_gclk.
	SigSpec sig_d;
	// The async data input, present if has_aload.
	SigSpec sig_ad;
	// The sync clock, present if has_clk.
	SigSpec sig_clk;
	// The clock enable, present if has_ce.
	SigSpec sig_ce;
	// The async load enable, present if has_aload.
	SigSpec sig_aload;
	// The async reset, preset if has_arst.
	SigSpec sig_arst;
	// The sync reset, preset if has_srst.
	SigSpec sig_srst;
	// The async clear (per-lane), present if has_sr.
	SigSpec sig_clr;
	// The async set (per-lane), present if has_sr.
	SigSpec sig_set;
	// True if this is a clocked (edge-sensitive) flip-flop.
	bool has_clk;
	// True if this is a $ff, exclusive with every other has_*.
	bool has_gclk;
	// True if this FF has a clock enable.  Depends on has_clk.
	bool has_ce;
	// True if this FF has async load function — this includes D latches.
	// If this and has_clk are both set, has_arst and has_sr cannot be set.
	bool has_aload;
	// True if this FF has sync set/reset.  Depends on has_clk, exclusive
	// with has_arst, has_sr, has_aload.
	bool has_srst;
	// True if this FF has async set/reset.  Exclusive with has_srst,
	// has_sr.  If this and has_clk are both set, has_aload cannot be set.
	bool has_arst;
	// True if this FF has per-bit async set + clear.  Exclusive with
	// has_srst, has_arst.  If this and has_clk are both set, has_aload
	// cannot be set.
	bool has_sr;
	// If has_ce and has_srst are both set, determines their relative
	// priorities: if true, inactive ce disables srst; if false, srst
	// operates independent of ce.
	bool ce_over_srst;
	// True if this FF is a fine cell, false if it is a coarse cell.
	// If true, width must be 1.
	bool is_fine;
	// Polarities, corresponding to sig_*.  True means active-high, false
	// means active-low.
	bool pol_clk;
	bool pol_ce;
	bool pol_aload;
	bool pol_arst;
	bool pol_srst;
	bool pol_clr;
	bool pol_set;
	// The value loaded by sig_arst.
	Const val_arst;
	// The value loaded by sig_srst.
	Const val_srst;
	// The initial value at power-up.
	Const val_init;
	// The FF data width in bits.
	int width;
	dict<IdString, Const> attributes;

	FfData(FfInitVals *initvals = nullptr, Cell *cell = nullptr) : initvals(initvals) {
		width = 0;
		has_clk = false;
		has_gclk = false;
		has_ce = false;
		has_aload = false;
		has_srst = false;
		has_arst = false;
		has_sr = false;
		ce_over_srst = false;
		is_fine = false;
		pol_clk = false;
		pol_aload = false;
		pol_ce = false;
		pol_arst = false;
		pol_srst = false;
		pol_clr = false;
		pol_set = false;

		if (!cell)
			return;

		sig_q = cell->getPort(ID::Q);
		width = GetSize(sig_q);
		attributes = cell->attributes;

		if (initvals)
			val_init = (*initvals)(sig_q);

		std::string type_str = cell->type.str();

		if (cell->type.in(ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($dffsre), ID($adff), ID($adffe), ID($sdff), ID($sdffe), ID($sdffce), ID($dlatch), ID($adlatch), ID($dlatchsr), ID($sr))) {
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
			if (cell->type.in(ID($dffe), ID($dffsre), ID($adffe), ID($sdffe), ID($sdffce))) {
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

	// Returns a FF identical to this one, but only keeping bit indices from the argument.
	FfData slice(const std::vector<int> &bits) {
		FfData res(initvals);
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

	void unmap_ce(Module *module) {
		if (!has_ce)
			return;
		log_assert(has_clk);
		if (has_srst && ce_over_srst)
			unmap_srst(module);

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

	void unmap_srst(Module *module) {
		if (!has_srst)
			return;
		if (has_ce && !ce_over_srst)
			unmap_ce(module);

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

	void unmap_ce_srst(Module *module) {
		unmap_ce(module);
		unmap_srst(module);
	}

	Cell *emit(Module *module, IdString name) {
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
				if (initvals)
					initvals->remove_init(sig_q);
				module->connect(sig_q, val_init);
				return nullptr;
			}
		}
		if (initvals)
			initvals->set_init(sig_q, val_init);
		Cell *cell;
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
};

YOSYS_NAMESPACE_END

#endif
