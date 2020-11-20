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

struct FfData {
	FfInitVals *initvals;
	SigSpec sig_q;
	SigSpec sig_d;
	SigSpec sig_clk;
	SigSpec sig_en;
	SigSpec sig_arst;
	SigSpec sig_srst;
	SigSpec sig_clr;
	SigSpec sig_set;
	bool has_d;
	bool has_clk;
	bool has_en;
	bool has_srst;
	bool has_arst;
	bool has_sr;
	bool ce_over_srst;
	bool is_fine;
	bool pol_clk;
	bool pol_en;
	bool pol_arst;
	bool pol_srst;
	bool pol_clr;
	bool pol_set;
	Const val_arst;
	Const val_srst;
	Const val_init;
	Const val_d;
	bool d_is_const;
	int width;
	dict<IdString, Const> attributes;

	FfData(FfInitVals *initvals, Cell *cell = nullptr) : initvals(initvals) {
		width = 0;
		has_d = true;
		has_clk = false;
		has_en = false;
		has_srst = false;
		has_arst = false;
		has_sr = false;
		ce_over_srst = false;
		is_fine = false;
		pol_clk = false;
		pol_en = false;
		pol_arst = false;
		pol_srst = false;
		pol_clr = false;
		pol_set = false;
		d_is_const = false;

		if (!cell)
			return;

		sig_q = cell->getPort(ID::Q);
		width = GetSize(sig_q);
		attributes = cell->attributes;

		if (initvals)
			val_init = (*initvals)(sig_q);

		std::string type_str = cell->type.str();

		if (cell->type.in(ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($dffsre), ID($adff), ID($adffe), ID($sdff), ID($sdffe), ID($sdffce), ID($dlatch), ID($adlatch), ID($dlatchsr), ID($sr))) {
			if (cell->type == ID($sr)) {
				has_d = false;
			} else {
				sig_d = cell->getPort(ID::D);
			}
			if (!cell->type.in(ID($ff), ID($dlatch), ID($adlatch), ID($dlatchsr), ID($sr))) {
				has_clk = true;
				sig_clk = cell->getPort(ID::CLK);
				pol_clk = cell->getParam(ID::CLK_POLARITY).as_bool();
			}
			if (cell->type.in(ID($dffe), ID($dffsre), ID($adffe), ID($sdffe), ID($sdffce), ID($dlatch), ID($adlatch), ID($dlatchsr))) {
				has_en = true;
				sig_en = cell->getPort(ID::EN);
				pol_en = cell->getParam(ID::EN_POLARITY).as_bool();
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
			sig_d = cell->getPort(ID::D);
		} else if (type_str.substr(0, 5) == "$_SR_") {
			is_fine = true;
			has_d = false;
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
			has_en = true;
			pol_en = type_str[8] == 'P';
			sig_en = cell->getPort(ID::E);
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
			has_en = true;
			pol_en = type_str[10] == 'P';
			sig_en = cell->getPort(ID::E);
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
			has_en = true;
			pol_en = type_str[12] == 'P';
			sig_en = cell->getPort(ID::E);
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
			has_en = true;
			pol_en = type_str[11] == 'P';
			sig_en = cell->getPort(ID::E);
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
			has_en = true;
			pol_en = type_str[12] == 'P';
			sig_en = cell->getPort(ID::E);
			ce_over_srst = true;
		} else if (type_str.substr(0, 9) == "$_DLATCH_" && type_str.size() == 11) {
			is_fine = true;
			sig_d = cell->getPort(ID::D);
			has_en = true;
			pol_en = type_str[9] == 'P';
			sig_en = cell->getPort(ID::E);
		} else if (type_str.substr(0, 9) == "$_DLATCH_" && type_str.size() == 13) {
			is_fine = true;
			sig_d = cell->getPort(ID::D);
			has_en = true;
			pol_en = type_str[9] == 'P';
			sig_en = cell->getPort(ID::E);
			has_arst = true;
			pol_arst = type_str[10] == 'P';
			sig_arst = cell->getPort(ID::R);
			val_arst = type_str[11] == '1' ? State::S1 : State::S0;
		} else if (type_str.substr(0, 11) == "$_DLATCHSR_" && type_str.size() == 15) {
			is_fine = true;
			sig_d = cell->getPort(ID::D);
			has_en = true;
			pol_en = type_str[11] == 'P';
			sig_en = cell->getPort(ID::E);
			has_sr = true;
			pol_set = type_str[12] == 'P';
			pol_clr = type_str[13] == 'P';
			sig_set = cell->getPort(ID::S);
			sig_clr = cell->getPort(ID::R);
		} else {
			log_assert(0);
		}
		if (has_d && sig_d.is_fully_const()) {
			d_is_const = true;
			val_d = sig_d.as_const();
			if (has_en && !has_clk && !has_sr && !has_arst) {
				// Plain D latches with const D treated specially.
				has_en = has_d = false;
				has_arst = true;
				sig_arst = sig_en;
				pol_arst = pol_en;
				val_arst = val_d;
			}
		}
	}

	// Returns a FF identical to this one, but only keeping bit indices from the argument.
	FfData slice(const std::vector<int> &bits) {
		FfData res(initvals);
		res.sig_clk = sig_clk;
		res.sig_en = sig_en;
		res.sig_arst = sig_arst;
		res.sig_srst = sig_srst;
		res.has_d = has_d;
		res.has_clk = has_clk;
		res.has_en = has_en;
		res.has_arst = has_arst;
		res.has_srst = has_srst;
		res.has_sr = has_sr;
		res.ce_over_srst = ce_over_srst;
		res.is_fine = is_fine;
		res.pol_clk = pol_clk;
		res.pol_en = pol_en;
		res.pol_arst = pol_arst;
		res.pol_srst = pol_srst;
		res.pol_clr = pol_clr;
		res.pol_set = pol_set;
		res.attributes = attributes;
		for (int i : bits) {
			res.sig_q.append(sig_q[i]);
			if (has_d)
				res.sig_d.append(sig_d[i]);
			if (has_sr) {
				res.sig_clr.append(sig_clr[i]);
				res.sig_set.append(sig_set[i]);
			}
			if (has_arst)
				res.val_arst.bits.push_back(val_arst[i]);
			if (has_srst)
				res.val_srst.bits.push_back(val_srst[i]);
			res.val_init.bits.push_back(val_init[i]);
		}
		res.width = GetSize(res.sig_q);
		// Slicing bits out may cause D to become const.
		if (has_d && res.sig_d.is_fully_const()) {
			res.d_is_const = true;
			res.val_d = res.sig_d.as_const();
		}
		return res;
	}

	void unmap_ce(Module *module) {
		if (!has_en)
			return;
		log_assert(has_clk);
		if (has_srst && ce_over_srst)
			unmap_srst(module);

		if (!is_fine) {
			if (pol_en)
				sig_d = module->Mux(NEW_ID, sig_q, sig_d, sig_en);
			else
				sig_d = module->Mux(NEW_ID, sig_d, sig_q, sig_en);
		} else {
			if (pol_en)
				sig_d = module->MuxGate(NEW_ID, sig_q, sig_d, sig_en);
			else
				sig_d = module->MuxGate(NEW_ID, sig_d, sig_q, sig_en);
		}
		has_en = false;
	}

	void unmap_srst(Module *module) {
		if (!has_srst)
			return;
		if (has_en && !ce_over_srst)
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
		if (!has_d && !has_sr) {
			if (has_arst) {
				// Convert this case to a D latch.
				has_d = has_en = true;
				has_arst = false;
				sig_d = val_arst;
				sig_en = sig_arst;
				pol_en = pol_arst;
			} else {
				// No control inputs left.  Turn into a const driver.
				initvals->remove_init(sig_q);
				module->connect(sig_q, val_init);
				return nullptr;
			}
		}
		initvals->set_init(sig_q, val_init);
		Cell *cell;
		if (!is_fine) {
			if (!has_d) {
				log_assert(has_sr);
				cell = module->addSr(name, sig_set, sig_clr, sig_q, pol_set, pol_clr);
			} else if (!has_clk && !has_en) {
				log_assert(!has_arst);
				log_assert(!has_srst);
				log_assert(!has_sr);
				cell = module->addFf(name, sig_d, sig_q);
			} else if (!has_clk) {
				log_assert(!has_srst);
				if (has_sr)
					cell = module->addDlatchsr(name, sig_en, sig_set, sig_clr, sig_d, sig_q, pol_en, pol_set, pol_clr);
				else if (has_arst)
					cell = module->addAdlatch(name, sig_en, sig_arst, sig_d, sig_q, val_arst, pol_en, pol_arst);
				else
					cell = module->addDlatch(name, sig_en, sig_d, sig_q, pol_en);
			} else {
				if (has_sr) {
					if (has_en)
						cell = module->addDffsre(name, sig_clk, sig_en, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_en, pol_set, pol_clr);
					else
						cell = module->addDffsr(name, sig_clk, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_set, pol_clr);
				} else if (has_arst) {
					if (has_en)
						cell = module->addAdffe(name, sig_clk, sig_en, sig_arst, sig_d, sig_q, val_arst, pol_clk, pol_en, pol_arst);
					else
						cell = module->addAdff(name, sig_clk, sig_arst, sig_d, sig_q, val_arst, pol_clk, pol_arst);
				} else if (has_srst) {
					if (has_en)
						if (ce_over_srst)
							cell = module->addSdffce(name, sig_clk, sig_en, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_en, pol_srst);
						else
							cell = module->addSdffe(name, sig_clk, sig_en, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_en, pol_srst);
					else
						cell = module->addSdff(name, sig_clk, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_srst);
				} else {
					if (has_en)
						cell = module->addDffe(name, sig_clk, sig_en, sig_d, sig_q, pol_clk, pol_en);
					else
						cell = module->addDff(name, sig_clk, sig_d, sig_q, pol_clk);
				}
			}
		} else {
			if (!has_d) {
				log_assert(has_sr);
				cell = module->addSrGate(name, sig_set, sig_clr, sig_q, pol_set, pol_clr);
			} else if (!has_clk && !has_en) {
				log_assert(!has_arst);
				log_assert(!has_srst);
				log_assert(!has_sr);
				cell = module->addFfGate(name, sig_d, sig_q);
			} else if (!has_clk) {
				log_assert(!has_srst);
				if (has_sr)
					cell = module->addDlatchsrGate(name, sig_en, sig_set, sig_clr, sig_d, sig_q, pol_en, pol_set, pol_clr);
				else if (has_arst)
					cell = module->addAdlatchGate(name, sig_en, sig_arst, sig_d, sig_q, val_arst.as_bool(), pol_en, pol_arst);
				else
					cell = module->addDlatchGate(name, sig_en, sig_d, sig_q, pol_en);
			} else {
				if (has_sr) {
					if (has_en)
						cell = module->addDffsreGate(name, sig_clk, sig_en, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_en, pol_set, pol_clr);
					else
						cell = module->addDffsrGate(name, sig_clk, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_set, pol_clr);
				} else if (has_arst) {
					if (has_en)
						cell = module->addAdffeGate(name, sig_clk, sig_en, sig_arst, sig_d, sig_q, val_arst.as_bool(), pol_clk, pol_en, pol_arst);
					else
						cell = module->addAdffGate(name, sig_clk, sig_arst, sig_d, sig_q, val_arst.as_bool(), pol_clk, pol_arst);
				} else if (has_srst) {
					if (has_en)
						if (ce_over_srst)
							cell = module->addSdffceGate(name, sig_clk, sig_en, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_en, pol_srst);
						else
							cell = module->addSdffeGate(name, sig_clk, sig_en, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_en, pol_srst);
					else
						cell = module->addSdffGate(name, sig_clk, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_srst);
				} else {
					if (has_en)
						cell = module->addDffeGate(name, sig_clk, sig_en, sig_d, sig_q, pol_clk, pol_en);
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
