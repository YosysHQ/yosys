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
#include "kernel/unstable/patch.h"

USING_YOSYS_NAMESPACE

// sorry
template<typename InputType, typename OutputType, typename = std::enable_if_t<std::is_base_of_v<FfTypeData, OutputType>>>
void manufacture_info(InputType flop, OutputType& info, FfInitVals *initvals) {
	Cell* cell = nullptr;
	TwineRef type;
	constexpr bool have_cell = std::is_same_v<InputType, Cell*>;
	if constexpr (std::is_same_v<InputType, TwineRef>) {
		type = flop;
	} else {
		static_assert(std::is_same_v<InputType, Cell*>);
		cell = flop;
		type = flop->type.ref();
	}
	if constexpr (have_cell) {
		info.sig_q = cell->getPort(TW::Q);
		info.width = GetSize(info.sig_q);
		info.attributes = cell->attributes;
		if (cell->src_id() != Twine::Null && cell->module && cell->module->design)
			info.src_twine = cell->src_id();
		if (initvals)
			info.val_init = (*initvals)(info.sig_q);
	}


	std::string type_str = TW::str(type);

	if (type.in(TW($anyinit), TW($ff), TW($dff), TW($dffe), TW($dffsr), TW($dffsre), TW($adff), TW($adffe), TW($aldff), TW($aldffe), TW($sdff), TW($sdffe), TW($sdffce), TW($dlatch), TW($adlatch), TW($dlatchsr), TW($sr))) {
		if (type.in(TW($anyinit), TW($ff))) {
			info.has_gclk = true;
			if constexpr (have_cell)
				info.sig_d = cell->getPort(TW::D);
			if (type == TW($anyinit)) {
				info.is_anyinit = true;
				if constexpr (have_cell)
					log_assert(info.val_init.is_fully_undef());
			}
		} else if (type == TW($sr)) {
			// No data input at all.
		} else if (type.in(TW($dlatch), TW($adlatch), TW($dlatchsr))) {
			info.has_aload = true;
			if constexpr (have_cell) {
				info.sig_aload = cell->getPort(TW::EN);
				info.pol_aload = cell->getParam(ID::EN_POLARITY).as_bool();
				info.sig_ad = cell->getPort(TW::D);
			}
		} else {
			info.has_clk = true;
			if constexpr (have_cell) {
				info.sig_clk = cell->getPort(TW::CLK);
				info.pol_clk = cell->getParam(ID::CLK_POLARITY).as_bool();
				info.sig_d = cell->getPort(TW::D);
			}
		}
		if (type.in(TW($dffe), TW($dffsre), TW($adffe), TW($aldffe), TW($sdffe), TW($sdffce))) {
			info.has_ce = true;
			if constexpr (have_cell) {
				info.sig_ce = cell->getPort(TW::EN);
				info.pol_ce = cell->getParam(ID::EN_POLARITY).as_bool();
			}
		}
		if (type.in(TW($dffsr), TW($dffsre), TW($dlatchsr), TW($sr))) {
			info.has_sr = true;
			if constexpr (have_cell) {
				info.sig_clr = cell->getPort(TW::CLR);
				info.sig_set = cell->getPort(TW::SET);
				info.pol_clr = cell->getParam(ID::CLR_POLARITY).as_bool();
				info.pol_set = cell->getParam(ID::SET_POLARITY).as_bool();
			}
		}
		if (type.in(TW($aldff), TW($aldffe))) {
			info.has_aload = true;
			if constexpr (have_cell) {
				info.sig_aload = cell->getPort(TW::ALOAD);
				info.pol_aload = cell->getParam(ID::ALOAD_POLARITY).as_bool();
				info.sig_ad = cell->getPort(TW::AD);
			}
		}
		if (type.in(TW($adff), TW($adffe), TW($adlatch))) {
			info.has_arst = true;
			if constexpr (have_cell) {
				info.sig_arst = cell->getPort(TW::ARST);
				info.pol_arst = cell->getParam(ID::ARST_POLARITY).as_bool();
				info.val_arst = cell->getParam(ID::ARST_VALUE);
			}
		}
		if (type.in(TW($sdff), TW($sdffe), TW($sdffce))) {
			info.has_srst = true;
			if constexpr (have_cell) {
				info.sig_srst = cell->getPort(TW::SRST);
				info.pol_srst = cell->getParam(ID::SRST_POLARITY).as_bool();
				info.val_srst = cell->getParam(ID::SRST_VALUE);
			}
			info.ce_over_srst = type == TW($sdffce);
		}
	} else if (type == TW($_FF_)) {
		info.is_fine = true;
		info.has_gclk = true;
		if constexpr (have_cell)
			info.sig_d = cell->getPort(TW::D);
	} else if (type_str.substr(0, 5) == "$_SR_") {
		info.is_fine = true;
		info.has_sr = true;
		info.pol_set = type_str[5] == 'P';
		info.pol_clr = type_str[6] == 'P';
		if constexpr (have_cell) {
			info.sig_set = cell->getPort(TW::S);
			info.sig_clr = cell->getPort(TW::R);
		}
	} else if (type_str.substr(0, 6) == "$_DFF_" && type_str.size() == 8) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[6] == 'P';
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
		}
	} else if (type_str.substr(0, 7) == "$_DFFE_" && type_str.size() == 10) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[7] == 'P';
		info.has_ce = true;
		info.pol_ce = type_str[8] == 'P';
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_ce = cell->getPort(TW::E);
		}
	} else if (type_str.substr(0, 6) == "$_DFF_" && type_str.size() == 10) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[6] == 'P';
		info.has_arst = true;
		info.pol_arst = type_str[7] == 'P';
		info.val_arst = type_str[8] == '1' ? State::S1 : State::S0;
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_arst = cell->getPort(TW::R);
		}
	} else if (type_str.substr(0, 7) == "$_DFFE_" && type_str.size() == 12) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[7] == 'P';
		info.has_arst = true;
		info.pol_arst = type_str[8] == 'P';
		info.val_arst = type_str[9] == '1' ? State::S1 : State::S0;
		info.has_ce = true;
		info.pol_ce = type_str[10] == 'P';
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_arst = cell->getPort(TW::R);
			info.sig_ce = cell->getPort(TW::E);
		}
	} else if (type_str.substr(0, 8) == "$_ALDFF_" && type_str.size() == 11) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[8] == 'P';
		info.has_aload = true;
		info.pol_aload = type_str[9] == 'P';
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_aload = cell->getPort(TW::L);
			info.sig_ad = cell->getPort(TW::AD);
		}
	} else if (type_str.substr(0, 9) == "$_ALDFFE_" && type_str.size() == 13) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[9] == 'P';
		info.has_aload = true;
		info.pol_aload = type_str[10] == 'P';
		info.has_ce = true;
		info.pol_ce = type_str[11] == 'P';
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_aload = cell->getPort(TW::L);
			info.sig_ad = cell->getPort(TW::AD);
			info.sig_ce = cell->getPort(TW::E);
		}
	} else if (type_str.substr(0, 8) == "$_DFFSR_" && type_str.size() == 12) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[8] == 'P';
		info.has_sr = true;
		info.pol_set = type_str[9] == 'P';
		info.pol_clr = type_str[10] == 'P';
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_set = cell->getPort(TW::S);
			info.sig_clr = cell->getPort(TW::R);
		}
	} else if (type_str.substr(0, 9) == "$_DFFSRE_" && type_str.size() == 14) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[9] == 'P';
		info.has_sr = true;
		info.pol_set = type_str[10] == 'P';
		info.pol_clr = type_str[11] == 'P';
		info.has_ce = true;
		info.pol_ce = type_str[12] == 'P';
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_set = cell->getPort(TW::S);
			info.sig_clr = cell->getPort(TW::R);
			info.sig_ce = cell->getPort(TW::E);
		}
	} else if (type_str.substr(0, 7) == "$_SDFF_" && type_str.size() == 11) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[7] == 'P';
		info.has_srst = true;
		info.pol_srst = type_str[8] == 'P';
		info.val_srst = type_str[9] == '1' ? State::S1 : State::S0;
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_srst = cell->getPort(TW::R);
		}
	} else if (type_str.substr(0, 8) == "$_SDFFE_" && type_str.size() == 13) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[8] == 'P';
		info.has_srst = true;
		info.pol_srst = type_str[9] == 'P';
		info.val_srst = type_str[10] == '1' ? State::S1 : State::S0;
		info.has_ce = true;
		info.pol_ce = type_str[11] == 'P';
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_srst = cell->getPort(TW::R);
			info.sig_ce = cell->getPort(TW::E);
		}
	} else if (type_str.substr(0, 9) == "$_SDFFCE_" && type_str.size() == 14) {
		info.is_fine = true;
		info.has_clk = true;
		info.pol_clk = type_str[9] == 'P';
		info.has_srst = true;
		info.pol_srst = type_str[10] == 'P';
		info.val_srst = type_str[11] == '1' ? State::S1 : State::S0;
		info.has_ce = true;
		info.pol_ce = type_str[12] == 'P';
		info.ce_over_srst = true;
		if constexpr (have_cell) {
			info.sig_d = cell->getPort(TW::D);
			info.sig_clk = cell->getPort(TW::C);
			info.sig_srst = cell->getPort(TW::R);
			info.sig_ce = cell->getPort(TW::E);
		}
	} else if (type_str.substr(0, 9) == "$_DLATCH_" && type_str.size() == 11) {
		info.is_fine = true;
		info.has_aload = true;
		info.has_aload = true;
		info.pol_aload = type_str[9] == 'P';
		if constexpr (have_cell) {
			info.sig_ad = cell->getPort(TW::D);
			info.sig_aload = cell->getPort(TW::E);
		}
	} else if (type_str.substr(0, 9) == "$_DLATCH_" && type_str.size() == 13) {
		info.is_fine = true;
		info.has_aload = true;
		info.has_aload = true;
		info.pol_aload = type_str[9] == 'P';
		info.has_arst = true;
		info.pol_arst = type_str[10] == 'P';
		info.val_arst = type_str[11] == '1' ? State::S1 : State::S0;
		if constexpr (have_cell) {
			info.sig_ad = cell->getPort(TW::D);
			info.sig_aload = cell->getPort(TW::E);
			info.sig_arst = cell->getPort(TW::R);
		}
	} else if (type_str.substr(0, 11) == "$_DLATCHSR_" && type_str.size() == 15) {
		info.is_fine = true;
		info.has_aload = true;
		info.has_aload = true;
		info.pol_aload = type_str[11] == 'P';
		info.has_sr = true;
		info.pol_set = type_str[12] == 'P';
		info.pol_clr = type_str[13] == 'P';
		if constexpr (have_cell) {
			info.sig_ad = cell->getPort(TW::D);
			info.sig_aload = cell->getPort(TW::E);
			info.sig_set = cell->getPort(TW::S);
			info.sig_clr = cell->getPort(TW::R);
		}
	} else {
		log_assert(0);
	}
	if constexpr (have_cell)
		if (info.has_aload && !info.has_clk && !info.has_sr && !info.has_arst && info.sig_ad.is_fully_const()) {
			// Plain D latches with const D treated specially.
			info.has_aload = false;
			info.has_arst = true;
			info.sig_arst = info.sig_aload;
			info.pol_arst = info.pol_aload;
			info.val_arst = info.sig_ad.as_const();
		}
}

FfTypeData::FfTypeData(TwineRef type) : FfTypeData()
{
	manufacture_info(type, *this, nullptr);
}

FfData::FfData(FfInitVals *initvals, Cell *cell_) : FfData(cell_->module, initvals, cell_->name)
{
	cell = cell_;
	manufacture_info(cell, *this, initvals);
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
	res.is_anyinit = is_anyinit;
	res.pol_clk = pol_clk;
	res.pol_ce = pol_ce;
	res.pol_aload = pol_aload;
	res.pol_arst = pol_arst;
	res.pol_srst = pol_srst;
	res.pol_clr = pol_clr;
	res.pol_set = pol_set;
	res.attributes = attributes;
	res.src_twine = src_twine;
	std::optional<Const::Builder> arst_bits;
	if (has_arst)
		arst_bits.emplace(bits.size());
	std::optional<Const::Builder> srst_bits;
	if (has_srst)
		srst_bits.emplace(bits.size());
	std::optional<Const::Builder> init_bits;
	if (initvals)
		init_bits.emplace(bits.size());

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
			arst_bits->push_back(val_arst[i]);
		if (has_srst)
			srst_bits->push_back(val_srst[i]);
		if (initvals)
			init_bits->push_back(val_init[i]);
	}

	if (has_arst)
		res.val_arst = arst_bits->build();
	if (has_srst)
		res.val_srst = srst_bits->build();
	if (initvals)
		res.val_init = init_bits->build();
	res.width = GetSize(res.sig_q);
	return res;
}

void FfData::add_dummy_ce() {
	if (has_ce)
		return;
	has_ce = true;
	pol_ce = true;
	sig_ce = State::S1;
	ce_over_srst = false;
}

void FfData::add_dummy_srst() {
	if (has_srst)
		return;
	has_srst = true;
	pol_srst = true;
	sig_srst = State::S0;
	val_srst = Const(State::Sx, width);
	ce_over_srst = false;
}

void FfData::add_dummy_arst() {
	if (has_arst)
		return;
	has_arst = true;
	pol_arst = true;
	sig_arst = State::S0;
	val_arst = Const(State::Sx, width);
}

void FfData::add_dummy_aload() {
	if (has_aload)
		return;
	has_aload = true;
	pol_aload = true;
	sig_aload = State::S0;
	sig_ad = Const(State::Sx, width);
}

void FfData::add_dummy_sr() {
	if (has_sr)
		return;
	has_sr = true;
	pol_clr = true;
	pol_set = true;
	sig_clr = Const(State::S0, width);
	sig_set = Const(State::S0, width);
}

void FfData::add_dummy_clk() {
	if (has_clk)
		return;
	has_clk = true;
	pol_clk = true;
	sig_clk = State::S0;
	sig_d = Const(State::Sx, width);
}

void FfData::arst_to_aload() {
	log_assert(has_arst);
	log_assert(!has_aload);
	pol_aload = pol_arst;
	sig_aload = sig_arst;
	sig_ad = val_arst;
	has_aload = true;
	has_arst = false;
}

void FfData::arst_to_sr() {
	log_assert(has_arst);
	log_assert(!has_sr);
	pol_clr = pol_arst;
	pol_set = pol_arst;
	sig_clr = Const(pol_arst ? State::S0 : State::S1, width);
	sig_set = Const(pol_arst ? State::S0 : State::S1, width);
	has_sr = true;
	has_arst = false;
	for (int i = 0; i < width; i++) {
		if (val_arst[i] == State::S1)
			sig_set[i] = sig_arst;
		else
			sig_clr[i] = sig_arst;
	}
}

void FfData::aload_to_sr() {
	log_assert(has_aload);
	log_assert(!has_sr);
	has_sr = true;
	has_aload = false;
	RTLIL::Patch patcher(module);
	if (!is_fine) {
		pol_clr = false;
		pol_set = true;
		if (pol_aload) {
			sig_clr = patcher.Mux(NEW_TWINE, Const(State::S1, width), sig_ad, sig_aload);
			sig_set = patcher.Mux(NEW_TWINE, Const(State::S0, width), sig_ad, sig_aload);
		} else {
			sig_clr = patcher.Mux(NEW_TWINE, sig_ad, Const(State::S1, width), sig_aload);
			sig_set = patcher.Mux(NEW_TWINE, sig_ad, Const(State::S0, width), sig_aload);
		}
	} else {
		pol_clr = pol_aload;
		pol_set = pol_aload;
		if (pol_aload) {
			sig_clr = patcher.AndnotGate(NEW_TWINE, sig_aload, sig_ad);
			sig_set = patcher.AndGate(NEW_TWINE, sig_aload, sig_ad);
		} else {
			sig_clr = patcher.OrGate(NEW_TWINE, sig_aload, sig_ad);
			sig_set = patcher.OrnotGate(NEW_TWINE, sig_aload, sig_ad);
		}
	}
	patcher.commit_inheriting_src(cell);
}

void FfData::convert_ce_over_srst(bool val) {
	if (!has_ce || !has_srst || ce_over_srst == val)
		return;
	RTLIL::Patch patcher(module);
	if (val) {
		// sdffe to sdffce
		if (!is_fine) {
			if (pol_ce) {
				if (pol_srst) {
					sig_ce = patcher.Or(NEW_TWINE, sig_ce, sig_srst);
				} else {
					SigSpec tmp = patcher.Not(NEW_TWINE, sig_srst);
					sig_ce = patcher.Or(NEW_TWINE, sig_ce, tmp);
				}
			} else {
				if (pol_srst) {
					SigSpec tmp = patcher.Not(NEW_TWINE, sig_srst);
					sig_ce = patcher.And(NEW_TWINE, sig_ce, tmp);
				} else {
					sig_ce = patcher.And(NEW_TWINE, sig_ce, sig_srst);
				}
			}
		} else {
			if (pol_ce) {
				if (pol_srst) {
					sig_ce = patcher.OrGate(NEW_TWINE, sig_ce, sig_srst);
				} else {
					sig_ce = patcher.OrnotGate(NEW_TWINE, sig_ce, sig_srst);
				}
			} else {
				if (pol_srst) {
					sig_ce = patcher.AndnotGate(NEW_TWINE, sig_ce, sig_srst);
				} else {
					sig_ce = patcher.AndGate(NEW_TWINE, sig_ce, sig_srst);
				}
			}
		}
	} else {
		// sdffce to sdffe
		if (!is_fine) {
			if (pol_srst) {
				if (pol_ce) {
					sig_srst = patcher.And(NEW_TWINE, sig_srst, sig_ce);
				} else {
					SigSpec tmp = patcher.Not(NEW_TWINE, sig_ce);
					sig_srst = patcher.And(NEW_TWINE, sig_srst, tmp);
				}
			} else {
				if (pol_ce) {
					SigSpec tmp = patcher.Not(NEW_TWINE, sig_ce);
					sig_srst = patcher.Or(NEW_TWINE, sig_srst, tmp);
				} else {
					sig_srst = patcher.Or(NEW_TWINE, sig_srst, sig_ce);
				}
			}
		} else {
			if (pol_srst) {
				if (pol_ce) {
					sig_srst = patcher.AndGate(NEW_TWINE, sig_srst, sig_ce);
				} else {
					sig_srst = patcher.AndnotGate(NEW_TWINE, sig_srst, sig_ce);
				}
			} else {
				if (pol_ce) {
					sig_srst = patcher.OrnotGate(NEW_TWINE, sig_srst, sig_ce);
				} else {
					sig_srst = patcher.OrGate(NEW_TWINE, sig_srst, sig_ce);
				}
			}
		}
	}
	patcher.commit_inheriting_src(cell);
	ce_over_srst = val;
}

void FfData::unmap_ce() {
	if (!has_ce)
		return;
	log_assert(has_clk);
	if (has_srst && ce_over_srst)
		unmap_srst();

	RTLIL::Patch patcher(module);
	if (!is_fine) {
		if (pol_ce)
			sig_d = patcher.Mux(NEW_TWINE, sig_q, sig_d, sig_ce);
		else
			sig_d = patcher.Mux(NEW_TWINE, sig_d, sig_q, sig_ce);
	} else {
		if (pol_ce)
			sig_d = patcher.MuxGate(NEW_TWINE, sig_q, sig_d, sig_ce);
		else
			sig_d = patcher.MuxGate(NEW_TWINE, sig_d, sig_q, sig_ce);
	}
	patcher.commit_inheriting_src(cell);
	has_ce = false;
}

void FfData::unmap_srst() {
	if (!has_srst)
		return;
	if (has_ce && !ce_over_srst)
		unmap_ce();

	RTLIL::Patch patcher(module);
	if (!is_fine) {
		if (pol_srst)
			sig_d = patcher.Mux(NEW_TWINE, sig_d, val_srst, sig_srst);
		else
			sig_d = patcher.Mux(NEW_TWINE, val_srst, sig_d, sig_srst);
	} else {
		if (pol_srst)
			sig_d = patcher.MuxGate(NEW_TWINE, sig_d, val_srst[0], sig_srst);
		else
			sig_d = patcher.MuxGate(NEW_TWINE, val_srst[0], sig_d, sig_srst);
	}
	patcher.commit_inheriting_src(cell);
	has_srst = false;
}

Cell *FfData::emit() {
	remove();
	if (!width)
		return nullptr;
	if (!has_aload && !has_clk && !has_gclk && !has_sr) {
		if (has_arst) {
			// Convert this case to a D latch.
			arst_to_aload();
		} else {
			// No control inputs left.  Turn into a const driver.
			module->connect(sig_q, val_init);
			return nullptr;
		}
	}
	if (!is_fine) {
		if (has_gclk) {
			log_assert(!has_clk);
			log_assert(!has_ce);
			log_assert(!has_aload);
			log_assert(!has_arst);
			log_assert(!has_srst);
			log_assert(!has_sr);
			if (is_anyinit) {
				cell = module->addAnyinit(Twine{name.str()}, sig_d, sig_q);
				log_assert(val_init.is_fully_undef());
			} else {
				cell = module->addFf(Twine{name.str()}, sig_d, sig_q);
			}
		} else if (!has_aload && !has_clk) {
			log_assert(has_sr);
			cell = module->addSr(Twine{name.str()}, sig_set, sig_clr, sig_q, pol_set, pol_clr);
		} else if (!has_clk) {
			log_assert(!has_srst);
			if (has_sr)
				cell = module->addDlatchsr(Twine{name.str()}, sig_aload, sig_set, sig_clr, sig_ad, sig_q, pol_aload, pol_set, pol_clr);
			else if (has_arst)
				cell = module->addAdlatch(Twine{name.str()}, sig_aload, sig_arst, sig_ad, sig_q, val_arst, pol_aload, pol_arst);
			else
				cell = module->addDlatch(Twine{name.str()}, sig_aload, sig_ad, sig_q, pol_aload);
		} else {
			if (has_sr) {
				if (has_ce)
					cell = module->addDffsre(Twine{name.str()}, sig_clk, sig_ce, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_ce, pol_set, pol_clr);
				else
					cell = module->addDffsr(Twine{name.str()}, sig_clk, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_set, pol_clr);
			} else if (has_arst) {
				if (has_ce)
					cell = module->addAdffe(Twine{name.str()}, sig_clk, sig_ce, sig_arst, sig_d, sig_q, val_arst, pol_clk, pol_ce, pol_arst);
				else
					cell = module->addAdff(Twine{name.str()}, sig_clk, sig_arst, sig_d, sig_q, val_arst, pol_clk, pol_arst);
			} else if (has_aload) {
				if (has_ce)
					cell = module->addAldffe(Twine{name.str()}, sig_clk, sig_ce, sig_aload, sig_d, sig_q, sig_ad, pol_clk, pol_ce, pol_aload);
				else
					cell = module->addAldff(Twine{name.str()}, sig_clk, sig_aload, sig_d, sig_q, sig_ad, pol_clk, pol_aload);
			} else if (has_srst) {
				if (has_ce)
					if (ce_over_srst)
						cell = module->addSdffce(Twine{name.str()}, sig_clk, sig_ce, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_ce, pol_srst);
					else
						cell = module->addSdffe(Twine{name.str()}, sig_clk, sig_ce, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_ce, pol_srst);
				else
					cell = module->addSdff(Twine{name.str()}, sig_clk, sig_srst, sig_d, sig_q, val_srst, pol_clk, pol_srst);
			} else {
				if (has_ce)
					cell = module->addDffe(Twine{name.str()}, sig_clk, sig_ce, sig_d, sig_q, pol_clk, pol_ce);
				else
					cell = module->addDff(Twine{name.str()}, sig_clk, sig_d, sig_q, pol_clk);
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
			log_assert(!is_anyinit);
			cell = module->addFfGate(Twine{name.str()}, sig_d, sig_q);
		} else if (!has_aload && !has_clk) {
			log_assert(has_sr);
			cell = module->addSrGate(Twine{name.str()}, sig_set, sig_clr, sig_q, pol_set, pol_clr);
		} else if (!has_clk) {
			log_assert(!has_srst);
			if (has_sr)
				cell = module->addDlatchsrGate(Twine{name.str()}, sig_aload, sig_set, sig_clr, sig_ad, sig_q, pol_aload, pol_set, pol_clr);
			else if (has_arst)
				cell = module->addAdlatchGate(Twine{name.str()}, sig_aload, sig_arst, sig_ad, sig_q, val_arst.as_bool(), pol_aload, pol_arst);
			else
				cell = module->addDlatchGate(Twine{name.str()}, sig_aload, sig_ad, sig_q, pol_aload);
		} else {
			if (has_sr) {
				if (has_ce)
					cell = module->addDffsreGate(Twine{name.str()}, sig_clk, sig_ce, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_ce, pol_set, pol_clr);
				else
					cell = module->addDffsrGate(Twine{name.str()}, sig_clk, sig_set, sig_clr, sig_d, sig_q, pol_clk, pol_set, pol_clr);
			} else if (has_arst) {
				if (has_ce)
					cell = module->addAdffeGate(Twine{name.str()}, sig_clk, sig_ce, sig_arst, sig_d, sig_q, val_arst.as_bool(), pol_clk, pol_ce, pol_arst);
				else
					cell = module->addAdffGate(Twine{name.str()}, sig_clk, sig_arst, sig_d, sig_q, val_arst.as_bool(), pol_clk, pol_arst);
			} else if (has_aload) {
				if (has_ce)
					cell = module->addAldffeGate(Twine{name.str()}, sig_clk, sig_ce, sig_aload, sig_d, sig_q, sig_ad, pol_clk, pol_ce, pol_aload);
				else
					cell = module->addAldffGate(Twine{name.str()}, sig_clk, sig_aload, sig_d, sig_q, sig_ad, pol_clk, pol_aload);
			} else if (has_srst) {
				if (has_ce)
					if (ce_over_srst)
						cell = module->addSdffceGate(Twine{name.str()}, sig_clk, sig_ce, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_ce, pol_srst);
					else
						cell = module->addSdffeGate(Twine{name.str()}, sig_clk, sig_ce, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_ce, pol_srst);
				else
					cell = module->addSdffGate(Twine{name.str()}, sig_clk, sig_srst, sig_d, sig_q, val_srst.as_bool(), pol_clk, pol_srst);
			} else {
				if (has_ce)
					cell = module->addDffeGate(Twine{name.str()}, sig_clk, sig_ce, sig_d, sig_q, pol_clk, pol_ce);
				else
					cell = module->addDffGate(Twine{name.str()}, sig_clk, sig_d, sig_q, pol_clk);
			}
		}
	}
	// src is carried in info.src_twine (an OwnedTwine retaining the
	// pool, no flatten. The OwnedTwine still holds its own ref until
	// FfData is destroyed; set_src_id retains on the cell's behalf.
	cell->attributes = attributes;
	if (src_twine != Twine::Null && cell->module && cell->module->design)
		cell->set_src_id(src_twine);
	if (initvals && !is_anyinit)
		initvals->set_init(cell->getPort(TW::Q), val_init);
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

void FfData::flip_rst_bits(const pool<int> &bits) {
	if (!bits.size())
		return;

	remove_init();

	for (auto bit: bits) {
		if (has_arst)
			val_arst.set(bit, invert(val_arst[bit]));
		if (has_srst)
			val_srst.set(bit, invert(val_srst[bit]));
		val_init.set(bit, invert(val_init[bit]));
	}
}

void FfData::flip_bits(const pool<int> &bits) {
	if (!bits.size())
		return;

	flip_rst_bits(bits);

	Wire *new_q = module->addWire(NEW_TWINE, width);

	if (has_sr && cell) {
		log_warning("Flipping D/Q/init and inserting priority fixup to legalize %s.%s [%s].\n", module->design->twines.str(module->meta_->name).c_str(), cell->name, cell->type.unescape());
	}

	if (is_fine) {
		if (has_sr) {
			bool new_pol_clr = pol_set;
			SigSpec new_sig_clr;
			if (pol_set) {
				if (pol_clr) {
					new_sig_clr = module->AndnotGate(NEW_TWINE, sig_set, sig_clr);
				} else {
					new_sig_clr = module->AndGate(NEW_TWINE, sig_set, sig_clr);
				}
			} else {
				if (pol_clr) {
					new_sig_clr = module->OrGate(NEW_TWINE, sig_set, sig_clr);
				} else {
					new_sig_clr = module->OrnotGate(NEW_TWINE, sig_set, sig_clr);
				}
			}
			pol_set = pol_clr;
			sig_set = sig_clr;
			pol_clr = new_pol_clr;
			sig_clr = new_sig_clr;
		}
		if (has_clk || has_gclk)
			sig_d = module->NotGate(NEW_TWINE, sig_d);
		if (has_aload)
			sig_ad = module->NotGate(NEW_TWINE, sig_ad);
		module->addNotGate(NEW_TWINE, new_q, sig_q);
	}
	else
	{
		if (has_sr) {
			SigSpec not_clr;
			if (!pol_clr) {
				not_clr = sig_clr;
				sig_clr = module->Not(NEW_TWINE, sig_clr);
				pol_clr = true;
			} else {
				not_clr = module->Not(NEW_TWINE, sig_clr);
			}
			if (!pol_set) {
				sig_set = module->Not(NEW_TWINE, sig_set);
				pol_set = true;
			}

			SigSpec masked_set = module->And(NEW_TWINE, sig_set, not_clr);
			for (auto bit: bits) {
				sig_set[bit] = sig_clr[bit];
				sig_clr[bit] = masked_set[bit];
			}
		}

		Const mask = Const(State::S0, width);
		for (auto bit: bits)
			mask.set(bit, State::S1);

		if (has_clk || has_gclk)
			sig_d = module->Xor(NEW_TWINE, sig_d, mask);
		if (has_aload)
			sig_ad = module->Xor(NEW_TWINE, sig_ad, mask);
		module->addXor(NEW_TWINE, new_q, mask, sig_q);
	}

	sig_q = new_q;
}
