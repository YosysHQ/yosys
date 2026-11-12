/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#ifndef VERIFIC_CLOCKING_H
#define VERIFIC_CLOCKING_H

#ifdef YOSYS_ENABLE_VERIFIC

#include "kernel/yosys.h"

#include "DataBase.h"

YOSYS_NAMESPACE_BEGIN

struct VerificImporter;

struct VerificClocking {
	RTLIL::Module *module = nullptr;
	Verific::Net *clock_net = nullptr;
	Verific::Net *enable_net = nullptr;
	Verific::Net *disable_net = nullptr;
	Verific::Net *body_net = nullptr;
	Verific::Net *cond_net = nullptr;
	SigBit clock_sig = State::Sx;
	SigBit enable_sig = State::S1;
	SigBit disable_sig = State::S0;
	bool posedge = true;
	bool gclk = false;
	bool cond_pol = true;

	VerificClocking() { }
	VerificClocking(VerificImporter *importer, Verific::Net *net, bool sva_at_only = false);
	RTLIL::Cell *addDff(IdString name, SigSpec sig_d, SigSpec sig_q, Const init_value = Const());
	RTLIL::Cell *addAdff(IdString name, RTLIL::SigSpec sig_arst, SigSpec sig_d, SigSpec sig_q, Const arst_value);
	RTLIL::Cell *addDffsr(IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, SigSpec sig_d, SigSpec sig_q);
	RTLIL::Cell *addAldff(IdString name, RTLIL::SigSpec sig_aload, RTLIL::SigSpec sig_adata, SigSpec sig_d, SigSpec sig_q);
	YS_NAME_FWD_POOL(addDff, module->twines()) YS_NAME_FWD_POOL(addAdff, module->twines())
	YS_NAME_FWD_POOL(addDffsr, module->twines()) YS_NAME_FWD_POOL(addAldff, module->twines())

	bool property_matches_sequence(const VerificClocking &seq) const {
		if (clock_net != seq.clock_net)
			return false;
		if (enable_net != seq.enable_net)
			return false;
		if (posedge != seq.posedge)
			return false;
		return true;
	}
};

YOSYS_NAMESPACE_END

#endif
#endif
