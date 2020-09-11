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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum FfType {
	FF_DFF,
	FF_DFFE,
	FF_ADFF0,
	FF_ADFF1,
	FF_ADFFE0,
	FF_ADFFE1,
	FF_DFFSR,
	FF_DFFSRE,
	FF_SDFF0,
	FF_SDFF1,
	FF_SDFFE0,
	FF_SDFFE1,
	FF_SDFFCE0,
	FF_SDFFCE1,
	FF_SR,
	FF_DLATCH,
	FF_ADLATCH0,
	FF_ADLATCH1,
	FF_DLATCHSR,
	NUM_FFTYPES,
};

enum FfNeg {
	NEG_R = 0x1,
	NEG_S = 0x2,
	NEG_E = 0x4,
	NEG_C = 0x8,
	NUM_NEG = 0x10,
};

enum FfInit {
	INIT_X = 0x1,
	INIT_0 = 0x2,
	INIT_1 = 0x4,
};

struct DffLegalizePass : public Pass {
	DffLegalizePass() : Pass("dfflegalize", "convert FFs to types supported by the target") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dfflegalize [options] [selection]\n");
		log("\n");
		log("Converts FFs to types supported by the target.\n");
		log("\n");
		log("    -cell <cell_type_pattern> <init_values>\n");
		log("        specifies a supported group of FF cells.  <cell_type_pattern>\n");
		log("        is a yosys internal fine cell name, where ? characters can be\n");
		log("        as a wildcard matching any character.  <init_values> specifies\n");
		log("        which initialization values these FF cells can support, and can\n");
		log("        be one of:\n");
		log("\n");
		log("        - x (no init value supported)\n");
		log("        - 0\n");
		log("        - 1\n");
		log("        - r (init value has to match reset value, only for some FF types)\n");
		log("        - 01 (both 0 and 1 supported).\n");
		log("\n");
		log("    -mince <num>\n");
		log("        specifies a minimum number of FFs that should be using any given\n");
		log("        clock enable signal.  If a clock enable signal doesn't meet this\n");
		log("        threshold, it is unmapped into soft logic.\n");
		log("\n");
		log("    -minsrst <num>\n");
		log("        specifies a minimum number of FFs that should be using any given\n");
		log("        sync set/reset signal.  If a sync set/reset signal doesn't meet this\n");
		log("        threshold, it is unmapped into soft logic.\n");
		log("\n");
		log("The following cells are supported by this pass (ie. will be ingested,\n");
		log("and can be specified as allowed targets):\n");
		log("\n");
		log("- $_DFF_[NP]_\n");
		log("- $_DFFE_[NP][NP]_\n");
		log("- $_DFF_[NP][NP][01]_\n");
		log("- $_DFFE_[NP][NP][01][NP]_\n");
		log("- $_DFFSR_[NP][NP][NP]_\n");
		log("- $_DFFSRE_[NP][NP][NP][NP]_\n");
		log("- $_SDFF_[NP][NP][01]_\n");
		log("- $_SDFFE_[NP][NP][01][NP]_\n");
		log("- $_SDFFCE_[NP][NP][01][NP]_\n");
		log("- $_SR_[NP][NP]_\n");
		log("- $_DLATCH_[NP]_\n");
		log("- $_DLATCH_[NP][NP][01]_\n");
		log("- $_DLATCHSR_[NP][NP][NP]_\n");
		log("\n");
		log("The following transformations are performed by this pass:");
		log("\n");
		log("- upconversion from a less capable cell to a more capable cell, if the less");
		log("  capable cell is not supported (eg. dff -> dffe, or adff -> dffsr)");
		log("\n");
		log("- unmapping FFs with clock enable (due to unsupported cell type or -mince)");
		log("\n");
		log("- unmapping FFs with sync reset (due to unsupported cell type or -minsrst)");
		log("\n");
		log("- adding inverters on the control pins (due to unsupported polarity)");
		log("\n");
		log("- adding inverters on the D and Q pins and inverting the init/reset values\n");
		log("  (due to unsupported init or reset value)");
		log("\n");
		log("- converting sr into adlatch (by tying D to 1 and using E as set input)");
		log("\n");
		log("- emulating unsupported dffsr cell by adff + adff + sr + mux");
		log("\n");
		log("- emulating unsupported dlatchsr cell by adlatch + adlatch + sr + mux");
		log("\n");
		log("- emulating adff when the (reset, init) value combination is unsupported by\n");
		log("  dff + adff + dlatch + mux");
		log("\n");
		log("- emulating adlatch when the (reset, init) value combination is unsupported by\n");
		log("- dlatch + adlatch + dlatch + mux");
		log("\n");
		log("If the pass is unable to realize a given cell type (eg. adff when only plain dff");
		log("is available), an error is raised.");
	}

	// Table of all supported cell types.
	// First index in the array is one of the FF_* values, second 
	// index is the set of negative-polarity inputs (OR of NEG_*
	// values), and the value is the set of supported init values
	// (OR of INIT_* values).
	int supported_cells_neg[NUM_FFTYPES][NUM_NEG];
	// Aggregated table ignoring signal polarity.
	int supported_cells[NUM_FFTYPES];
	// Aggregated for all *dff* cells.
	int supported_dff;
	// Aggregated for all dffsr* cells.
	int supported_dffsr;
	// Aggregated for all adff* cells.
	int supported_adff0;
	int supported_adff1;
	// Aggregated for all sdff* cells.
	int supported_sdff0;
	int supported_sdff1;
	// Aggregated for all ways to obtain a SR latch.
	int supported_sr;
	// Aggregated for all *dlatch* cells.
	int supported_dlatch;

	int mince;
	int minsrst;

	dict<SigBit, int> ce_used;
	dict<SigBit, int> srst_used;

	SigMap sigmap;
	FfInitVals initvals;

	int flip_initmask(int mask) {
		int res = mask & INIT_X;
		if (mask & INIT_0)
			res |= INIT_1;
		if (mask & INIT_1)
			res |= INIT_0;
		return res;
	}

	void handle_ff(Cell *cell) {
		std::string type_str = cell->type.str();

		FfType ff_type;
		int ff_neg = 0;
		SigSpec sig_d;
		SigSpec sig_q;
		SigSpec sig_c;
		SigSpec sig_e;
		SigSpec sig_r;
		SigSpec sig_s;
		bool has_srst = false;

		if (cell->hasPort(ID::D))
			sig_d = cell->getPort(ID::D);
		if (cell->hasPort(ID::Q))
			sig_q = cell->getPort(ID::Q);
		if (cell->hasPort(ID::C))
			sig_c = cell->getPort(ID::C);
		if (cell->hasPort(ID::E))
			sig_e = cell->getPort(ID::E);
		if (cell->hasPort(ID::R))
			sig_r = cell->getPort(ID::R);
		if (cell->hasPort(ID::S))
			sig_s = cell->getPort(ID::S);
		
		if (type_str.substr(0, 5) == "$_SR_") {
			ff_type = FF_SR;
			if (type_str[5] == 'N')
				ff_neg |= NEG_S;
			if (type_str[6] == 'N')
				ff_neg |= NEG_R;
		} else if (type_str.substr(0, 6) == "$_DFF_" && type_str.size() == 8) {
			ff_type = FF_DFF;
			if (type_str[6] == 'N')
				ff_neg |= NEG_C;
		} else if (type_str.substr(0, 7) == "$_DFFE_" && type_str.size() == 10) {
			ff_type = FF_DFFE;
			if (type_str[7] == 'N')
				ff_neg |= NEG_C;
			if (type_str[8] == 'N')
				ff_neg |= NEG_E;
		} else if (type_str.substr(0, 6) == "$_DFF_" && type_str.size() == 10) {
			ff_type = type_str[8] == '1' ? FF_ADFF1 : FF_ADFF0;
			if (type_str[6] == 'N')
				ff_neg |= NEG_C;
			if (type_str[7] == 'N')
				ff_neg |= NEG_R;
		} else if (type_str.substr(0, 7) == "$_DFFE_" && type_str.size() == 12) {
			ff_type = type_str[9] == '1' ? FF_ADFFE1 : FF_ADFFE0;
			if (type_str[7] == 'N')
				ff_neg |= NEG_C;
			if (type_str[8] == 'N')
				ff_neg |= NEG_R;
			if (type_str[10] == 'N')
				ff_neg |= NEG_E;
		} else if (type_str.substr(0, 8) == "$_DFFSR_" && type_str.size() == 12) {
			ff_type = FF_DFFSR;
			if (type_str[8] == 'N')
				ff_neg |= NEG_C;
			if (type_str[9] == 'N')
				ff_neg |= NEG_S;
			if (type_str[10] == 'N')
				ff_neg |= NEG_R;
		} else if (type_str.substr(0, 9) == "$_DFFSRE_" && type_str.size() == 14) {
			ff_type = FF_DFFSRE;
			if (type_str[9] == 'N')
				ff_neg |= NEG_C;
			if (type_str[10] == 'N')
				ff_neg |= NEG_S;
			if (type_str[11] == 'N')
				ff_neg |= NEG_R;
			if (type_str[12] == 'N')
				ff_neg |= NEG_E;
		} else if (type_str.substr(0, 7) == "$_SDFF_" && type_str.size() == 11) {
			ff_type = type_str[9] == '1' ? FF_SDFF1 : FF_SDFF0;
			if (type_str[7] == 'N')
				ff_neg |= NEG_C;
			if (type_str[8] == 'N')
				ff_neg |= NEG_R;
			has_srst = true;
		} else if (type_str.substr(0, 8) == "$_SDFFE_" && type_str.size() == 13) {
			ff_type = type_str[10] == '1' ? FF_SDFFE1 : FF_SDFFE0;
			if (type_str[8] == 'N')
				ff_neg |= NEG_C;
			if (type_str[9] == 'N')
				ff_neg |= NEG_R;
			if (type_str[11] == 'N')
				ff_neg |= NEG_E;
			has_srst = true;
		} else if (type_str.substr(0, 9) == "$_SDFFCE_" && type_str.size() == 14) {
			ff_type = type_str[11] == '1' ? FF_SDFFCE1 : FF_SDFFCE0;
			if (type_str[9] == 'N')
				ff_neg |= NEG_C;
			if (type_str[10] == 'N')
				ff_neg |= NEG_R;
			if (type_str[12] == 'N')
				ff_neg |= NEG_E;
			has_srst = true;
		} else if (type_str.substr(0, 9) == "$_DLATCH_" && type_str.size() == 11) {
			ff_type = FF_DLATCH;
			if (type_str[9] == 'N')
				ff_neg |= NEG_E;
		} else if (type_str.substr(0, 9) == "$_DLATCH_" && type_str.size() == 13) {
			ff_type = type_str[11] == '1' ? FF_ADLATCH1 : FF_ADLATCH0;
			if (type_str[9] == 'N')
				ff_neg |= NEG_E;
			if (type_str[10] == 'N')
				ff_neg |= NEG_R;
		} else if (type_str.substr(0, 11) == "$_DLATCHSR_" && type_str.size() == 15) {
			ff_type = FF_DLATCHSR;
			if (type_str[11] == 'N')
				ff_neg |= NEG_E;
			if (type_str[12] == 'N')
				ff_neg |= NEG_S;
			if (type_str[13] == 'N')
				ff_neg |= NEG_R;
		} else {
			log_warning("Ignoring unknown ff type %s [%s.%s].\n", log_id(cell->type), log_id(cell->module->name), log_id(cell->name));
			return;
		}

		State initval = initvals(sig_q[0]);
		
		FfInit initmask = INIT_X;
		if (initval == State::S0)
			initmask = INIT_0;
		else if (initval == State::S1)
			initmask = INIT_1;
		const char *reason;

		bool kill_ce = mince && GetSize(sig_c) && GetSize(sig_e) && sig_e[0].wire && ce_used[sig_e[0]] < mince;
		bool kill_srst = minsrst && has_srst && sig_r[0].wire && srst_used[sig_r[0]] < minsrst;

		while (!(supported_cells[ff_type] & initmask) || kill_ce || kill_srst) {
			// Well, cell is not directly supported.  Decide how to deal with it.

			if (ff_type == FF_DFF || ff_type == FF_DFFE) {
				if (kill_ce) {
					ff_type = FF_DFF;
					goto unmap_enable;
				}
				if (!(supported_dff & initmask)) {
					// This init value is not supported at all...
					if (supported_dff & flip_initmask(initmask)) {
						// The other one is, though.  Negate D, Q, and init.
flip_dqi:
						if (initval == State::S0) {
							initval = State::S1;
							initmask = INIT_1;
						} else if (initval == State::S1) {
							initval = State::S0;
							initmask = INIT_0;
						}
						if (ff_type != FF_SR)
							sig_d = cell->module->NotGate(NEW_ID, sig_d[0]);
						SigBit new_q = SigSpec(cell->module->addWire(NEW_ID))[0];
						cell->module->addNotGate(NEW_ID, new_q, sig_q[0]);
						initvals.remove_init(sig_q[0]);
						initvals.set_init(new_q, initval);
						sig_q = new_q;
						continue;
					}
					if (!supported_dff)
						reason = "dffs are not supported";
					else
						reason = "initialized dffs are not supported";
					goto error;
				}

				// Some DFF is supported with this init val.  Just pick a type.
				if (ff_type == FF_DFF) {
					// Try adding a set or reset pin.
					for (auto new_type: {FF_SDFF0, FF_SDFF1, FF_ADFF0, FF_ADFF1})
						if (supported_cells[new_type] & initmask) {
							ff_type = new_type;
							sig_r = State::S0;
							goto cell_ok;
						}
					// Try adding both.
					if (supported_cells[FF_DFFSR] & initmask) {
						ff_type = FF_DFFSR;
						sig_r = State::S0;
						sig_s = State::S0;
						break;
					}
					// Nope.  Will need to add enable and go the DFFE route.
					sig_e = State::S1;
					if (supported_cells[FF_DFFE] & initmask) {
						ff_type = FF_DFFE;
						break;
					}
				}
				// Try adding a set or reset pin.
				for (auto new_type: {FF_SDFFE0, FF_SDFFE1, FF_SDFFCE0, FF_SDFFCE1, FF_ADFFE0, FF_ADFFE1})
					if (supported_cells[new_type] & initmask) {
						ff_type = new_type;
						sig_r = State::S0;
						goto cell_ok;
					}
				// Try adding both.
				if (supported_cells[FF_DFFSRE] & initmask) {
					ff_type = FF_DFFSRE;
					sig_r = State::S0;
					sig_s = State::S0;
					break;
				}

				// Seems that no DFFs with enable are supported.
				// The enable input needs to be unmapped.
				// This should not be reached if we started from plain DFF.
				log_assert(ff_type == FF_DFFE);
				ff_type = FF_DFF;
unmap_enable:
				if (ff_neg & NEG_E)
					sig_d = cell->module->MuxGate(NEW_ID, sig_d[0], sig_q[0], sig_e[0]);
				else
					sig_d = cell->module->MuxGate(NEW_ID, sig_q[0], sig_d[0], sig_e[0]);
				ff_neg &= ~NEG_E;
				sig_e = SigSpec();
				kill_ce = false;
				// Now try again as plain DFF.
				continue;
			} else if (ff_type == FF_ADFF0 || ff_type == FF_ADFF1 || ff_type == FF_ADFFE0 || ff_type == FF_ADFFE1) {
				bool has_set = ff_type == FF_ADFF1 || ff_type == FF_ADFFE1;
				bool has_en = ff_type == FF_ADFFE0 || ff_type == FF_ADFFE1;
				if (kill_ce) {
					ff_type = has_set ? FF_ADFF1 : FF_ADFF0;
					goto unmap_enable;
				}
				if (!has_en && (supported_cells[has_set ? FF_ADFFE1 : FF_ADFFE0] & initmask)) {
					// Just add enable.
					sig_e = State::S1;
					ff_type = has_set ? FF_ADFFE1 : FF_ADFFE0;
					break;
				}
				if (supported_cells[has_en ? FF_DFFSRE : FF_DFFSR] & initmask) {
adff_to_dffsr:
					// Throw in a set/reset, retry in DFFSR/DFFSRE branch.
					if (has_set) {
						sig_s = sig_r;
						sig_r = State::S0;
						if (ff_neg & NEG_R) {
							ff_neg &= ~NEG_R;
							ff_neg |= NEG_S;
						}
					} else {
						sig_s = State::S0;
					}
					if (has_en)
						ff_type = FF_DFFSRE;
					else
						ff_type = FF_DFFSR;
					continue;
				}
				if (has_en && (supported_cells[has_set ? FF_ADFF1 : FF_ADFF0] & initmask)) {
					// Unmap enable.
					ff_type = has_set ? FF_ADFF1 : FF_ADFF0;
					goto unmap_enable;
				}
				if (supported_dffsr & initmask) {
					goto adff_to_dffsr;
				}
				log_assert(!((has_set ? supported_adff1 : supported_adff0) & initmask));
				// Alright, so this particular combination of initval and
				// resetval is not natively supported.  First, try flipping
				// them both to see whether this helps.
				int flipmask = flip_initmask(initmask);
				if ((has_set ? supported_adff0 : supported_adff1) & flipmask) {
					// Checks out, do it.
					ff_type = has_en ? (has_set ? FF_ADFFE0 : FF_ADFFE1) : (has_set ? FF_ADFF0 : FF_ADFF1);
					goto flip_dqi;
				}

				if (!supported_adff0 && !supported_adff1) {
					reason = "dffs with async set or reset are not supported";
					goto error;
				}
				if (!(supported_dff & ~INIT_X)) {
					reason = "initialized dffs are not supported";
					goto error;
				}
				// If we got here, initialized dff is supported, but not this
				// particular reset+init combination (nor its negation).
				// The only hope left is breaking down to adff + dff + dlatch + mux.
				if (!(supported_dlatch & ~INIT_X)) {
					reason = "unsupported initial value and async reset value combination";
					goto error;
				}

				// If we have to unmap enable anyway, do it before breakdown.
				if (has_en && !supported_cells[FF_ADFFE0] && !supported_cells[FF_ADFFE1]) {
					ff_type = has_set ? FF_ADFF1 : FF_ADFF0;
					goto unmap_enable;
				}

				log_warning("Emulating mismatched async reset and init with several FFs and a mux for %s.%s\n", log_id(cell->module->name), log_id(cell->name));
				initvals.remove_init(sig_q[0]);
				Wire *adff_q = cell->module->addWire(NEW_ID);
				Wire *dff_q = cell->module->addWire(NEW_ID);
				Wire *sel_q = cell->module->addWire(NEW_ID);
				initvals.set_init(SigBit(dff_q, 0), initval);
				initvals.set_init(SigBit(sel_q, 0), State::S0);
				Cell *cell_dff;
				Cell *cell_adff;
				Cell *cell_sel;
				if (!has_en) {
					cell_dff = cell->module->addDffGate(NEW_ID, sig_c, sig_d, dff_q, !(ff_neg & NEG_C));
					cell_adff = cell->module->addAdffGate(NEW_ID, sig_c, sig_r, sig_d, adff_q, has_set, !(ff_neg & NEG_C), !(ff_neg & NEG_R));
				} else {
					cell_dff = cell->module->addDffeGate(NEW_ID, sig_c, sig_e, sig_d, dff_q, !(ff_neg & NEG_C), !(ff_neg & NEG_E));
					cell_adff = cell->module->addAdffeGate(NEW_ID, sig_c, sig_e, sig_r, sig_d, adff_q, has_set, !(ff_neg & NEG_C), !(ff_neg & NEG_E), !(ff_neg & NEG_R));
				}
				cell_sel = cell->module->addDlatchGate(NEW_ID, sig_r, State::S1, sel_q, !(ff_neg & NEG_R));
				cell->module->addMuxGate(NEW_ID, dff_q, adff_q, sel_q, sig_q);

				// Bye, cell.
				cell->module->remove(cell);
				handle_ff(cell_dff);
				handle_ff(cell_adff);
				handle_ff(cell_sel);
				return;
			} else if (ff_type == FF_DFFSR || ff_type == FF_DFFSRE) {
				if (kill_ce) {
					ff_type = FF_DFFSR;
					goto unmap_enable;
				}
				// First, see if mapping/unmapping enable will help.
				if (supported_cells[FF_DFFSRE] & initmask) {
					ff_type = FF_DFFSRE;
					sig_e = State::S1;
					break;
				}
				if (supported_cells[FF_DFFSR] & initmask) {
					ff_type = FF_DFFSR;
					goto unmap_enable;
				}
				if (supported_dffsr & flip_initmask(initmask)) {
flip_dqisr:;
					log_warning("Flipping D/Q/init and inserting set/reset fixup to handle init value on %s.%s [%s]\n", log_id(cell->module->name), log_id(cell->name), log_id(cell->type));
					SigSpec new_r;
					bool neg_r = (ff_neg & NEG_R);
					bool neg_s = (ff_neg & NEG_S);
					if (!(ff_neg & NEG_S)) {
						if (!(ff_neg & NEG_R))
							new_r = cell->module->AndnotGate(NEW_ID, sig_s, sig_r);
						else
							new_r = cell->module->AndGate(NEW_ID, sig_s, sig_r);
					} else {
						if (!(ff_neg & NEG_R))
							new_r = cell->module->OrGate(NEW_ID, sig_s, sig_r);
						else
							new_r = cell->module->OrnotGate(NEW_ID, sig_s, sig_r);
					}
					ff_neg &= ~(NEG_R | NEG_S);
					if (neg_r)
						ff_neg |= NEG_S;
					if (neg_s)
						ff_neg |= NEG_R;
					sig_s = sig_r;
					sig_r = new_r;
					goto flip_dqi;
				}
				// No native DFFSR.  However, if we can conjure
				// a SR latch and ADFF, it can still be emulated.
				int flipmask = flip_initmask(initmask);
				bool init0 = true;
				bool init1 = true;
				State initsel = State::Sx;
				if (((supported_adff0 & initmask) || (supported_adff1 & flipmask)) && ((supported_adff1 & initmask) || (supported_adff0 & flipmask)) && supported_sr) {
					// OK
				} else if (((supported_adff0 & initmask) || (supported_adff1 & flipmask)) && (supported_sr & INIT_0)) {
					init1 = false;
					initsel = State::S0;
				} else if (((supported_adff1 & initmask) || (supported_adff0 & flipmask)) && (supported_sr & INIT_1)) {
					init0 = false;
					initsel = State::S1;
				} else if (((supported_adff0 & initmask) || (supported_adff1 & flipmask)) && (supported_sr & INIT_1)) {
					init1 = false;
					initsel = State::S0;
				} else if (((supported_adff1 & initmask) || (supported_adff0 & flipmask)) && (supported_sr & INIT_0)) {
					init0 = false;
					initsel = State::S1;
				} else {
					if (!supported_dffsr)
						reason = "dffs with async set and reset are not supported";
					else
						reason = "initialized dffs with async set and reset are not supported";
					goto error;
				}

				// If we have to unmap enable anyway, do it before breakdown.
				if (ff_type == FF_DFFSRE && !supported_cells[FF_ADFFE0] && !supported_cells[FF_ADFFE1]) {
					ff_type = FF_DFFSR;
					goto unmap_enable;
				}

				log_warning("Emulating async set + reset with several FFs and a mux for %s.%s\n", log_id(cell->module->name), log_id(cell->name));
				initvals.remove_init(sig_q[0]);
				Wire *adff0_q = cell->module->addWire(NEW_ID);
				Wire *adff1_q = cell->module->addWire(NEW_ID);
				Wire *sel_q = cell->module->addWire(NEW_ID);
				if (init0)
					initvals.set_init(SigBit(adff0_q, 0), initval);
				if (init1)
					initvals.set_init(SigBit(adff1_q, 0), initval);
				initvals.set_init(SigBit(sel_q, 0), initsel);
				Cell *cell_adff0;
				Cell *cell_adff1;
				Cell *cell_sel;
				if (ff_type == FF_DFFSR) {
					cell_adff0 = cell->module->addAdffGate(NEW_ID, sig_c, sig_r, sig_d, adff0_q, false, !(ff_neg & NEG_C), !(ff_neg & NEG_R));
					cell_adff1 = cell->module->addAdffGate(NEW_ID, sig_c, sig_s, sig_d, adff1_q, true, !(ff_neg & NEG_C), !(ff_neg & NEG_S));
				} else {
					cell_adff0 = cell->module->addAdffeGate(NEW_ID, sig_c, sig_e, sig_r, sig_d, adff0_q, false, !(ff_neg & NEG_C), !(ff_neg & NEG_E), !(ff_neg & NEG_R));
					cell_adff1 = cell->module->addAdffeGate(NEW_ID, sig_c, sig_e, sig_s, sig_d, adff1_q, true, !(ff_neg & NEG_C), !(ff_neg & NEG_E), !(ff_neg & NEG_S));
				}
				cell_sel = cell->module->addSrGate(NEW_ID, sig_s, sig_r, sel_q, !(ff_neg & NEG_S), !(ff_neg & NEG_R));
				cell->module->addMuxGate(NEW_ID, adff0_q, adff1_q, sel_q, sig_q);

				// Bye, cell.
				cell->module->remove(cell);
				handle_ff(cell_adff0);
				handle_ff(cell_adff1);
				handle_ff(cell_sel);
				return;
			} else if (ff_type == FF_SR) {
				if (supported_cells[FF_ADLATCH0] & initmask || supported_cells[FF_ADLATCH1] & flip_initmask(initmask)) {
					// Convert to ADLATCH0.  May get converted to ADLATCH1.
					ff_type = FF_ADLATCH0;
					sig_e = sig_s;
					sig_d = State::S1;
					if (ff_neg & NEG_S) {
						ff_neg &= ~NEG_S;
						ff_neg |= NEG_E;
					}
					continue;
				} else if (supported_cells[FF_DLATCHSR] & initmask) {
					// Upgrade to DLATCHSR.
					ff_type = FF_DLATCHSR;
					sig_e = State::S0;
					sig_d = State::Sx;
					break;
				} else if (supported_dffsr & initmask) {
					// Upgrade to DFFSR.  May get further upgraded to DFFSRE.
					ff_type = FF_DFFSR;
					sig_c = State::S0;
					sig_d = State::Sx;
					continue;
				} else if (supported_sr & flip_initmask(initmask)) {
					goto flip_dqisr;
				} else {
					if (!supported_sr)
						reason = "sr latches are not supported";
					else
						reason = "initialized sr latches are not supported";
					goto error;
				}
			} else if (ff_type == FF_DLATCH) {
				if (!(supported_dlatch & initmask)) {
					// This init value is not supported at all...
					if (supported_dlatch & flip_initmask(initmask))
						goto flip_dqi;

					if ((sig_d == State::S0 && (supported_adff0 & initmask)) ||
							(sig_d == State::S1 && (supported_adff1 & initmask)) ||
							(sig_d == State::S0 && (supported_adff1 & flip_initmask(initmask))) ||
							(sig_d == State::S1 && (supported_adff0 & flip_initmask(initmask)))
					) {
						// Special case: const-D dlatch can be converted into adff with const clock.
						ff_type = (sig_d == State::S0) ? FF_ADFF0 : FF_ADFF1;
						if (ff_neg & NEG_E) {
							ff_neg &= ~NEG_E;
							ff_neg |= NEG_R;
						}
						sig_r = sig_e;
						sig_d = State::Sx;
						sig_c = State::S1;
						continue;
					}

					if (!supported_dlatch)
						reason = "dlatch are not supported";
					else
						reason = "initialized dlatch are not supported";
					goto error;
				}

				// Some DLATCH is supported with this init val.  Just pick a type.
				if (supported_cells[FF_ADLATCH0] & initmask) {
					ff_type = FF_ADLATCH0;
					sig_r = State::S0;
					break;
				}
				if (supported_cells[FF_ADLATCH1] & initmask) {
					ff_type = FF_ADLATCH1;
					sig_r = State::S0;
					break;
				}
				if (supported_cells[FF_DLATCHSR] & initmask) {
					ff_type = FF_DLATCHSR;
					sig_r = State::S0;
					sig_s = State::S0;
					break;
				}
				log_assert(0);
			} else if (ff_type == FF_ADLATCH0 || ff_type == FF_ADLATCH1) {
				if (supported_cells[FF_DLATCHSR] & initmask) {
					if (ff_type == FF_ADLATCH1) {
						sig_s = sig_r;
						sig_r = State::S0;
						if (ff_neg & NEG_R) {
							ff_neg &= ~NEG_R;
							ff_neg |= NEG_S;
						}
					} else {
						sig_s = State::S0;
					}
					ff_type = FF_DLATCHSR;
					break;
				}
				FfType flip_type = ff_type == FF_ADLATCH0 ? FF_ADLATCH1 : FF_ADLATCH0;
				if ((supported_cells[flip_type] | supported_cells[FF_DLATCHSR]) & flip_initmask(initmask)) {
					ff_type = flip_type;
					goto flip_dqi;
				}

				if (!supported_cells[FF_ADLATCH0] && !supported_cells[FF_ADLATCH1] && !supported_cells[FF_DLATCHSR]) {
					reason = "dlatch with async set or reset are not supported";
					goto error;
				}
				if (!(supported_dlatch & ~INIT_X)) {
					reason = "initialized dlatch are not supported";
					goto error;
				}

				if (!(supported_dlatch & ~INIT_X)) {
					reason = "initialized dlatch are not supported";
					goto error;
				}
				// If we got here, initialized dlatch is supported, but not this
				// particular reset+init combination (nor its negation).
				// The only hope left is breaking down to adff + dff + dlatch + mux.

				log_warning("Emulating mismatched async reset and init with several latches and a mux for %s.%s\n", log_id(cell->module->name), log_id(cell->name));
				initvals.remove_init(sig_q[0]);
				Wire *adlatch_q = cell->module->addWire(NEW_ID);
				Wire *dlatch_q = cell->module->addWire(NEW_ID);
				Wire *sel_q = cell->module->addWire(NEW_ID);
				initvals.set_init(SigBit(dlatch_q, 0), initval);
				initvals.set_init(SigBit(sel_q, 0), State::S0);
				Cell *cell_dlatch;
				Cell *cell_adlatch;
				Cell *cell_sel;
				cell_dlatch = cell->module->addDlatchGate(NEW_ID, sig_e, sig_d, dlatch_q, !(ff_neg & NEG_E));
				cell_adlatch = cell->module->addAdlatchGate(NEW_ID, sig_e, sig_r, sig_d, adlatch_q, ff_type == FF_ADLATCH1, !(ff_neg & NEG_E), !(ff_neg & NEG_R));
				cell_sel = cell->module->addDlatchGate(NEW_ID, sig_r, State::S1, sel_q, !(ff_neg & NEG_R));
				cell->module->addMuxGate(NEW_ID, dlatch_q, adlatch_q, sel_q, sig_q);

				// Bye, cell.
				cell->module->remove(cell);
				handle_ff(cell_dlatch);
				handle_ff(cell_adlatch);
				handle_ff(cell_sel);
				return;
			} else if (ff_type == FF_DLATCHSR) {
				if (supported_cells[FF_DLATCHSR] & flip_initmask(initmask)) {
					goto flip_dqisr;
				}
				// No native DFFSR.  However, if we can conjure
				// a SR latch and ADFF, it can still be emulated.
				int flipmask = flip_initmask(initmask);
				bool init0 = true;
				bool init1 = true;
				State initsel = State::Sx;
				if (((supported_cells[FF_ADLATCH0] & initmask) || (supported_cells[FF_ADLATCH1] & flipmask)) && ((supported_cells[FF_ADLATCH1] & initmask) || (supported_cells[FF_ADLATCH0] & flipmask)) && supported_sr) {
					// OK
				} else if (((supported_cells[FF_ADLATCH0] & initmask) || (supported_cells[FF_ADLATCH1] & flipmask)) && (supported_sr & INIT_0)) {
					init1 = false;
					initsel = State::S0;
				} else if (((supported_cells[FF_ADLATCH1] & initmask) || (supported_cells[FF_ADLATCH0] & flipmask)) && (supported_sr & INIT_1)) {
					init0 = false;
					initsel = State::S1;
				} else if (((supported_cells[FF_ADLATCH0] & initmask) || (supported_cells[FF_ADLATCH1] & flipmask)) && (supported_sr & INIT_1)) {
					init1 = false;
					initsel = State::S0;
				} else if (((supported_cells[FF_ADLATCH1] & initmask) || (supported_cells[FF_ADLATCH0] & flipmask)) && (supported_sr & INIT_0)) {
					init0 = false;
					initsel = State::S1;
				} else {
					if (!supported_cells[FF_DLATCHSR])
						reason = "dlatch with async set and reset are not supported";
					else
						reason = "initialized dlatch with async set and reset are not supported";
					goto error;
				}

				log_warning("Emulating async set + reset with several latches and a mux for %s.%s\n", log_id(cell->module->name), log_id(cell->name));
				initvals.remove_init(sig_q[0]);
				Wire *adlatch0_q = cell->module->addWire(NEW_ID);
				Wire *adlatch1_q = cell->module->addWire(NEW_ID);
				Wire *sel_q = cell->module->addWire(NEW_ID);
				if (init0)
					initvals.set_init(SigBit(adlatch0_q, 0), initval);
				if (init1)
					initvals.set_init(SigBit(adlatch1_q, 0), initval);
				initvals.set_init(SigBit(sel_q, 0), initsel);
				Cell *cell_adlatch0;
				Cell *cell_adlatch1;
				Cell *cell_sel;
				cell_adlatch0 = cell->module->addAdlatchGate(NEW_ID, sig_e, sig_r, sig_d, adlatch0_q, false, !(ff_neg & NEG_E), !(ff_neg & NEG_R));
				cell_adlatch1 = cell->module->addAdlatchGate(NEW_ID, sig_e, sig_s, sig_d, adlatch1_q, true, !(ff_neg & NEG_E), !(ff_neg & NEG_S));
				cell_sel = cell->module->addSrGate(NEW_ID, sig_s, sig_r, sel_q, !(ff_neg & NEG_S), !(ff_neg & NEG_R));
				cell->module->addMuxGate(NEW_ID, adlatch0_q, adlatch1_q, sel_q, sig_q);

				// Bye, cell.
				cell->module->remove(cell);
				handle_ff(cell_adlatch0);
				handle_ff(cell_adlatch1);
				handle_ff(cell_sel);
				return;
			} else if (ff_type == FF_SDFF0 || ff_type == FF_SDFF1 || ff_type == FF_SDFFE0 || ff_type == FF_SDFFE1 || ff_type == FF_SDFFCE0 || ff_type == FF_SDFFCE1) {
				bool has_set = ff_type == FF_SDFF1 || ff_type == FF_SDFFE1 || ff_type == FF_SDFFCE1;
				bool has_en = ff_type == FF_SDFFE0 || ff_type == FF_SDFFE1;
				bool has_ce = ff_type == FF_SDFFCE0 || ff_type == FF_SDFFCE1;

				if (has_en) {
					if (kill_ce || kill_srst) {
						ff_type = has_set ? FF_SDFF1 : FF_SDFF0;
						goto unmap_enable;
					}
				} else if (has_ce) {
					if (kill_ce || kill_srst)
						goto unmap_srst;
				} else {
					log_assert(!kill_ce);
					if (kill_srst)
						goto unmap_srst;
				}

				if (!has_ce) {
					if (!has_en && (supported_cells[has_set ? FF_SDFFE1 : FF_SDFFE0] & initmask)) {
						// Just add enable.
						sig_e = State::S1;
						ff_type = has_set ? FF_SDFFE1 : FF_SDFFE0;
						break;
					}
					if (!has_en && (supported_cells[has_set ? FF_SDFFCE1 : FF_SDFFCE0] & initmask)) {
						// Just add enable.
						sig_e = State::S1;
						ff_type = has_set ? FF_SDFFCE1 : FF_SDFFCE0;
						break;
					}
					if (has_en && (supported_cells[has_set ? FF_SDFFCE1 : FF_SDFFCE0] & initmask)) {
						// Convert sdffe to sdffce
						if (!(ff_neg & NEG_E)) {
							if (!(ff_neg & NEG_R))
								sig_e = cell->module->OrGate(NEW_ID, sig_e, sig_r);
							else
								sig_e = cell->module->OrnotGate(NEW_ID, sig_e, sig_r);
						} else {
							if (!(ff_neg & NEG_R))
								sig_e = cell->module->AndnotGate(NEW_ID, sig_e, sig_r);
							else
								sig_e = cell->module->AndGate(NEW_ID, sig_e, sig_r);
						}
						ff_type = has_set ? FF_SDFFCE1 : FF_SDFFCE0;
						break;
					}
					if (has_en && (supported_cells[has_set ? FF_SDFF1 : FF_SDFF0] & initmask)) {
						// Unmap enable.
						ff_type = has_set ? FF_SDFF1 : FF_SDFF0;
						goto unmap_enable;
					}
					log_assert(!((has_set ? supported_sdff1 : supported_sdff0) & initmask));
				} else {
					if ((has_set ? supported_sdff1 : supported_sdff0) & initmask) {
						// Convert sdffce to sdffe, which may be further converted to sdff.
						if (!(ff_neg & NEG_R)) {
							if (!(ff_neg & NEG_E))
								sig_r = cell->module->AndGate(NEW_ID, sig_r, sig_e);
							else
								sig_r = cell->module->AndnotGate(NEW_ID, sig_r, sig_e);
						} else {
							if (!(ff_neg & NEG_E))
								sig_r = cell->module->OrnotGate(NEW_ID, sig_r, sig_e);
							else
								sig_r = cell->module->OrGate(NEW_ID, sig_r, sig_e);
						}
						ff_type = has_set ? FF_SDFFE1 : FF_SDFFE0;
						continue;
					}
				}
				// Alright, so this particular combination of initval and
				// resetval is not natively supported.  First, try flipping
				// them both to see whether this helps.
				if ((has_set ? supported_sdff0 : supported_sdff1) & flip_initmask(initmask)) {
					// Checks out, do it.
					ff_type = has_ce ? (has_set ? FF_SDFFCE0 : FF_SDFFCE1) : has_en ? (has_set ? FF_SDFFE0 : FF_SDFFE1) : (has_set ? FF_SDFF0 : FF_SDFF1);
					goto flip_dqi;
				}

				// Nope.  No way to get SDFF* of the right kind, so unmap it.
				// For SDFFE, the enable has to be unmapped first.
				if (has_en) {
					ff_type = has_set ? FF_SDFF1 : FF_SDFF0;
					goto unmap_enable;
				}
unmap_srst:
				if (has_ce)
					ff_type = FF_DFFE;
				else
					ff_type = FF_DFF;
				if (ff_neg & NEG_R)
					sig_d = cell->module->MuxGate(NEW_ID, has_set ? State::S1 : State::S0, sig_d[0], sig_r[0]);
				else
					sig_d = cell->module->MuxGate(NEW_ID, sig_d[0], has_set ? State::S1 : State::S0, sig_r[0]);
				ff_neg &= ~NEG_R;
				sig_r = SigSpec();
				kill_srst = false;
				continue;
			} else {
				log_assert(0);
			}
		}
cell_ok:

		if (!(supported_cells_neg[ff_type][ff_neg] & initmask)) {
			// Cell is supported, but not with those polarities.
			// Will need to add some inverters.

			// Find the smallest value that xored with the neg mask
			// results in a supported one — this results in preferentially
			// inverting resets before clocks, etc.
			int xneg;
			for (xneg = 0; xneg < NUM_NEG; xneg++)
				if (supported_cells_neg[ff_type][ff_neg ^ xneg] & initmask)
					break;
			log_assert(xneg < NUM_NEG);
			if (xneg & NEG_R)
				sig_r = cell->module->NotGate(NEW_ID, sig_r[0]);
			if (xneg & NEG_S)
				sig_s = cell->module->NotGate(NEW_ID, sig_s[0]);
			if (xneg & NEG_E)
				sig_e = cell->module->NotGate(NEW_ID, sig_e[0]);
			if (xneg & NEG_C)
				sig_c = cell->module->NotGate(NEW_ID, sig_c[0]);
			ff_neg ^= xneg;
		}

		cell->unsetPort(ID::D);
		cell->unsetPort(ID::Q);
		cell->unsetPort(ID::C);
		cell->unsetPort(ID::E);
		cell->unsetPort(ID::S);
		cell->unsetPort(ID::R);
		switch (ff_type) {
			case FF_DFF:
				cell->type = IdString(stringf("$_DFF_%c_",
						(ff_neg & NEG_C) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				break;
			case FF_DFFE:
				cell->type = IdString(stringf("$_DFFE_%c%c_",
						(ff_neg & NEG_C) ? 'N' : 'P',
						(ff_neg & NEG_E) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				cell->setPort(ID::E, sig_e);
				break;
			case FF_ADFF0:
			case FF_ADFF1:
				cell->type = IdString(stringf("$_DFF_%c%c%c_",
						(ff_neg & NEG_C) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P',
						(ff_type == FF_ADFF1) ? '1' : '0'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_ADFFE0:
			case FF_ADFFE1:
				cell->type = IdString(stringf("$_DFFE_%c%c%c%c_",
						(ff_neg & NEG_C) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P',
						(ff_type == FF_ADFFE1) ? '1' : '0',
						(ff_neg & NEG_E) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				cell->setPort(ID::E, sig_e);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_DFFSR:
				cell->type = IdString(stringf("$_DFFSR_%c%c%c_",
						(ff_neg & NEG_C) ? 'N' : 'P',
						(ff_neg & NEG_S) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				cell->setPort(ID::S, sig_s);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_DFFSRE:
				cell->type = IdString(stringf("$_DFFSRE_%c%c%c%c_",
						(ff_neg & NEG_C) ? 'N' : 'P',
						(ff_neg & NEG_S) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P',
						(ff_neg & NEG_E) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				cell->setPort(ID::E, sig_e);
				cell->setPort(ID::S, sig_s);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_SDFF0:
			case FF_SDFF1:
				cell->type = IdString(stringf("$_SDFF_%c%c%c_",
						(ff_neg & NEG_C) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P',
						(ff_type == FF_SDFF1) ? '1' : '0'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_SDFFE0:
			case FF_SDFFE1:
				cell->type = IdString(stringf("$_SDFFE_%c%c%c%c_",
						(ff_neg & NEG_C) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P',
						(ff_type == FF_SDFFE1) ? '1' : '0',
						(ff_neg & NEG_E) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				cell->setPort(ID::E, sig_e);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_SDFFCE0:
			case FF_SDFFCE1:
				cell->type = IdString(stringf("$_SDFFCE_%c%c%c%c_",
						(ff_neg & NEG_C) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P',
						(ff_type == FF_SDFFCE1) ? '1' : '0',
						(ff_neg & NEG_E) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::C, sig_c);
				cell->setPort(ID::E, sig_e);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_DLATCH:
				cell->type = IdString(stringf("$_DLATCH_%c_",
						(ff_neg & NEG_E) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::E, sig_e);
				break;
			case FF_ADLATCH0:
			case FF_ADLATCH1:
				cell->type = IdString(stringf("$_DLATCH_%c%c%c_",
						(ff_neg & NEG_E) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P',
						(ff_type == FF_ADLATCH1) ? '1' : '0'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::E, sig_e);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_DLATCHSR:
				cell->type = IdString(stringf("$_DLATCHSR_%c%c%c_",
						(ff_neg & NEG_E) ? 'N' : 'P',
						(ff_neg & NEG_S) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P'
					));
				cell->setPort(ID::D, sig_d);
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::E, sig_e);
				cell->setPort(ID::S, sig_s);
				cell->setPort(ID::R, sig_r);
				break;
			case FF_SR:
				cell->type = IdString(stringf("$_SR_%c%c_",
						(ff_neg & NEG_S) ? 'N' : 'P',
						(ff_neg & NEG_R) ? 'N' : 'P'
					));
				cell->setPort(ID::Q, sig_q);
				cell->setPort(ID::S, sig_s);
				cell->setPort(ID::R, sig_r);
				break;
			default:
				log_assert(0);
		}
		return;

error:
		log_error("FF %s.%s (type %s) cannot be legalized: %s\n", log_id(cell->module->name), log_id(cell->name), log_id(cell->type), reason);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{

		log_header(design, "Executing DFFLEGALIZE pass (convert FFs to types supported by the target).\n");

		for (int i = 0; i < NUM_FFTYPES; i++) {
			for (int j = 0; j < NUM_NEG; j++)
				supported_cells_neg[i][j] = 0;
			supported_cells[i] = 0;
		}
		mince = 0;
		minsrst = 0;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-cell" && argidx + 2 < args.size()) {
				std::string celltype = args[++argidx];
				std::string inittype = args[++argidx];
				enum FfType ff_type[2] = {NUM_FFTYPES, NUM_FFTYPES};
				char pol_c = 0;
				char pol_e = 0;
				char pol_s = 0;
				char pol_r = 0;
				char srval = 0;
				if (celltype.substr(0, 5) == "$_SR_" && celltype.size() == 8 && celltype[7] == '_') {
					ff_type[0] = FF_SR;
					pol_s = celltype[5];
					pol_r = celltype[6];
				} else if (celltype.substr(0, 6) == "$_DFF_" && celltype.size() == 8 && celltype[7] == '_') {
					ff_type[0] = FF_DFF;
					pol_c = celltype[6];
				} else if (celltype.substr(0, 7) == "$_DFFE_" && celltype.size() == 10 && celltype[9] == '_') {
					ff_type[0] = FF_DFFE;
					pol_c = celltype[7];
					pol_e = celltype[8];
				} else if (celltype.substr(0, 6) == "$_DFF_" && celltype.size() == 10 && celltype[9] == '_') {
					ff_type[0] = FF_ADFF0;
					ff_type[1] = FF_ADFF1;
					pol_c = celltype[6];
					pol_r = celltype[7];
					srval = celltype[8];
				} else if (celltype.substr(0, 7) == "$_DFFE_" && celltype.size() == 12 && celltype[11] == '_') {
					ff_type[0] = FF_ADFFE0;
					ff_type[1] = FF_ADFFE1;
					pol_c = celltype[7];
					pol_r = celltype[8];
					srval = celltype[9];
					pol_e = celltype[10];
				} else if (celltype.substr(0, 8) == "$_DFFSR_" && celltype.size() == 12 && celltype[11] == '_') {
					ff_type[0] = FF_DFFSR;
					pol_c = celltype[8];
					pol_s = celltype[9];
					pol_r = celltype[10];
				} else if (celltype.substr(0, 9) == "$_DFFSRE_" && celltype.size() == 14 && celltype[13] == '_') {
					ff_type[0] = FF_DFFSRE;
					pol_c = celltype[9];
					pol_s = celltype[10];
					pol_r = celltype[11];
					pol_e = celltype[12];
				} else if (celltype.substr(0, 7) == "$_SDFF_" && celltype.size() == 11 && celltype[10] == '_') {
					ff_type[0] = FF_SDFF0;
					ff_type[1] = FF_SDFF1;
					pol_c = celltype[7];
					pol_r = celltype[8];
					srval = celltype[9];
				} else if (celltype.substr(0, 8) == "$_SDFFE_" && celltype.size() == 13 && celltype[12] == '_') {
					ff_type[0] = FF_SDFFE0;
					ff_type[1] = FF_SDFFE1;
					pol_c = celltype[8];
					pol_r = celltype[9];
					srval = celltype[10];
					pol_e = celltype[11];
				} else if (celltype.substr(0, 9) == "$_SDFFCE_" && celltype.size() == 14 && celltype[13] == '_') {
					ff_type[0] = FF_SDFFCE0;
					ff_type[1] = FF_SDFFCE1;
					pol_c = celltype[9];
					pol_r = celltype[10];
					srval = celltype[11];
					pol_e = celltype[12];
				} else if (celltype.substr(0, 9) == "$_DLATCH_" && celltype.size() == 11 && celltype[10] == '_') {
					ff_type[0] = FF_DLATCH;
					pol_e = celltype[9];
				} else if (celltype.substr(0, 9) == "$_DLATCH_" && celltype.size() == 13 && celltype[12] == '_') {
					ff_type[0] = FF_ADLATCH0;
					ff_type[1] = FF_ADLATCH1;
					pol_e = celltype[9];
					pol_r = celltype[10];
					srval = celltype[11];
				} else if (celltype.substr(0, 11) == "$_DLATCHSR_" && celltype.size() == 15 && celltype[14] == '_') {
					ff_type[0] = FF_DLATCHSR;
					pol_e = celltype[11];
					pol_s = celltype[12];
					pol_r = celltype[13];
				} else {
unrecognized:
					log_error("unrecognized cell type %s.\n", celltype.c_str());
				}
				int mask = 0;
				int match = 0;
				for (auto pair : {
					std::make_pair(pol_c, NEG_C),
					std::make_pair(pol_e, NEG_E),
					std::make_pair(pol_s, NEG_S),
					std::make_pair(pol_r, NEG_R),
				}) {
					if (pair.first == 'N') {
						mask |= pair.second;
						match |= pair.second;
					} else if (pair.first == 'P' || pair.first == 0) {
						mask |= pair.second;
					} else if (pair.first != '?') {
						goto unrecognized;
					}
				}
				if (srval == '0') {
					ff_type[1] = NUM_FFTYPES;
				} else if (srval == '1') {
					ff_type[0] = NUM_FFTYPES;
				} else if (srval != 0 && srval != '?') {
					goto unrecognized;
				}
				for (int i = 0; i < 2; i++) {
					if (ff_type[i] == NUM_FFTYPES)
						continue;
					int initmask;
					if (inittype == "x") {
						initmask = INIT_X;
					} else if (inittype == "0") {
						initmask = INIT_X | INIT_0;
					} else if (inittype == "1") {
						initmask = INIT_X | INIT_1;
					} else if (inittype == "r") {
						if (srval == 0)
							log_error("init type r not valid for cell type %s.\n", celltype.c_str());
						if (i == 0)
							initmask = INIT_X | INIT_0;
						else
							initmask = INIT_X | INIT_1;
					} else if (inittype == "01") {
						initmask = INIT_X | INIT_0 | INIT_1;
					} else {
						log_error("unrecognized init type %s for cell type %s.\n", inittype.c_str(), celltype.c_str());
					}
					for (int neg = 0; neg < NUM_NEG; neg++)
						if ((neg & mask) == match)
							supported_cells_neg[ff_type[i]][neg] |= initmask;
					supported_cells[ff_type[i]] |= initmask;
				}
				continue;
			} else if (args[argidx] == "-mince" && argidx + 1 < args.size()) {
				mince = atoi(args[++argidx].c_str());
				continue;
			} else if (args[argidx] == "-minsrst" && argidx + 1 < args.size()) {
				minsrst = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		supported_dffsr = supported_cells[FF_DFFSR] | supported_cells[FF_DFFSRE];
		supported_adff0 = supported_cells[FF_ADFF0] | supported_cells[FF_ADFFE0] | supported_dffsr;
		supported_adff1 = supported_cells[FF_ADFF1] | supported_cells[FF_ADFFE1] | supported_dffsr;
		supported_sdff0 = supported_cells[FF_SDFF0] | supported_cells[FF_SDFFE0] | supported_cells[FF_SDFFCE0];
		supported_sdff1 = supported_cells[FF_SDFF1] | supported_cells[FF_SDFFE1] | supported_cells[FF_SDFFCE1];
		supported_dff = supported_cells[FF_DFF] | supported_cells[FF_DFFE] | supported_dffsr | supported_adff0 | supported_adff1 | supported_sdff0 | supported_sdff1;
		supported_sr = supported_dffsr | supported_cells[FF_DLATCHSR] | supported_cells[FF_SR] | supported_cells[FF_ADLATCH0] | flip_initmask(supported_cells[FF_ADLATCH1]);
		supported_dlatch = supported_cells[FF_DLATCH] | supported_cells[FF_ADLATCH0] | supported_cells[FF_ADLATCH1] | supported_cells[FF_DLATCHSR];

		for (auto module : design->selected_modules())
		{
			sigmap.set(module);
			initvals.set(&sigmap, module);

			if (mince || minsrst) {
				ce_used.clear();
				srst_used.clear();

				for (auto cell : module->cells()) {
					if (!RTLIL::builtin_ff_cell_types().count(cell->type))
						continue;

					if (cell->hasPort(ID::C) && cell->hasPort(ID::E)) {
						SigSpec sig = cell->getPort(ID::E);
						// Do not count const enable signals.
						if (GetSize(sig) == 1 && sig[0].wire)
							ce_used[sig[0]]++;
					}
					if (cell->type.str().substr(0, 6) == "$_SDFF") {
						SigSpec sig = cell->getPort(ID::R);
						// Do not count const srst signals.
						if (GetSize(sig) == 1 && sig[0].wire)
							srst_used[sig[0]]++;
					}
				}
			}

			// First gather FF cells, then iterate over them later.
			// We may need to split an FF into several cells.
			std::vector<Cell *> ff_cells;

			for (auto cell : module->selected_cells())
			{
				// Early exit for non-FFs.
				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				ff_cells.push_back(cell);
			}

			for (auto cell: ff_cells)
				handle_ff(cell);
		}

		sigmap.clear();
		initvals.clear();
		ce_used.clear();
		srst_used.clear();
	}
} DffLegalizePass;

PRIVATE_NAMESPACE_END
