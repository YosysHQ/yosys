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
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum FfType {
	FF_DFF,
	FF_DFFE,
	FF_ADFF,
	FF_ADFFE,
	FF_ALDFF,
	FF_ALDFFE,
	FF_DFFSR,
	FF_DFFSRE,
	FF_SDFF,
	FF_SDFFE,
	FF_SDFFCE,
	FF_RLATCH,
	FF_SR,
	FF_DLATCH,
	FF_ADLATCH,
	FF_DLATCHSR,
	NUM_FFTYPES,
};

enum FfNeg {
	NEG_CE = 0x1,
	NEG_R = 0x2,
	NEG_S = 0x4,
	NEG_L = 0x8,
	NEG_C = 0x10,
	NUM_NEG = 0x20,
};

enum FfInit {
	INIT_X = 0x1,
	INIT_0 = 0x2,
	INIT_1 = 0x4,
	INIT_X_R0 = 0x10,
	INIT_0_R0 = 0x20,
	INIT_1_R0 = 0x40,
	INIT_X_R1 = 0x100,
	INIT_0_R1 = 0x200,
	INIT_1_R1 = 0x400,
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
		log("- $_ALDFF_[NP][NP]_\n");
		log("- $_ALDFFE_[NP][NP][NP]_\n");
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
		log("The following transformations are performed by this pass:\n");
		log("\n");
		log("- upconversion from a less capable cell to a more capable cell, if the less\n");
		log("  capable cell is not supported (eg. dff -> dffe, or adff -> dffsr)\n");
		log("- unmapping FFs with clock enable (due to unsupported cell type or -mince)\n");
		log("- unmapping FFs with sync reset (due to unsupported cell type or -minsrst)\n");
		log("- adding inverters on the control pins (due to unsupported polarity)\n");
		log("- adding inverters on the D and Q pins and inverting the init/reset values\n");
		log("  (due to unsupported init or reset value)\n");
		log("- converting sr into adlatch (by tying D to 1 and using E as set input)\n");
		log("- emulating unsupported dffsr cell by adff + adff + sr + mux\n");
		log("- emulating unsupported dlatchsr cell by adlatch + adlatch + sr + mux\n");
		log("- emulating adff when the (reset, init) value combination is unsupported by\n");
		log("  dff + adff + dlatch + mux\n");
		log("- emulating adlatch when the (reset, init) value combination is unsupported by\n");
		log("- dlatch + adlatch + dlatch + mux\n");
		log("If the pass is unable to realize a given cell type (eg. adff when only plain dff\n");
		log("is available), an error is raised.\n");
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
	// Aggregated for all *dffe* cells.
	int supported_dffe;
	// Aggregated for all dffsr* cells.
	int supported_dffsr;
	// Aggregated for all aldff cells.
	int supported_aldff;
	// Aggregated for all aldffe cells.
	int supported_aldffe;
	// Aggregated for all adff* cells and trivial emulations.
	int supported_adff;
	// Aggregated for all adffe* cells and trivial emulations.
	int supported_adffe;
	// Aggregated for all sdff* cells.
	int supported_sdff;
	// Aggregated for all ways to obtain a SR latch.
	int supported_sr;
	int supported_sr_plain;
	// Aggregated for all *dlatch* cells.
	int supported_dlatch;
	int supported_dlatch_plain;
	// Aggregated for all ways to obtain an R latch.
	int supported_rlatch;
	// Aggregated for all adlatch cells and trivial emulations.
	int supported_adlatch;

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
		if (mask & INIT_X_R0)
			res |= INIT_X_R1;
		if (mask & INIT_0_R0)
			res |= INIT_1_R1;
		if (mask & INIT_1_R0)
			res |= INIT_0_R1;
		if (mask & INIT_X_R1)
			res |= INIT_X_R0;
		if (mask & INIT_0_R1)
			res |= INIT_1_R0;
		if (mask & INIT_1_R1)
			res |= INIT_0_R0;
		return res;
	}

	int get_ff_type(const FfData &ff) {
		if (ff.has_clk) {
			if (ff.has_sr) {
				return ff.has_ce ? FF_DFFSRE : FF_DFFSR;
			} else if (ff.has_arst) {
				return ff.has_ce ? FF_ADFFE : FF_ADFF;
			} else if (ff.has_aload) {
				return ff.has_ce ? FF_ALDFFE : FF_ALDFF;
			} else if (ff.has_srst) {
				if (ff.has_ce)
					return ff.ce_over_srst ? FF_SDFFCE : FF_SDFFE;
				else
					return FF_SDFF;
			} else {
				return ff.has_ce ? FF_DFFE : FF_DFF;
			}
		} else {
			if (ff.has_aload) {
				if (ff.has_sr)
					return FF_DLATCHSR;
				else if (ff.has_arst)
					return FF_ADLATCH;
				else
					return FF_DLATCH;
			} else {
				if (ff.has_sr) {
					return FF_SR;
				} else if (ff.has_arst) {
					return FF_RLATCH;
				} else {
					log_assert(0);
					return 0;
				}
			}
		}
	}

	int get_initmask(FfData &ff) {
		int res = 0;
		if (ff.val_init[0] == State::S0)
			res = INIT_0;
		else if (ff.val_init[0] == State::S1)
			res = INIT_1;
		else
			res = INIT_X;
		if (ff.has_arst) {
			if (ff.val_arst[0] == State::S0)
				res <<= 4;
			else if (ff.val_arst[0] == State::S1)
				res <<= 8;
		} else if (ff.has_srst) {
			if (ff.val_srst[0] == State::S0)
				res <<= 4;
			else if (ff.val_srst[0] == State::S1)
				res <<= 8;
		}
		return res;
	}

	void fail_ff(const FfData &ff, const char *reason) {
		log_error("FF %s.%s (type %s) cannot be legalized: %s\n", log_id(ff.module->name), log_id(ff.cell->name), log_id(ff.cell->type), reason);
	}

	bool try_flip(FfData &ff, int supported_mask) {
		int initmask = get_initmask(ff);
		if (supported_mask & initmask)
			return true;
		if (supported_mask & flip_initmask(initmask)) {
			ff.flip_bits({0});
			return true;
		}
		return false;
	}

	void emulate_split_init_arst(FfData &ff) {
		ff.remove();

		FfData ff_dff(ff.module, &initvals, NEW_ID);
		ff_dff.width = ff.width;
		ff_dff.has_aload = ff.has_aload;
		ff_dff.sig_aload = ff.sig_aload;
		ff_dff.pol_aload = ff.pol_aload;
		ff_dff.sig_ad = ff.sig_ad;
		ff_dff.has_clk = ff.has_clk;
		ff_dff.sig_clk = ff.sig_clk;
		ff_dff.pol_clk = ff.pol_clk;
		ff_dff.sig_d = ff.sig_d;
		ff_dff.has_ce = ff.has_ce;
		ff_dff.sig_ce = ff.sig_ce;
		ff_dff.pol_ce = ff.pol_ce;
		ff_dff.sig_q = ff.module->addWire(NEW_ID, ff.width);
		ff_dff.val_init = ff.val_init;
		ff_dff.is_fine = ff.is_fine;

		FfData ff_adff(ff.module, &initvals, NEW_ID);
		ff_adff.width = ff.width;
		ff_adff.has_aload = ff.has_aload;
		ff_adff.sig_aload = ff.sig_aload;
		ff_adff.pol_aload = ff.pol_aload;
		ff_adff.sig_ad = ff.sig_ad;
		ff_adff.has_clk = ff.has_clk;
		ff_adff.sig_clk = ff.sig_clk;
		ff_adff.pol_clk = ff.pol_clk;
		ff_adff.sig_d = ff.sig_d;
		ff_adff.has_ce = ff.has_ce;
		ff_adff.sig_ce = ff.sig_ce;
		ff_adff.pol_ce = ff.pol_ce;
		ff_adff.sig_q = ff.module->addWire(NEW_ID, ff.width);
		ff_adff.val_init = Const(State::Sx, ff.width);
		ff_adff.has_arst = true;
		ff_adff.sig_arst = ff.sig_arst;
		ff_adff.pol_arst = ff.pol_arst;
		ff_adff.val_arst = ff.val_arst;
		ff_adff.is_fine = ff.is_fine;

		FfData ff_sel(ff.module, &initvals, NEW_ID);
		ff_sel.width = 1;
		ff_sel.sig_q = ff.module->addWire(NEW_ID);
		ff_sel.has_arst = true;
		ff_sel.sig_arst = ff.sig_arst;
		ff_sel.pol_arst = ff.pol_arst;
		ff_sel.val_arst = State::S1;
		ff_sel.val_init = State::S0;
		ff_sel.is_fine = ff.is_fine;

		if (ff.is_fine)
			ff.module->addMuxGate(NEW_ID, ff_dff.sig_q, ff_adff.sig_q, ff_sel.sig_q, ff.sig_q);
		else
			ff.module->addMux(NEW_ID, ff_dff.sig_q, ff_adff.sig_q, ff_sel.sig_q, ff.sig_q);

		legalize_ff(ff_dff);
		legalize_ff(ff_adff);
		legalize_ff(ff_sel);
	}

	void emulate_split_set_clr(FfData &ff) {
		// No native DFFSR.  However, if we can conjure
		// a SR latch and ADFF, it can still be emulated.
		int initmask = get_initmask(ff);
		int flipmask = flip_initmask(initmask);
		bool init_clr = true;
		bool init_set = true;
		State initsel = State::Sx;
		int supported_arst = ff.has_clk ? supported_adff : supported_adlatch;
		bool init_clr_ok = (supported_arst & initmask << 4) || (supported_arst & flipmask << 8);
		bool init_set_ok = (supported_arst & initmask << 8) || (supported_arst & flipmask << 4);
		if (init_clr_ok && init_set_ok && supported_sr) {
			// OK
		} else if (init_clr_ok && (supported_sr & INIT_0)) {
			init_set = false;
			initsel = State::S0;
		} else if (init_set_ok && (supported_sr & INIT_1)) {
			init_clr = false;
			initsel = State::S1;
		} else if (init_clr_ok && (supported_sr & INIT_1)) {
			init_set = false;
			initsel = State::S0;
		} else if (init_set_ok && (supported_sr & INIT_0)) {
			init_clr = false;
			initsel = State::S1;
		} else {
			if (ff.has_clk) {
				if (!supported_dffsr)
					fail_ff(ff, "dffs with async set and reset are not supported");
				else
					fail_ff(ff, "initialized dffs with async set and reset are not supported");
			} else {
				if (!supported_cells[FF_DLATCHSR])
					fail_ff(ff, "dlatch with async set and reset are not supported");
				else
					fail_ff(ff, "initialized dlatch with async set and reset are not supported");
			}
		}

		// If we have to unmap enable anyway, do it before breakdown.
		if (ff.has_ce && !supported_cells[FF_ADFFE])
			ff.unmap_ce();

		log_warning("Emulating async set + reset with several FFs and a mux for %s.%s\n", log_id(ff.module->name), log_id(ff.cell->name));

		log_assert(ff.width == 1);
		ff.remove();

		FfData ff_clr(ff.module, &initvals, NEW_ID);
		ff_clr.width = ff.width;
		ff_clr.has_aload = ff.has_aload;
		ff_clr.sig_aload = ff.sig_aload;
		ff_clr.pol_aload = ff.pol_aload;
		ff_clr.sig_ad = ff.sig_ad;
		ff_clr.has_clk = ff.has_clk;
		ff_clr.sig_clk = ff.sig_clk;
		ff_clr.pol_clk = ff.pol_clk;
		ff_clr.sig_d = ff.sig_d;
		ff_clr.has_ce = ff.has_ce;
		ff_clr.sig_ce = ff.sig_ce;
		ff_clr.pol_ce = ff.pol_ce;
		ff_clr.has_arst = true;
		ff_clr.sig_arst = ff.sig_clr;
		ff_clr.pol_arst = ff.pol_clr;
		ff_clr.val_arst = Const(State::S0, ff.width);
		ff_clr.sig_q = ff.module->addWire(NEW_ID, ff.width);
		ff_clr.val_init = init_clr ? ff.val_init : Const(State::Sx, ff.width);
		ff_clr.is_fine = ff.is_fine;

		FfData ff_set(ff.module, &initvals, NEW_ID);
		ff_set.width = ff.width;
		ff_set.has_aload = ff.has_aload;
		ff_set.sig_aload = ff.sig_aload;
		ff_set.pol_aload = ff.pol_aload;
		ff_set.sig_ad = ff.sig_ad;
		ff_set.has_clk = ff.has_clk;
		ff_set.sig_clk = ff.sig_clk;
		ff_set.pol_clk = ff.pol_clk;
		ff_set.sig_d = ff.sig_d;
		ff_set.has_ce = ff.has_ce;
		ff_set.sig_ce = ff.sig_ce;
		ff_set.pol_ce = ff.pol_ce;
		ff_set.has_arst = true;
		ff_set.sig_arst = ff.sig_set;
		ff_set.pol_arst = ff.pol_set;
		ff_set.val_arst = Const(State::S1, ff.width);
		ff_set.sig_q = ff.module->addWire(NEW_ID, ff.width);
		ff_set.val_init = init_set ? ff.val_init : Const(State::Sx, ff.width);
		ff_set.is_fine = ff.is_fine;

		FfData ff_sel(ff.module, &initvals, NEW_ID);
		ff_sel.width = ff.width;
		ff_sel.has_sr = true;
		ff_sel.pol_clr = ff.pol_clr;
		ff_sel.pol_set = ff.pol_set;
		ff_sel.sig_clr = ff.sig_clr;
		ff_sel.sig_set = ff.sig_set;
		ff_sel.sig_q = ff.module->addWire(NEW_ID, ff.width);
		ff_sel.val_init = Const(initsel, ff.width);
		ff_sel.is_fine = ff.is_fine;

		if (!ff.is_fine)
			ff.module->addMux(NEW_ID, ff_clr.sig_q, ff_set.sig_q, ff_sel.sig_q, ff.sig_q);
		else
			ff.module->addMuxGate(NEW_ID, ff_clr.sig_q, ff_set.sig_q, ff_sel.sig_q, ff.sig_q);

		legalize_ff(ff_clr);
		legalize_ff(ff_set);
		legalize_ff(ff_sel);
	}

	void legalize_dff(FfData &ff) {
		if (!try_flip(ff, supported_dff)) {
			if (!supported_dff)
				fail_ff(ff, "D flip-flops are not supported");
			else
				fail_ff(ff, "initialized D flip-flops are not supported");
		}

		int initmask = get_initmask(ff);
		// Some DFF is supported with this init val.  Just pick a type.
		if (ff.has_ce && !(supported_dffe & initmask)) {
			ff.unmap_ce();
		}

		if (!ff.has_ce) {
			if (supported_cells[FF_DFF] & initmask) {
				legalize_finish(ff);
				return;
			}
			// Try adding a set or reset pin.
			if (supported_cells[FF_SDFF] & initmask) {
				ff.add_dummy_srst();
				legalize_finish(ff);
				return;
			}
			if (supported_cells[FF_ADFF] & initmask) {
				ff.add_dummy_arst();
				legalize_finish(ff);
				return;
			}
			// Try adding async load.
			if (supported_cells[FF_ALDFF] & initmask) {
				ff.add_dummy_aload();
				legalize_finish(ff);
				return;
			}
			// Try adding both.
			if (supported_cells[FF_DFFSR] & initmask) {
				ff.add_dummy_sr();
				legalize_finish(ff);
				return;
			}
			// Nope.  Will need to add enable and go the DFFE route.
			ff.add_dummy_ce();
		}
		if (supported_cells[FF_DFFE] & initmask) {
			legalize_finish(ff);
			return;
		}
		// Try adding a set or reset pin.
		if (supported_cells[FF_SDFFCE] & initmask) {
			ff.add_dummy_srst();
			ff.ce_over_srst = true;
			legalize_finish(ff);
			return;
		}
		if (supported_cells[FF_SDFFE] & initmask) {
			ff.add_dummy_srst();
			legalize_finish(ff);
			return;
		}
		if (supported_cells[FF_ADFFE] & initmask) {
			ff.add_dummy_arst();
			legalize_finish(ff);
			return;
		}
		if (supported_cells[FF_ALDFFE] & initmask) {
			ff.add_dummy_aload();
			legalize_finish(ff);
			return;
		}
		// Try adding both.
		if (supported_cells[FF_DFFSRE] & initmask) {
			ff.add_dummy_sr();
			legalize_finish(ff);
			return;
		}
		log_assert(0);
	}

	void legalize_sdffce(FfData &ff) {
		if (!try_flip(ff, supported_cells[FF_SDFFCE] | supported_cells[FF_SDFFE])) {
			ff.unmap_srst();
			legalize_dff(ff);
			return;
		}

		int initmask = get_initmask(ff);
		if (supported_cells[FF_SDFFCE] & initmask) {
			// OK
		} else if (supported_cells[FF_SDFFE] & initmask) {
			ff.convert_ce_over_srst(false);
		} else {
			log_assert(0);
		}
		legalize_finish(ff);
	}

	void legalize_sdff(FfData &ff) {
		if (!try_flip(ff, supported_sdff)) {
			ff.unmap_srst();
			legalize_dff(ff);
			return;
		}

		int initmask = get_initmask(ff);
		if (!ff.has_ce) {
			if (supported_cells[FF_SDFF] & initmask) {
				// OK
			} else if (supported_cells[FF_SDFFE] & initmask) {
				ff.add_dummy_ce();
			} else if (supported_cells[FF_SDFFCE] & initmask) {
				ff.add_dummy_ce();
				ff.ce_over_srst = true;
			} else {
				log_assert(0);
			}
		} else {
			log_assert(!ff.ce_over_srst);
			if (supported_cells[FF_SDFFE] & initmask) {
				// OK
			} else if (supported_cells[FF_SDFFCE] & initmask) {
				ff.convert_ce_over_srst(true);
			} else if (supported_cells[FF_SDFF] & initmask) {
				ff.unmap_ce();
			} else {
				log_assert(0);
			}
		}
		legalize_finish(ff);
	}

	void legalize_adff(FfData &ff) {
		if (!try_flip(ff, supported_adff)) {
			if (!supported_adff)
				fail_ff(ff, "dffs with async set or reset are not supported");
			if (!(supported_dff & (INIT_0 | INIT_1)))
				fail_ff(ff, "initialized dffs are not supported");

			// If we got here, initialized dff is supported, but not this
			// particular reset+init combination (nor its negation).
			// The only hope left is breaking down to adff + dff + dlatch + mux.

			if (!((supported_rlatch) & (INIT_0_R1 | INIT_1_R0)))
				fail_ff(ff, "unsupported initial value and async reset value combination");

			// If we have to unmap enable anyway, do it before breakdown.
			if (ff.has_ce && !supported_cells[FF_ADFFE])
				ff.unmap_ce();

			if (ff.cell)
				log_warning("Emulating mismatched async reset and init with several FFs and a mux for %s.%s\n", log_id(ff.module->name), log_id(ff.cell->name));
			emulate_split_init_arst(ff);
			return;
		}

		int initmask = get_initmask(ff);
		if (ff.has_ce && !(supported_adffe & initmask)) {
			ff.unmap_ce();
		}

		if (!ff.has_ce) {
			if (supported_cells[FF_ADFF] & initmask) {
				legalize_finish(ff);
				return;
			}
			// Try converting to async load.
			if (supported_cells[FF_ALDFF] & initmask) {
				ff.arst_to_aload();
				legalize_finish(ff);
				return;
			}
			// Try convertint to SR.
			if (supported_cells[FF_DFFSR] & initmask) {
				ff.arst_to_sr();
				legalize_finish(ff);
				return;
			}
			ff.add_dummy_ce();
		}
		if (supported_cells[FF_ADFFE] & initmask) {
			legalize_finish(ff);
			return;
		}
		// Try converting to async load.
		if (supported_cells[FF_ALDFFE] & initmask) {
			ff.arst_to_aload();
			legalize_finish(ff);
			return;
		}
		// Try convertint to SR.
		if (supported_cells[FF_DFFSRE] & initmask) {
			ff.arst_to_sr();
			legalize_finish(ff);
			return;
		}
		log_assert(0);
	}

	void legalize_aldff(FfData &ff) {
		if (!try_flip(ff, supported_aldff)) {
			ff.aload_to_sr();
			emulate_split_set_clr(ff);
			return;
		}

		int initmask = get_initmask(ff);
		if (ff.has_ce && !(supported_aldffe & initmask)) {
			ff.unmap_ce();
		}

		if (!ff.has_ce) {
			if (supported_cells[FF_ALDFF] & initmask) {
				legalize_finish(ff);
				return;
			}
			if (supported_cells[FF_DFFSR] & initmask) {
				ff.aload_to_sr();
				legalize_finish(ff);
				return;
			}
			ff.add_dummy_ce();
		}
		if (supported_cells[FF_ALDFFE] & initmask) {
			legalize_finish(ff);
			return;
		}
		if (supported_cells[FF_DFFSRE] & initmask) {
			ff.aload_to_sr();
			legalize_finish(ff);
			return;
		}
		log_assert(0);
	}

	void legalize_dffsr(FfData &ff) {
		if (!try_flip(ff, supported_dffsr)) {
			emulate_split_set_clr(ff);
			return;
		}

		int initmask = get_initmask(ff);
		if (ff.has_ce && !(supported_cells[FF_DFFSRE] & initmask)) {
			ff.unmap_ce();
		}

		if (!ff.has_ce) {
			if (supported_cells[FF_DFFSR] & initmask) {
				legalize_finish(ff);
				return;
			}
			ff.add_dummy_ce();
		}

		log_assert(supported_cells[FF_DFFSRE] & initmask);
		legalize_finish(ff);
	}

	void legalize_dlatch(FfData &ff) {
		if (!try_flip(ff, supported_dlatch)) {
			if (!supported_dlatch)
				fail_ff(ff, "D latches are not supported");
			else
				fail_ff(ff, "initialized D latches are not supported");
		}

		int initmask = get_initmask(ff);
		// Some DLATCH is supported with this init val.  Just pick a type.
		if (supported_cells[FF_DLATCH] & initmask) {
			legalize_finish(ff);
		} else if (supported_cells[FF_ADLATCH] & initmask) {
			ff.add_dummy_arst();
			legalize_finish(ff);
		} else if (supported_cells[FF_DLATCHSR] & initmask) {
			ff.add_dummy_sr();
			legalize_finish(ff);
		} else if (supported_cells[FF_ALDFF] & initmask) {
			ff.add_dummy_clk();
			legalize_finish(ff);
		} else if (supported_cells[FF_ALDFFE] & initmask) {
			ff.add_dummy_clk();
			ff.add_dummy_ce();
			legalize_finish(ff);
		} else if (supported_sr & initmask) {
			ff.aload_to_sr();
			legalize_sr(ff);
		} else {
			log_assert(0);
		}
	}

	void legalize_adlatch(FfData &ff) {
		if (!try_flip(ff, supported_adlatch)) {
			if (!supported_adlatch)
				fail_ff(ff, "D latches with async set or reset are not supported");
			if (!(supported_dlatch & (INIT_0 | INIT_1)))
				fail_ff(ff, "initialized D latches are not supported");

			// If we got here, initialized dlatch is supported, but not this
			// particular reset+init combination (nor its negation).
			// The only hope left is breaking down to adlatch + dlatch + dlatch + mux.

			if (ff.cell)
				log_warning("Emulating mismatched async reset and init with several latches and a mux for %s.%s\n", log_id(ff.module->name), log_id(ff.cell->name));
			ff.remove();

			emulate_split_init_arst(ff);
			return;
		}
		int initmask = get_initmask(ff);
		if (supported_cells[FF_ADLATCH] & initmask) {
			// OK
		} else if (supported_cells[FF_DLATCHSR] & initmask) {
			ff.arst_to_sr();
		} else {
			log_assert(0);
		}
		legalize_finish(ff);
	}

	void legalize_dlatchsr(FfData &ff) {
		if (!try_flip(ff, supported_cells[FF_DLATCHSR])) {
			emulate_split_set_clr(ff);
			return;
		}
		legalize_finish(ff);
	}

	void legalize_rlatch(FfData &ff) {
		if (!try_flip(ff, supported_rlatch)) {
			if (!supported_dlatch)
				fail_ff(ff, "D latches are not supported");
			else
				fail_ff(ff, "initialized D latches are not supported");
		}

		int initmask = get_initmask(ff);
		if (((supported_dlatch_plain & 7) * 0x111) & initmask) {
			ff.arst_to_aload();
			legalize_dlatch(ff);
		} else if (supported_sr & initmask) {
			ff.arst_to_sr();
			legalize_sr(ff);
		} else if (supported_adff & initmask) {
			ff.add_dummy_clk();
			legalize_adff(ff);
		} else {
			log_assert(0);
		}
	}

	void legalize_sr(FfData &ff) {
		if (!try_flip(ff, supported_sr)) {
			if (!supported_sr)
				fail_ff(ff, "sr latches are not supported");
			else
				fail_ff(ff, "initialized sr latches are not supported");
		}
		int initmask = get_initmask(ff);
		if (supported_cells[FF_SR] & initmask) {
			// OK
		} else if (supported_cells[FF_DLATCHSR] & initmask) {
			// Upgrade to DLATCHSR.
			ff.add_dummy_aload();
		} else if (supported_cells[FF_DFFSR] & initmask) {
			// Upgrade to DFFSR.
			ff.add_dummy_clk();
		} else if (supported_cells[FF_DFFSRE] & initmask) {
			// Upgrade to DFFSRE.
			ff.add_dummy_clk();
			ff.add_dummy_ce();
		} else if (supported_cells[FF_ADLATCH] & (initmask << 4)) {
			ff.has_sr = false;
			ff.has_aload = true;
			ff.has_arst = true;
			ff.pol_arst = ff.pol_clr;
			ff.sig_arst = ff.sig_clr;
			ff.sig_aload = ff.sig_set;
			ff.pol_aload = ff.pol_set;
			ff.sig_ad = State::S1;
			ff.val_arst = State::S0;
		} else if (supported_cells[FF_ADLATCH] & (flip_initmask(initmask) << 8)) {
			ff.has_sr = false;
			ff.has_aload = true;
			ff.has_arst = true;
			ff.pol_arst = ff.pol_clr;
			ff.sig_arst = ff.sig_clr;
			ff.sig_aload = ff.sig_set;
			ff.pol_aload = ff.pol_set;
			ff.sig_ad = State::S0;
			ff.val_arst = State::S1;
			ff.remove_init();
			Wire *new_q = ff.module->addWire(NEW_ID);
			if (ff.is_fine)
				ff.module->addNotGate(NEW_ID, new_q, ff.sig_q);
			else
				ff.module->addNot(NEW_ID, new_q, ff.sig_q);
			ff.sig_q = new_q;
			if (ff.val_init == State::S0)
				ff.val_init = State::S1;
			else if (ff.val_init == State::S1)
				ff.val_init = State::S0;
		} else {
			log_assert(0);
		}
		legalize_finish(ff);
	}

	void fixup_reset_x(FfData &ff, int supported) {
		for (int i = 0; i < ff.width; i++) {
			int mask;
			if (ff.val_init[i] == State::S0)
				mask = INIT_0;
			else if (ff.val_init[i] == State::S1)
				mask = INIT_1;
			else
				mask = INIT_X;
			if (ff.has_arst) {
				if (ff.val_arst[i] == State::Sx) {
					if (!(supported & (mask << 8)))
						ff.val_arst.bits()[i] = State::S0;
					if (!(supported & (mask << 4)))
						ff.val_arst.bits()[i] = State::S1;
				}
			}
			if (ff.has_srst) {
				if (ff.val_srst[i] == State::Sx) {
					if (!(supported & (mask << 8)))
						ff.val_srst.bits()[i] = State::S0;
					if (!(supported & (mask << 4)))
						ff.val_srst.bits()[i] = State::S1;
				}
			}
		}
	}

	void legalize_ff(FfData &ff) {
		if (ff.has_gclk)
			return;

		// TODO: consider supporting coarse as well.
		if (!ff.is_fine)
			return;

		if (mince && ff.has_ce && ff.sig_ce[0].wire && ce_used[ff.sig_ce[0]] < mince)
			ff.unmap_ce();
		if (minsrst && ff.has_srst && ff.sig_srst[0].wire && srst_used[ff.sig_srst[0]] < minsrst)
			ff.unmap_srst();

		if (ff.has_clk) {
			if (ff.has_sr) {
				legalize_dffsr(ff);
			} else if (ff.has_aload) {
				legalize_aldff(ff);
			} else if (ff.has_arst) {
				legalize_adff(ff);
			} else if (ff.has_srst) {
				if (ff.has_ce && ff.ce_over_srst)
					legalize_sdffce(ff);
				else
					legalize_sdff(ff);
			} else {
				legalize_dff(ff);
			}
		} else if (ff.has_aload) {
			if (ff.has_sr) {
				legalize_dlatchsr(ff);
			} else if (ff.has_arst) {
				legalize_adlatch(ff);
			} else {
				legalize_dlatch(ff);
			}
		} else {
			if (ff.has_sr) {
				legalize_sr(ff);
			} else if (ff.has_arst) {
				legalize_rlatch(ff);
			} else {
				log_assert(0);
			}
		}
	}

	void flip_pol(FfData &ff, SigSpec &sig, bool &pol) {
		if (sig == State::S0) {
			sig = State::S1;
		} else if (sig == State::S1) {
			sig = State::S0;
		} else if (ff.is_fine) {
			sig = ff.module->NotGate(NEW_ID, sig);
		} else {
			sig = ff.module->Not(NEW_ID, sig);
		}
		pol = !pol;
	}

	void legalize_finish(FfData &ff) {
		int ff_type = get_ff_type(ff);
		int initmask = get_initmask(ff);
		log_assert(supported_cells[ff_type] & initmask);
		int ff_neg = 0;
		if (ff.has_sr) {
			if (!ff.pol_clr)
				ff_neg |= NEG_R;
			if (!ff.pol_set)
				ff_neg |= NEG_S;
		}
		if (ff.has_arst) {
			if (!ff.pol_arst)
				ff_neg |= NEG_R;
		}
		if (ff.has_srst) {
			if (!ff.pol_srst)
				ff_neg |= NEG_R;
		}
		if (ff.has_aload) {
			if (!ff.pol_aload)
				ff_neg |= NEG_L;
		}
		if (ff.has_clk) {
			if (!ff.pol_clk)
				ff_neg |= NEG_C;
		}
		if (ff.has_ce) {
			if (!ff.pol_ce)
				ff_neg |= NEG_CE;
		}
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
			if (xneg & NEG_CE)
				flip_pol(ff, ff.sig_ce, ff.pol_ce);
			if (ff.has_sr) {
				if (xneg & NEG_R)
					flip_pol(ff, ff.sig_clr, ff.pol_clr);
				if (xneg & NEG_S)
					flip_pol(ff, ff.sig_set, ff.pol_set);
			}
			if (ff.has_arst && xneg & NEG_R)
				flip_pol(ff, ff.sig_arst, ff.pol_arst);
			if (ff.has_srst && xneg & NEG_R)
				flip_pol(ff, ff.sig_srst, ff.pol_srst);
			if (xneg & NEG_L)
				flip_pol(ff, ff.sig_aload, ff.pol_aload);
			if (xneg & NEG_C)
				flip_pol(ff, ff.sig_clk, ff.pol_clk);
			ff_neg ^= xneg;
		}

		fixup_reset_x(ff, supported_cells_neg[ff_type][ff_neg]);
		ff.emit();
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{

		log_header(design, "Executing DFFLEGALIZE pass (convert FFs to types supported by the target).\n");

		for (int i = 0; i < NUM_FFTYPES; i++) {
			for (int j = 0; j < NUM_NEG; j++)
				supported_cells_neg[i][j] = 0;
			supported_cells[i] = 0;
		}
		mince = design->scratchpad_get_int("dfflegalize.mince", 0);
		minsrst = design->scratchpad_get_int("dfflegalize.minsrst", 0);

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-cell" && argidx + 2 < args.size()) {
				std::string celltype = args[++argidx];
				std::string inittype = args[++argidx];
				enum FfType ff_type;
				char pol_c = 0;
				char pol_l = 0;
				char pol_s = 0;
				char pol_r = 0;
				char pol_ce = 0;
				char srval = 0;
				if (celltype.substr(0, 5) == "$_SR_" && celltype.size() == 8 && celltype[7] == '_') {
					ff_type = FF_SR;
					pol_s = celltype[5];
					pol_r = celltype[6];
				} else if (celltype.substr(0, 6) == "$_DFF_" && celltype.size() == 8 && celltype[7] == '_') {
					ff_type = FF_DFF;
					pol_c = celltype[6];
				} else if (celltype.substr(0, 7) == "$_DFFE_" && celltype.size() == 10 && celltype[9] == '_') {
					ff_type = FF_DFFE;
					pol_c = celltype[7];
					pol_ce = celltype[8];
				} else if (celltype.substr(0, 6) == "$_DFF_" && celltype.size() == 10 && celltype[9] == '_') {
					ff_type = FF_ADFF;
					pol_c = celltype[6];
					pol_r = celltype[7];
					srval = celltype[8];
				} else if (celltype.substr(0, 7) == "$_DFFE_" && celltype.size() == 12 && celltype[11] == '_') {
					ff_type = FF_ADFFE;
					pol_c = celltype[7];
					pol_r = celltype[8];
					srval = celltype[9];
					pol_ce = celltype[10];
				} else if (celltype.substr(0, 8) == "$_ALDFF_" && celltype.size() == 11 && celltype[10] == '_') {
					ff_type = FF_ALDFF;
					pol_c = celltype[8];
					pol_l = celltype[9];
				} else if (celltype.substr(0, 9) == "$_ALDFFE_" && celltype.size() == 13 && celltype[12] == '_') {
					ff_type = FF_ALDFFE;
					pol_c = celltype[9];
					pol_l = celltype[10];
					pol_ce = celltype[11];
				} else if (celltype.substr(0, 8) == "$_DFFSR_" && celltype.size() == 12 && celltype[11] == '_') {
					ff_type = FF_DFFSR;
					pol_c = celltype[8];
					pol_s = celltype[9];
					pol_r = celltype[10];
				} else if (celltype.substr(0, 9) == "$_DFFSRE_" && celltype.size() == 14 && celltype[13] == '_') {
					ff_type = FF_DFFSRE;
					pol_c = celltype[9];
					pol_s = celltype[10];
					pol_r = celltype[11];
					pol_ce = celltype[12];
				} else if (celltype.substr(0, 7) == "$_SDFF_" && celltype.size() == 11 && celltype[10] == '_') {
					ff_type = FF_SDFF;
					pol_c = celltype[7];
					pol_r = celltype[8];
					srval = celltype[9];
				} else if (celltype.substr(0, 8) == "$_SDFFE_" && celltype.size() == 13 && celltype[12] == '_') {
					ff_type = FF_SDFFE;
					pol_c = celltype[8];
					pol_r = celltype[9];
					srval = celltype[10];
					pol_ce = celltype[11];
				} else if (celltype.substr(0, 9) == "$_SDFFCE_" && celltype.size() == 14 && celltype[13] == '_') {
					ff_type = FF_SDFFCE;
					pol_c = celltype[9];
					pol_r = celltype[10];
					srval = celltype[11];
					pol_ce = celltype[12];
				} else if (celltype.substr(0, 9) == "$_DLATCH_" && celltype.size() == 11 && celltype[10] == '_') {
					ff_type = FF_DLATCH;
					pol_l = celltype[9];
				} else if (celltype.substr(0, 9) == "$_DLATCH_" && celltype.size() == 13 && celltype[12] == '_') {
					ff_type = FF_ADLATCH;
					pol_l = celltype[9];
					pol_r = celltype[10];
					srval = celltype[11];
				} else if (celltype.substr(0, 11) == "$_DLATCHSR_" && celltype.size() == 15 && celltype[14] == '_') {
					ff_type = FF_DLATCHSR;
					pol_l = celltype[11];
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
					std::make_pair(pol_l, NEG_L),
					std::make_pair(pol_s, NEG_S),
					std::make_pair(pol_r, NEG_R),
					std::make_pair(pol_ce, NEG_CE),
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
				int initmask;
				if (inittype == "x") {
					initmask = 0x111;
				} else if (inittype == "0") {
					initmask = 0x333;
				} else if (inittype == "1") {
					initmask = 0x555;
				} else if (inittype == "r") {
					if (srval == 0)
						log_error("init type r not valid for cell type %s.\n", celltype.c_str());
					initmask = 0x537;
				} else if (inittype == "01") {
					initmask = 0x777;
				} else {
					log_error("unrecognized init type %s for cell type %s.\n", inittype.c_str(), celltype.c_str());
				}
				if (srval == '0') {
					initmask &= 0x0ff;
				} else if (srval == '1') {
					initmask &= 0xf0f;
				} else if (srval != 0 && srval != '?') {
					goto unrecognized;
				}
				for (int neg = 0; neg < NUM_NEG; neg++)
					if ((neg & mask) == match)
						supported_cells_neg[ff_type][neg] |= initmask;
				supported_cells[ff_type] |= initmask;
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
		supported_aldff = supported_cells[FF_ALDFF] | supported_cells[FF_ALDFFE] | supported_dffsr;
		supported_aldffe = supported_cells[FF_ALDFFE] | supported_cells[FF_DFFSRE];
		supported_adff = supported_cells[FF_ADFF] | supported_cells[FF_ADFFE] | supported_dffsr | supported_aldff;
		supported_adffe = supported_cells[FF_ADFFE] | supported_cells[FF_ALDFFE] | supported_cells[FF_DFFSRE];
		supported_sdff = supported_cells[FF_SDFF] | supported_cells[FF_SDFFE] | supported_cells[FF_SDFFCE];
		supported_dff = supported_cells[FF_DFF] | supported_cells[FF_DFFE] | supported_adff | supported_sdff;
		supported_dffe = supported_cells[FF_DFFE] | supported_cells[FF_DFFSRE] | supported_cells[FF_ALDFFE] | supported_cells[FF_ADFFE] | supported_cells[FF_SDFFE] | supported_cells[FF_SDFFCE];
		supported_sr_plain = supported_dffsr | supported_cells[FF_DLATCHSR] | supported_cells[FF_SR];
		supported_sr = supported_sr_plain;
		supported_sr |= (supported_cells[FF_ADLATCH] >> 4 & 7) * 0x111;
		supported_sr |= (flip_initmask(supported_cells[FF_ADLATCH]) >> 4 & 7) * 0x111;
		supported_dlatch_plain = supported_cells[FF_DLATCH] | supported_cells[FF_ADLATCH] | supported_cells[FF_DLATCHSR] | supported_cells[FF_ALDFF] | supported_cells[FF_ALDFFE];
		supported_dlatch = supported_dlatch_plain | supported_sr_plain;
		supported_rlatch = supported_adff | (supported_dlatch & 7) * 0x111;
		supported_adlatch = supported_cells[FF_ADLATCH] | supported_cells[FF_DLATCHSR];

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

					FfData ff(&initvals, cell);
					if (ff.has_ce && ff.sig_ce[0].wire)
						ce_used[ff.sig_ce[0]] += ff.width;
					if (ff.has_srst && ff.sig_srst[0].wire)
						srst_used[ff.sig_srst[0]] += ff.width;
				}
			}
			for (auto cell : module->selected_cells())
			{
				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;
				FfData ff(&initvals, cell);
				legalize_ff(ff);
			}
		}

		sigmap.clear();
		initvals.clear();
		ce_used.clear();
		srst_used.clear();
	}
} DffLegalizePass;

PRIVATE_NAMESPACE_END
