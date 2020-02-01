/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

typedef std::pair<Const, std::vector<SigBit>> LutData;

// Compute a LUT implementing (select ^ select_inv) ? alt_data : data.  Returns true if successful.
bool merge_lut(LutData &result, const LutData &data, const LutData select, bool select_inv, SigBit alt_data, int max_lut_size) {
	// First, gather input signals -- insert new signals at the beginning
	// of the vector, so they don't disturb the likely-critical D LUT input
	// timings.
	result.second = data.second;
	// D lut inputs initially start at 0.
	int idx_data = 0;
	// Now add the control input LUT inputs.
	std::vector<int> idx_sel;
	for (auto bit : select.second) {
		int idx = -1;
		for (int i = 0; i < GetSize(result.second); i++)
			if (result.second[i] == bit)
				idx = i;
		if (idx == -1) {
			idx = 0;
			// Insert new signal at the beginning and bump all indices.
			result.second.insert(result.second.begin(), bit);
			idx_data++;
			for (int &sidx : idx_sel)
				sidx++;
		}
		idx_sel.push_back(idx);
	}
	// Insert the Q signal, if any, to the slowest input -- it will have
	// no problem meeting timing.
	int idx_alt = -1;
	if (alt_data.wire) {
		// Check if we already have it.
		for (int i = 0; i < GetSize(result.second); i++)
			if (result.second[i] == alt_data)
				idx_alt = i;
		// If not, add it.
		if (idx_alt == -1) {
			idx_alt = 0;
			result.second.insert(result.second.begin(), alt_data);
			idx_data++;
			for (int &sidx : idx_sel)
				sidx++;
		}
	}

	// If LUT would be too large, bail.
	if (GetSize(result.second) > max_lut_size)
		return false;

	// Okay, we're doing it — compute the LUT mask.
	result.first = Const(0, 1 << GetSize(result.second));
	for (int i = 0; i < GetSize(result.first); i++) {
		int sel_lut_idx = 0;
		for (int j = 0; j < GetSize(select.second); j++)
			if (i & 1 << idx_sel[j])
				sel_lut_idx |= 1 << j;
		bool select_val = (select.first.bits[sel_lut_idx] == State::S1);
		bool new_bit;
		if (select_val ^ select_inv) {
			// Use alt_data.
			if (alt_data.wire)
				new_bit = (i & 1 << idx_alt) != 0;
			else
				new_bit = alt_data.data == State::S1;
		} else {
			// Use original LUT.
			int lut_idx = i >> idx_data & ((1 << GetSize(data.second)) - 1);
			new_bit = data.first.bits[lut_idx] == State::S1;
		}
		result.first.bits[i] = new_bit ? State::S1 : State::S0;
	}
	return true;
}

struct XilinxDffOptPass : public Pass {
	XilinxDffOptPass() : Pass("xilinx_dffopt", "Xilinx: optimize FF control signal usage") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_dffopt [options] [selection]\n");
		log("\n");
		log("Converts hardware clock enable and set/reset signals on FFs to emulation\n");
		log("using LUTs, if doing so would improve area.  Operates on post-techmap Xilinx\n");
		log("cells (LUT*, FD*).\n");
		log("\n");
		log("    -lut4\n");
		log("        Assume a LUT4-based device (instead of a LUT6-based device).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing XILINX_DFFOPT pass (optimize FF control signal usage).\n");

		size_t argidx;
		int max_lut_size = 6;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-lut4") {
				max_lut_size = 4;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			log("Optimizing FFs in %s.\n", log_id(module));

			SigMap sigmap(module);
			dict<SigBit, pair<LutData, Cell *>> bit_to_lut;
			dict<SigBit, int> bit_uses;

			// Gather LUTs.
			for (auto cell : module->selected_cells())
			{
				for (auto port : cell->connections())
					for (auto bit : port.second)
						bit_uses[sigmap(bit)]++;
				if (cell->get_bool_attribute(ID::keep))
					continue;
				if (cell->type == ID(INV)) {
					SigBit sigout = sigmap(cell->getPort(ID(O)));
					SigBit sigin = sigmap(cell->getPort(ID(I)));
					bit_to_lut[sigout] = make_pair(LutData(Const(1, 2), {sigin}), cell);
				} else if (cell->type.in(ID(LUT1), ID(LUT2), ID(LUT3), ID(LUT4), ID(LUT5), ID(LUT6))) {
					SigBit sigout = sigmap(cell->getPort(ID(O)));
					const Const &init = cell->getParam(ID(INIT));
					std::vector<SigBit> sigin;
					sigin.push_back(sigmap(cell->getPort(ID(I0))));
					if (cell->type == ID(LUT1))
						goto lut_sigin_done;
					sigin.push_back(sigmap(cell->getPort(ID(I1))));
					if (cell->type == ID(LUT2))
						goto lut_sigin_done;
					sigin.push_back(sigmap(cell->getPort(ID(I2))));
					if (cell->type == ID(LUT3))
						goto lut_sigin_done;
					sigin.push_back(sigmap(cell->getPort(ID(I3))));
					if (cell->type == ID(LUT4))
						goto lut_sigin_done;
					sigin.push_back(sigmap(cell->getPort(ID(I4))));
					if (cell->type == ID(LUT5))
						goto lut_sigin_done;
					sigin.push_back(sigmap(cell->getPort(ID(I5))));
lut_sigin_done:
					bit_to_lut[sigout] = make_pair(LutData(init, sigin), cell);
				}
			}
			for (auto wire : module->wires())
				if (wire->port_output || wire->port_input)
					for (int i = 0; i < GetSize(wire); i++)
						bit_uses[sigmap(SigBit(wire, i))]++;

			// Iterate through FFs.
			for (auto cell : module->selected_cells())
			{
				bool has_s = false, has_r = false;
				if (cell->type.in(ID(FDCE), ID(FDPE), ID(FDCPE), ID(FDCE_1), ID(FDPE_1), ID(FDCPE_1))) {
					// Async reset.
				} else if (cell->type.in(ID(FDRE), ID(FDRE_1))) {
					has_r = true;
				} else if (cell->type.in(ID(FDSE), ID(FDSE_1))) {
					has_s = true;
				} else if (cell->type.in(ID(FDRSE), ID(FDRSE_1))) {
					has_r = true;
					has_s = true;
				} else {
					// Not a FF.
					continue;
				}
				if (cell->get_bool_attribute(ID::keep))
					continue;

				// Don't bother if D has more than one use.
				SigBit sig_D = sigmap(cell->getPort(ID(D)));
				if (bit_uses[sig_D] > 2)
					continue;

				// Find the D LUT.
				auto it_D = bit_to_lut.find(sig_D);
				if (it_D == bit_to_lut.end())
					continue;
				LutData lut_d = it_D->second.first;
				Cell *cell_d = it_D->second.second;
				if (cell->hasParam(ID(IS_D_INVERTED)) && cell->getParam(ID(IS_D_INVERTED)).as_bool()) {
					// Flip all bits in the LUT.
					for (int i = 0; i < GetSize(lut_d.first); i++)
						lut_d.first.bits[i] = (lut_d.first.bits[i] == State::S1) ? State::S0 : State::S1;
				}

				LutData lut_d_post_ce;
				LutData lut_d_post_s;
				LutData lut_d_post_r;
				bool worthy_post_ce = false;
				bool worthy_post_s = false;
				bool worthy_post_r = false;

				// First, unmap CE.
				SigBit sig_Q = sigmap(cell->getPort(ID(Q)));
				SigBit sig_CE = sigmap(cell->getPort(ID(CE)));
				LutData lut_ce = LutData(Const(2, 2), {sig_CE});
				auto it_CE = bit_to_lut.find(sig_CE);
				if (it_CE != bit_to_lut.end())
					lut_ce = it_CE->second.first;
				if (sig_CE.wire) {
					// Merge CE LUT and D LUT into one.  If it cannot be done, nothing to do about this FF.
					if (!merge_lut(lut_d_post_ce, lut_d, lut_ce, true, sig_Q, max_lut_size))
						continue;

					// If this gets rid of a CE LUT, it's worth it.  If not, it still may be worth it, if we can remove set/reset as well.
					if (it_CE != bit_to_lut.end())
						worthy_post_ce = true;
				} else if (sig_CE.data != State::S1) {
					// Strange.  Should not happen in a reasonable flow, so bail.
					continue;
				} else {
					lut_d_post_ce = lut_d;
				}

				// Second, unmap S, if any.
				lut_d_post_s = lut_d_post_ce;
				if (has_s) {
					SigBit sig_S = sigmap(cell->getPort(ID(S)));
					LutData lut_s = LutData(Const(2, 2), {sig_S});
					bool inv_s = cell->hasParam(ID(IS_S_INVERTED)) && cell->getParam(ID(IS_S_INVERTED)).as_bool();
					auto it_S = bit_to_lut.find(sig_S);
					if (it_S != bit_to_lut.end())
						lut_s = it_S->second.first;
					if (sig_S.wire) {
						// Merge S LUT and D LUT into one.  If it cannot be done, try to at least merge CE.
						if (!merge_lut(lut_d_post_s, lut_d_post_ce, lut_s, inv_s, SigBit(State::S1), max_lut_size))
							goto unmap;
						// If this gets rid of an S LUT, it's worth it.
						if (it_S != bit_to_lut.end())
							worthy_post_s = true;
					} else if (sig_S.data != (inv_s ? State::S1 : State::S0)) {
						// Strange.  Should not happen in a reasonable flow, so bail.
						continue;
					}
				}

				// Third, unmap R, if any.
				lut_d_post_r = lut_d_post_s;
				if (has_r) {
					SigBit sig_R = sigmap(cell->getPort(ID(R)));
					LutData lut_r = LutData(Const(2, 2), {sig_R});
					bool inv_r = cell->hasParam(ID(IS_R_INVERTED)) && cell->getParam(ID(IS_R_INVERTED)).as_bool();
					auto it_R = bit_to_lut.find(sig_R);
					if (it_R != bit_to_lut.end())
						lut_r = it_R->second.first;
					if (sig_R.wire) {
						// Merge R LUT and D LUT into one.  If it cannot be done, try to at least merge CE/S.
						if (!merge_lut(lut_d_post_r, lut_d_post_s, lut_r, inv_r, SigBit(State::S0), max_lut_size))
							goto unmap;
						// If this gets rid of an S LUT, it's worth it.
						if (it_R != bit_to_lut.end())
							worthy_post_r = true;
					} else if (sig_R.data != (inv_r ? State::S1 : State::S0)) {
						// Strange.  Should not happen in a reasonable flow, so bail.
						continue;
					}
				}

unmap:
				LutData final_lut;
				if (worthy_post_r) {
					final_lut = lut_d_post_r;
					log("  Merging R LUT for %s/%s (%d -> %d)\n", log_id(cell), log_id(sig_Q.wire), GetSize(lut_d.second), GetSize(final_lut.second));
				} else if (worthy_post_s) {
					final_lut = lut_d_post_s;
					log("  Merging S LUT for %s/%s (%d -> %d)\n", log_id(cell), log_id(sig_Q.wire), GetSize(lut_d.second), GetSize(final_lut.second));
				} else if (worthy_post_ce) {
					final_lut = lut_d_post_ce;
					log("  Merging CE LUT for %s/%s (%d -> %d)\n", log_id(cell), log_id(sig_Q.wire), GetSize(lut_d.second), GetSize(final_lut.second));
				} else {
					// Nothing to do here.
					continue;
				}

				// Okay, we're doing it.  Unmap ports.
				if (worthy_post_r) {
					cell->unsetParam(ID(IS_R_INVERTED));
					cell->setPort(ID(R), Const(0, 1));
				}
				if (has_s && (worthy_post_r || worthy_post_s)) {
					cell->unsetParam(ID(IS_S_INVERTED));
					cell->setPort(ID(S), Const(0, 1));
				}
				cell->setPort(ID(CE), Const(1, 1));
				cell->unsetParam(ID(IS_D_INVERTED));

				// Create the new LUT.
				Cell *lut_cell = 0;
				switch (GetSize(final_lut.second)) {
					case 1:
						lut_cell = module->addCell(NEW_ID, ID(LUT1));
						break;
					case 2:
						lut_cell = module->addCell(NEW_ID, ID(LUT2));
						break;
					case 3:
						lut_cell = module->addCell(NEW_ID, ID(LUT3));
						break;
					case 4:
						lut_cell = module->addCell(NEW_ID, ID(LUT4));
						break;
					case 5:
						lut_cell = module->addCell(NEW_ID, ID(LUT5));
						break;
					case 6:
						lut_cell = module->addCell(NEW_ID, ID(LUT6));
						break;
					default:
						log_assert(!"unknown lut size");
				}
				lut_cell->attributes = cell_d->attributes;
				Wire *lut_out = module->addWire(NEW_ID);
				lut_cell->setParam(ID(INIT), final_lut.first);
				cell->setPort(ID(D), lut_out);
				lut_cell->setPort(ID(O), lut_out);
				lut_cell->setPort(ID(I0), final_lut.second[0]);
				if (GetSize(final_lut.second) >= 2)
					lut_cell->setPort(ID(I1), final_lut.second[1]);
				if (GetSize(final_lut.second) >= 3)
					lut_cell->setPort(ID(I2), final_lut.second[2]);
				if (GetSize(final_lut.second) >= 4)
					lut_cell->setPort(ID(I3), final_lut.second[3]);
				if (GetSize(final_lut.second) >= 5)
					lut_cell->setPort(ID(I4), final_lut.second[4]);
				if (GetSize(final_lut.second) >= 6)
					lut_cell->setPort(ID(I5), final_lut.second[5]);
			}
		}
	}
} XilinxDffOptPass;

PRIVATE_NAMESPACE_END

