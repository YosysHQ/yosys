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

struct Pmux2ShiftxPass : public Pass {
	Pmux2ShiftxPass() : Pass("pmux2shiftx", "transform $pmux cells to $shiftx cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    pmux2shiftx [options] [selection]\n");
		log("\n");
		log("This pass transforms $pmux cells to $shiftx cells.\n");
		log("\n");
		log("    -density non_offset_percentage offset_percentage\n");
		log("        specifies the minimum density for non_offset- and for offset-mode\n");
		log("        default values are 30 (non-offset) and 50 (offset)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		int non_offset_percentage = 30;
		int offset_percentage = 50;

		log_header(design, "Executing PMUX2SHIFTX pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-density" && argidx+2 < args.size()) {
				non_offset_percentage = atoi(args[++argidx].c_str());
				offset_percentage = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);

			dict<SigBit, pair<SigSpec, Const>> eqdb;

			for (auto cell : module->selected_cells())
			{
				if (cell->type == "$eq")
				{
					dict<SigBit, State> bits;

					SigSpec A = sigmap(cell->getPort("\\A"));
					SigSpec B = sigmap(cell->getPort("\\B"));

					int a_width = cell->getParam("\\A_WIDTH").as_int();
					int b_width = cell->getParam("\\B_WIDTH").as_int();

					if (a_width < b_width) {
						bool a_signed = cell->getParam("\\A_SIGNED").as_int();
						A.extend_u0(b_width, a_signed);
					}

					if (b_width < a_width) {
						bool b_signed = cell->getParam("\\B_SIGNED").as_int();
						B.extend_u0(a_width, b_signed);
					}

					for (int i = 0; i < GetSize(A); i++) {
						SigBit a_bit = A[i], b_bit = B[i];
						if (b_bit.wire && !a_bit.wire) {
							std::swap(a_bit, b_bit);
						}
						if (!a_bit.wire || b_bit.wire)
							goto next_cell;
						if (bits.count(a_bit))
							goto next_cell;
						bits[a_bit] = b_bit.data;
					}

					if (GetSize(bits) > 20)
						goto next_cell;

					bits.sort();
					pair<SigSpec, Const> entry;

					for (auto it : bits) {
						entry.first.append_bit(it.first);
						entry.second.bits.push_back(it.second);
					}

					eqdb[sigmap(cell->getPort("\\Y")[0])] = entry;
					goto next_cell;
				}

				if (cell->type == "$logic_not")
				{
					dict<SigBit, State> bits;

					SigSpec A = sigmap(cell->getPort("\\A"));

					for (int i = 0; i < GetSize(A); i++)
						bits[A[i]] = State::S0;

					bits.sort();
					pair<SigSpec, Const> entry;

					for (auto it : bits) {
						entry.first.append_bit(it.first);
						entry.second.bits.push_back(it.second);
					}

					eqdb[sigmap(cell->getPort("\\Y")[0])] = entry;
					goto next_cell;
				}
		next_cell:;
			}

			for (auto cell : module->selected_cells())
			{
				if (cell->type != "$pmux")
					continue;

				string src = cell->get_src_attribute();
				int width = cell->getParam("\\WIDTH").as_int();
				int width_bits = ceil_log2(width);
				int extwidth = width;

				while (extwidth & (extwidth-1))
					extwidth++;

				dict<SigSpec, pool<int>> seldb;

				SigSpec B = cell->getPort("\\B");
				SigSpec S = sigmap(cell->getPort("\\S"));
				for (int i = 0; i < GetSize(S); i++)
				{
					if (!eqdb.count(S[i]))
						continue;

					auto &entry = eqdb.at(S[i]);
					seldb[entry.first].insert(i);
				}

				if (seldb.empty())
					continue;

				log("Inspecting $pmux cell %s/%s.\n", log_id(module), log_id(cell));
				log("  data width: %d (next power-of-2 = %d, log2 = %d)\n", width, extwidth, width_bits);

				SigSpec updated_S = cell->getPort("\\S");
				SigSpec updated_B = cell->getPort("\\B");

				while (!seldb.empty())
				{
					// pick the largest entry in seldb
					SigSpec sig = seldb.begin()->first;
					for (auto &it : seldb) {
						if (GetSize(sig) < GetSize(it.first))
							sig = it.first;
						else if (GetSize(seldb.at(sig)) < GetSize(it.second))
							sig = it.first;
					}

					log("  checking ctrl signal %s\n", log_signal(sig));

					// find the relevant choices
					dict<Const, int> choices;
					for (int i : seldb.at(sig)) {
						Const val = eqdb.at(S[i]).second;
						choices[val] = i;
					}

					// TBD: also find choices that are using signals that are subsets of the bits in "sig"

					// find the best permutation
					vector<int> perm_new_from_old(GetSize(sig));
					Const perm_xormask(State::S0, GetSize(sig));
					{
						vector<int> values(GetSize(choices));
						vector<bool> used_src_columns(GetSize(sig));
						vector<vector<bool>> columns(GetSize(sig), vector<bool>(GetSize(values)));

						for (int i = 0; i < GetSize(choices); i++) {
							Const val = choices.element(i)->first;
							for (int k = 0; k < GetSize(val); k++)
								if (val[k] == State::S1)
									columns[k][i] = true;
						}

						for (int dst_col = GetSize(sig)-1; dst_col >= 0; dst_col--)
						{
							int best_src_col = -1;
							bool best_inv = false;
							int best_maxval = 0;
							int best_delta = 0;

							// find best src colum for this dst column
							for (int src_col = 0; src_col < GetSize(sig); src_col++)
							{
								if (used_src_columns[src_col])
									continue;

								int this_maxval = 0;
								int this_minval = 1 << 30;

								int this_inv_maxval = 0;
								int this_inv_minval = 1 << 30;

								for (int i = 0; i < GetSize(values); i++)
								{
									int val = values[i];
									int inv_val = val;

									if (columns[src_col][i])
										val |= 1 << dst_col;
									else
										inv_val |= 1 << dst_col;

									this_maxval = std::max(this_maxval, val);
									this_minval = std::min(this_minval, val);

									this_inv_maxval = std::max(this_inv_maxval, inv_val);
									this_inv_minval = std::min(this_inv_minval, inv_val);
								}

								int this_delta = this_maxval - this_minval;
								int this_inv_delta = this_maxval - this_minval;
								bool this_inv = false;

								if (this_delta != this_inv_delta)
									this_inv = this_inv_delta < this_delta;
								else if (this_maxval != this_inv_maxval)
									this_inv = this_inv_maxval < this_maxval;

								if (this_inv) {
									this_delta = this_inv_delta;
									this_maxval = this_inv_maxval;
									this_minval = this_inv_minval;
								}

								bool this_is_better = false;

								if (best_src_col < 0)
									this_is_better = true;
								else if (this_delta != best_delta)
									this_is_better = this_delta < best_delta;
								else if (this_maxval != best_maxval)
									this_is_better = this_maxval < best_maxval;
								else
									this_is_better = sig[best_src_col] < sig[src_col];

								if (this_is_better) {
									best_src_col = src_col;
									best_inv = this_inv;
									best_maxval = this_maxval;
									best_delta = this_delta;
								}
							}

							used_src_columns[best_src_col] = true;
							perm_new_from_old[dst_col] = best_src_col;
							perm_xormask[dst_col] = best_inv ? State::S1 : State::S0;
						}
					}

					// permutated sig
					SigSpec perm_sig(State::S0, GetSize(sig));
					for (int i = 0; i < GetSize(sig); i++)
						perm_sig[i] = sig[perm_new_from_old[i]];

					log("    best permutation: %s\n", log_signal(perm_sig));
					log("    best xor mask: %s\n", log_signal(perm_xormask));

					// permutated choices
					int min_choice = 1 << 30;
					int max_choice = -1;
					dict<Const, int> perm_choices;

					for (auto &it : choices)
					{
						Const &old_c = it.first;
						Const new_c(State::S0, GetSize(old_c));

						for (int i = 0; i < GetSize(old_c); i++)
							new_c[i] = old_c[perm_new_from_old[i]];

						Const new_c_before_xor = new_c;
						new_c = const_xor(new_c, perm_xormask, false, false, GetSize(new_c));

						perm_choices[new_c] = it.second;

						min_choice = std::min(min_choice, new_c.as_int());
						max_choice = std::max(max_choice, new_c.as_int());

						log("    %3d: %s -> %s -> %s: %s\n", it.second, log_signal(old_c), log_signal(new_c_before_xor),
								log_signal(new_c), log_signal(B.extract(it.second*width, width)));
					}

					int range_density = 100*GetSize(choices) / (max_choice-min_choice+1);
					int absolute_density = 100*GetSize(choices) / (max_choice+1);

					log("    choices: %d\n", GetSize(choices));
					log("    min choice: %d\n", min_choice);
					log("    max choice: %d\n", max_choice);
					log("    range density: %d%%\n", range_density);
					log("    absolute density: %d%%\n", absolute_density);

					bool full_case = (min_choice == 0) && (max_choice == (1 << GetSize(sig))-1) && (max_choice+1 == GetSize(choices));
					log("    full case: %s\n", full_case ? "true" : "false");

					// check density percentages
					Const offset(State::S0, GetSize(sig));
					if (absolute_density < non_offset_percentage && range_density >= offset_percentage)
					{
						offset = Const(min_choice, GetSize(sig));
						log("    offset: %s\n", log_signal(offset));

						min_choice -= offset.as_int();
						max_choice -= offset.as_int();

						dict<Const, int> new_perm_choices;
						for (auto &it : perm_choices)
							new_perm_choices[const_sub(it.first, offset, false, false, GetSize(sig))] = it.second;
						perm_choices.swap(new_perm_choices);
					} else
					if (absolute_density < non_offset_percentage) {
						log("    insufficient density.\n");
						seldb.erase(sig);
						continue;
					}

					// creat cmp signal
					SigSpec cmp = perm_sig;
					if (perm_xormask.as_bool())
						cmp = module->Xor(NEW_ID, cmp, perm_xormask, false, src);
					if (offset.as_bool())
						cmp = module->Sub(NEW_ID, cmp, offset, false, src);

					// create enable signal
					SigBit en = State::S1;
					if (!full_case) {
						Const enable_mask(State::S0, max_choice+1);
						for (auto &it : perm_choices)
							enable_mask[it.first.as_int()] = State::S1;
						en = module->addWire(NEW_ID);
						module->addShift(NEW_ID, enable_mask, cmp, en, false, src);
					}

					// create data signal
					SigSpec data(State::Sx, (max_choice+1)*extwidth);
					for (auto &it : perm_choices) {
						int position = it.first.as_int()*extwidth;
						int data_index = it.second;
						data.replace(position, B.extract(data_index*width, width));
						updated_S[data_index] = State::S0;
						updated_B.replace(data_index*width, SigSpec(State::Sx, width));
					}

					// create shiftx cell
					SigSpec shifted_cmp = {cmp, SigSpec(State::S0, width_bits)};
					SigSpec outsig = module->addWire(NEW_ID, width);
					Cell *c = module->addShiftx(NEW_ID, data, shifted_cmp, outsig, false, src);
					updated_S.append(en);
					updated_B.append(outsig);
					log("    created $shiftx cell %s.\n", log_id(c));

					// remove this sig and continue with the next block
					seldb.erase(sig);
				}

				// update $pmux cell
				cell->setPort("\\S", updated_S);
				cell->setPort("\\B", updated_B);
				cell->setParam("\\S_WIDTH", GetSize(updated_S));
			}
		}
	}
} Pmux2ShiftxPass;

PRIVATE_NAMESPACE_END
