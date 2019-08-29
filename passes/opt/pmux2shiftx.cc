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

struct OnehotDatabase
{
	Module *module;
	const SigMap &sigmap;
	bool verbose = false;
	bool initialized = false;

	pool<SigBit> init_ones;
	dict<SigSpec, pool<SigSpec>> sig_sources_db;
	dict<SigSpec, bool> sig_onehot_cache;
	pool<SigSpec> recursion_guard;

	OnehotDatabase(Module *module, const SigMap &sigmap) : module(module), sigmap(sigmap)
	{
	}

	void initialize()
	{
		log_assert(!initialized);
		initialized = true;

		for (auto wire : module->wires())
		{
			auto it = wire->attributes.find(ID(init));
			if (it == wire->attributes.end())
				continue;

			auto &val = it->second;
			int width = std::max(GetSize(wire), GetSize(val));

			for (int i = 0; i < width; i++)
				if (val[i] == State::S1)
					init_ones.insert(sigmap(SigBit(wire, i)));
		}

		for (auto cell : module->cells())
		{
			vector<SigSpec> inputs;
			SigSpec output;

			if (cell->type.in(ID($adff), ID($dff), ID($dffe), ID($dlatch), ID($ff)))
			{
				output = cell->getPort(ID(Q));
				if (cell->type == ID($adff))
					inputs.push_back(cell->getParam(ID(ARST_VALUE)));
				inputs.push_back(cell->getPort(ID(D)));
			}

			if (cell->type.in(ID($mux), ID($pmux)))
			{
				output = cell->getPort(ID::Y);
				inputs.push_back(cell->getPort(ID::A));
				SigSpec B = cell->getPort(ID::B);
				for (int i = 0; i < GetSize(B); i += GetSize(output))
					inputs.push_back(B.extract(i, GetSize(output)));
			}

			if (!output.empty())
			{
				output = sigmap(output);
				auto &srcs = sig_sources_db[output];
				for (auto src : inputs) {
					while (!src.empty() && src[GetSize(src)-1] == State::S0)
						src.remove(GetSize(src)-1);
					srcs.insert(sigmap(src));
				}
			}
		}
	}

	void query_worker(const SigSpec &sig, bool &retval, bool &cache, int indent)
	{
		if (verbose)
			log("%*s %s\n", indent, "", log_signal(sig));
		log_assert(retval);

		if (recursion_guard.count(sig)) {
			if (verbose)
				log("%*s   - recursion\n", indent, "");
			cache = false;
			return;
		}

		auto it = sig_onehot_cache.find(sig);
		if (it != sig_onehot_cache.end()) {
			if (verbose)
				log("%*s   - cached (%s)\n", indent, "", it->second ? "true" : "false");
			if (!it->second)
				retval = false;
			return;
		}

		bool found_init_ones = false;
		for (auto bit : sig) {
			if (init_ones.count(bit)) {
				if (found_init_ones) {
					if (verbose)
						log("%*s   - non-onehot init value\n", indent, "");
					retval = false;
					break;
				}
				found_init_ones = true;
			}
		}

		if (retval)
		{
			if (sig.is_fully_const())
			{
				bool found_ones = false;
				for (auto bit : sig) {
					if (bit == State::S1) {
						if (found_ones) {
							if (verbose)
								log("%*s   - non-onehot constant\n", indent, "");
							retval = false;
							break;
						}
						found_ones = true;
					}
				}
			}
			else
			{
				auto srcs = sig_sources_db.find(sig);
				if (srcs == sig_sources_db.end()) {
					if (verbose)
						log("%*s   - no sources for non-const signal\n", indent, "");
					retval = false;
				} else {
					for (auto &src : srcs->second) {
						bool child_cache = true;
						recursion_guard.insert(sig);
						query_worker(src, retval, child_cache, indent+4);
						recursion_guard.erase(sig);
						if (!child_cache)
							cache = false;
						if (!retval)
							break;
					}
				}
			}
		}

		// it is always safe to cache a negative result
		if (cache || !retval)
			sig_onehot_cache[sig] = retval;
	}

	bool query(const SigSpec &sig)
	{
		bool retval = true;
		bool cache = true;

		if (verbose)
			log("** ONEHOT QUERY START (%s)\n", log_signal(sig));

		if (!initialized)
			initialize();

		query_worker(sig, retval, cache, 3);

		if (verbose)
			log("** ONEHOT QUERY RESULT = %s\n", retval ? "true" : "false");

		// it is always safe to cache the root result of a query
		if (!cache)
			sig_onehot_cache[sig] = retval;

		return retval;
	}
};

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
		log("    -v, -vv\n");
		log("        verbose output\n");
		log("\n");
		log("    -min_density <percentage>\n");
		log("        specifies the minimum density for the shifter\n");
		log("        default: 50\n");
		log("\n");
		log("    -min_choices <int>\n");
		log("        specified the minimum number of choices for a control signal\n");
		log("        default: 3\n");
		log("\n");
		log("    -onehot ignore|pmux|shiftx\n");
		log("        select strategy for one-hot encoded control signals\n");
		log("        default: pmux\n");
		log("\n");
		log("    -norange\n");
		log("        disable $sub inference for \"range decoders\"\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		int min_density = 50;
		int min_choices = 3;
		bool allow_onehot = false;
		bool optimize_onehot = true;
		bool verbose = false;
		bool verbose_onehot = false;
		bool norange = false;

		log_header(design, "Executing PMUX2SHIFTX pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-min_density" && argidx+1 < args.size()) {
				min_density = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min_choices" && argidx+1 < args.size()) {
				min_choices = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-onehot" && argidx+1 < args.size() && args[argidx+1] == "ignore") {
				argidx++;
				allow_onehot = false;
				optimize_onehot = false;
				continue;
			}
			if (args[argidx] == "-onehot" && argidx+1 < args.size() && args[argidx+1] == "pmux") {
				argidx++;
				allow_onehot = false;
				optimize_onehot = true;
				continue;
			}
			if (args[argidx] == "-onehot" && argidx+1 < args.size() && args[argidx+1] == "shiftx") {
				argidx++;
				allow_onehot = true;
				optimize_onehot = false;
				continue;
			}
			if (args[argidx] == "-v") {
				verbose = true;
				continue;
			}
			if (args[argidx] == "-vv") {
				verbose = true;
				verbose_onehot = true;
				continue;
			}
			if (args[argidx] == "-norange") {
				norange = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			OnehotDatabase onehot_db(module, sigmap);
			onehot_db.verbose = verbose_onehot;

			dict<SigBit, pair<SigSpec, Const>> eqdb;

			for (auto cell : module->cells())
			{
				if (cell->type == ID($eq))
				{
					dict<SigBit, State> bits;

					SigSpec A = sigmap(cell->getPort(ID::A));
					SigSpec B = sigmap(cell->getPort(ID::B));

					int a_width = cell->getParam(ID(A_WIDTH)).as_int();
					int b_width = cell->getParam(ID(B_WIDTH)).as_int();

					if (a_width < b_width) {
						bool a_signed = cell->getParam(ID(A_SIGNED)).as_int();
						A.extend_u0(b_width, a_signed);
					}

					if (b_width < a_width) {
						bool b_signed = cell->getParam(ID(B_SIGNED)).as_int();
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

					eqdb[sigmap(cell->getPort(ID::Y)[0])] = entry;
					goto next_cell;
				}

				if (cell->type == ID($logic_not))
				{
					dict<SigBit, State> bits;

					SigSpec A = sigmap(cell->getPort(ID::A));

					for (int i = 0; i < GetSize(A); i++)
						bits[A[i]] = State::S0;

					bits.sort();
					pair<SigSpec, Const> entry;

					for (auto it : bits) {
						entry.first.append_bit(it.first);
						entry.second.bits.push_back(it.second);
					}

					eqdb[sigmap(cell->getPort(ID::Y)[0])] = entry;
					goto next_cell;
				}
		next_cell:;
			}

			for (auto cell : module->selected_cells())
			{
				if (cell->type != ID($pmux))
					continue;

				string src = cell->get_src_attribute();
				int width = cell->getParam(ID(WIDTH)).as_int();
				int width_bits = ceil_log2(width);
				int extwidth = width;

				while (extwidth & (extwidth-1))
					extwidth++;

				dict<SigSpec, pool<int>> seldb;

				SigSpec A = cell->getPort(ID::A);
				SigSpec B = cell->getPort(ID::B);
				SigSpec S = sigmap(cell->getPort(ID(S)));
				for (int i = 0; i < GetSize(S); i++)
				{
					if (!eqdb.count(S[i]))
						continue;

					auto &entry = eqdb.at(S[i]);
					seldb[entry.first].insert(i);
				}

				if (seldb.empty())
					continue;

				bool printed_pmux_header = false;

				if (verbose) {
					printed_pmux_header = true;
					log("Inspecting $pmux cell %s/%s.\n", log_id(module), log_id(cell));
					log("  data width: %d (next power-of-2 = %d, log2 = %d)\n", width, extwidth, width_bits);
				}

				SigSpec updated_S = cell->getPort(ID(S));
				SigSpec updated_B = cell->getPort(ID::B);

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

					// find the relevant choices
					bool is_onehot = GetSize(sig) > 2;
					dict<Const, int> choices;
					for (int i : seldb.at(sig)) {
						Const val = eqdb.at(S[i]).second;
						int onebits = 0;
						for (auto b : val.bits)
							if (b == State::S1)
								onebits++;
						if (onebits > 1)
							is_onehot = false;
						choices[val] = i;
					}

					bool full_pmux = GetSize(choices) == GetSize(S);

					// TBD: also find choices that are using signals that are subsets of the bits in "sig"

					if (!verbose)
					{
						if (is_onehot && !allow_onehot && !optimize_onehot) {
							seldb.erase(sig);
							continue;
						}

						if (GetSize(choices) < min_choices) {
							seldb.erase(sig);
							continue;
						}
					}

					if (!printed_pmux_header) {
						printed_pmux_header = true;
						log("Inspecting $pmux cell %s/%s.\n", log_id(module), log_id(cell));
						log("  data width: %d (next power-of-2 = %d, log2 = %d)\n", width, extwidth, width_bits);
					}

					log("  checking ctrl signal %s\n", log_signal(sig));

					auto print_choices = [&]() {
						log("    table of choices:\n");
						for (auto &it : choices)
							log("    %3d: %s: %s\n", it.second, log_signal(it.first),
									log_signal(B.extract(it.second*width, width)));
					};

					if (verbose)
					{
						if (is_onehot && !allow_onehot && !optimize_onehot) {
							print_choices();
							log("    ignoring one-hot encoding.\n");
							seldb.erase(sig);
							continue;
						}

						if (GetSize(choices) < min_choices) {
							print_choices();
							log("    insufficient choices.\n");
							seldb.erase(sig);
							continue;
						}
					}

					if (is_onehot && optimize_onehot)
					{
						print_choices();
						if (!onehot_db.query(sig))
						{
							log("    failed to detect onehot driver. do not optimize.\n");
						}
						else
						{
							log("    optimizing one-hot encoding.\n");
							for (auto &it : choices)
							{
								const Const &val = it.first;
								int index = -1;

								for (int i = 0; i < GetSize(val); i++)
									if (val[i] == State::S1) {
										log_assert(index < 0);
										index = i;
									}

								if (index < 0) {
									log("    %3d: zero encoding.\n", it.second);
									continue;
								}

								SigBit new_ctrl = sig[index];
								log("    %3d: new crtl signal is %s.\n", it.second, log_signal(new_ctrl));
								updated_S[it.second] = new_ctrl;
							}
						}
						seldb.erase(sig);
						continue;
					}

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

							// find best src column for this dst column
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

								if (!norange && this_delta != this_inv_delta)
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
								else if (!norange && this_delta != best_delta)
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

					if (full_pmux) {
						int full_density = 100*GetSize(choices) / (1 << GetSize(sig));
						log("    full density: %d%%\n", full_density);
						if (full_density < min_density) {
							full_pmux = false;
						} else {
							min_choice = 0;
							max_choice = (1 << GetSize(sig))-1;
							log("    update to full case.\n");
							log("    new min choice: %d\n", min_choice);
							log("    new max choice: %d\n", max_choice);
						}
					}

					bool full_case = (min_choice == 0) && (max_choice == (1 << GetSize(sig))-1) && (full_pmux || max_choice+1 == GetSize(choices));
					log("    full case: %s\n", full_case ? "true" : "false");

					// check density percentages
					Const offset(State::S0, GetSize(sig));
					if (!norange && absolute_density < min_density && range_density >= min_density)
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
					if (absolute_density < min_density) {
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
					if (full_pmux) {
						for (int i = 0; i <= max_choice; i++)
							data.replace(i*extwidth, A);
					}
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
				cell->setPort(ID(S), updated_S);
				cell->setPort(ID::B, updated_B);
				cell->setParam(ID(S_WIDTH), GetSize(updated_S));
			}
		}
	}
} Pmux2ShiftxPass;

struct OnehotPass : public Pass {
	OnehotPass() : Pass("onehot", "optimize $eq cells for onehot signals") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    onehot [options] [selection]\n");
		log("\n");
		log("This pass optimizes $eq cells that compare one-hot signals against constants\n");
		log("\n");
		log("    -v, -vv\n");
		log("        verbose output\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool verbose = false;
		bool verbose_onehot = false;

		log_header(design, "Executing ONEHOT pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-v") {
				verbose = true;
				continue;
			}
			if (args[argidx] == "-vv") {
				verbose = true;
				verbose_onehot = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			OnehotDatabase onehot_db(module, sigmap);
			onehot_db.verbose = verbose_onehot;

			for (auto cell : module->selected_cells())
			{
				if (cell->type != ID($eq))
					continue;

				SigSpec A = sigmap(cell->getPort(ID::A));
				SigSpec B = sigmap(cell->getPort(ID::B));

				int a_width = cell->getParam(ID(A_WIDTH)).as_int();
				int b_width = cell->getParam(ID(B_WIDTH)).as_int();

				if (a_width < b_width) {
					bool a_signed = cell->getParam(ID(A_SIGNED)).as_int();
					A.extend_u0(b_width, a_signed);
				}

				if (b_width < a_width) {
					bool b_signed = cell->getParam(ID(B_SIGNED)).as_int();
					B.extend_u0(a_width, b_signed);
				}

				if (A.is_fully_const())
					std::swap(A, B);

				if (!B.is_fully_const())
					continue;

				if (verbose)
					log("Checking $eq(%s, %s) cell %s/%s.\n", log_signal(A), log_signal(B), log_id(module), log_id(cell));

				if (!onehot_db.query(A)) {
					if (verbose)
						log("  onehot driver test on %s failed.\n", log_signal(A));
					continue;
				}

				int index = -1;
				bool not_onehot = false;

				for (int i = 0; i < GetSize(B); i++) {
					if (B[i] != State::S1)
						continue;
					if (index >= 0)
						not_onehot = true;
					index = i;
				}

				if (index < 0) {
					if (verbose)
						log("  not optimizing the zero pattern.\n");
					continue;
				}

				SigSpec Y = cell->getPort(ID::Y);

				if (not_onehot)
				{
					if (verbose)
						log("  replacing with constant 0 driver.\n");
					else
						log("Replacing one-hot $eq(%s, %s) cell %s/%s with constant 0 driver.\n", log_signal(A), log_signal(B), log_id(module), log_id(cell));
					module->connect(Y, SigSpec(1, GetSize(Y)));
				}
				else
				{
					SigSpec sig = A[index];
					if (verbose)
						log("  replacing with signal %s.\n", log_signal(sig));
					else
						log("Replacing one-hot $eq(%s, %s) cell %s/%s with signal %s.\n",log_signal(A), log_signal(B), log_id(module), log_id(cell), log_signal(sig));
					sig.extend_u0(GetSize(Y));
					module->connect(Y, sig);
				}

				module->remove(cell);
			}
		}
	}
} OnehotPass;

PRIVATE_NAMESPACE_END
