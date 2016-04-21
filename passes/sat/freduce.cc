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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/consteval.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/satgen.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <algorithm>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool inv_mode;
int verbose_level, reduce_counter, reduce_stop_at;
typedef std::map<RTLIL::SigBit, std::pair<RTLIL::Cell*, std::set<RTLIL::SigBit>>> drivers_t;
std::string dump_prefix;

struct equiv_bit_t
{
	int depth;
	bool inverted;
	RTLIL::Cell *drv;
	RTLIL::SigBit bit;

	bool operator<(const equiv_bit_t &other) const {
		if (depth != other.depth)
			return depth < other.depth;
		if (inverted != other.inverted)
			return inverted < other.inverted;
		if (drv != other.drv)
			return drv < other.drv;
		return bit < other.bit;
	}
};

struct CountBitUsage
{
	SigMap &sigmap;
	std::map<RTLIL::SigBit, int> &cache;

	CountBitUsage(SigMap &sigmap, std::map<RTLIL::SigBit, int> &cache) : sigmap(sigmap), cache(cache) { }

	void operator()(RTLIL::SigSpec &sig) {
		std::vector<RTLIL::SigBit> vec = sigmap(sig).to_sigbit_vector();
		for (auto &bit : vec)
			cache[bit]++;
	}
};

struct FindReducedInputs
{
	SigMap &sigmap;
	drivers_t &drivers;

	ezSatPtr ez;
	std::set<RTLIL::Cell*> ez_cells;
	SatGen satgen;

	std::map<RTLIL::SigBit, int> sat_pi;
	std::vector<int> sat_pi_uniq_bitvec;

	FindReducedInputs(SigMap &sigmap, drivers_t &drivers) :
			sigmap(sigmap), drivers(drivers), satgen(ez.get(), &sigmap)
	{
		satgen.model_undef = true;
	}

	int get_bits(int val)
	{
		int bits = 0;
		for (int i = 8*sizeof(int); val; i = i >> 1)
			if (val >> (i-1)) {
				bits += i;
				val = val >> i;
			}
		return bits;
	}

	void register_pi_bit(RTLIL::SigBit bit)
	{
		if (sat_pi.count(bit) != 0)
			return;

		satgen.setContext(&sigmap, "A");
		int sat_a = satgen.importSigSpec(bit).front();
		ez->assume(ez->NOT(satgen.importUndefSigSpec(bit).front()));

		satgen.setContext(&sigmap, "B");
		int sat_b = satgen.importSigSpec(bit).front();
		ez->assume(ez->NOT(satgen.importUndefSigSpec(bit).front()));

		int idx = sat_pi.size();
		size_t idx_bits = get_bits(idx);

		if (sat_pi_uniq_bitvec.size() != idx_bits) {
			sat_pi_uniq_bitvec.push_back(ez->frozen_literal(stringf("uniq_%d", int(idx_bits)-1)));
			for (auto &it : sat_pi)
				ez->assume(ez->OR(ez->NOT(it.second), ez->NOT(sat_pi_uniq_bitvec.back())));
		}
		log_assert(sat_pi_uniq_bitvec.size() == idx_bits);

		sat_pi[bit] = ez->frozen_literal(stringf("p, falsei_%s", log_signal(bit)));
		ez->assume(ez->IFF(ez->XOR(sat_a, sat_b), sat_pi[bit]));

		for (size_t i = 0; i < idx_bits; i++)
			if ((idx & (1 << i)) == 0)
				ez->assume(ez->OR(ez->NOT(sat_pi[bit]), ez->NOT(sat_pi_uniq_bitvec[i])));
			else
				ez->assume(ez->OR(ez->NOT(sat_pi[bit]), sat_pi_uniq_bitvec[i]));
	}

	void register_cone_worker(std::set<RTLIL::SigBit> &pi, std::set<RTLIL::SigBit> &sigdone, RTLIL::SigBit out)
	{
		if (out.wire == NULL)
			return;
		if (sigdone.count(out) != 0)
			return;
		sigdone.insert(out);

		if (drivers.count(out) != 0) {
			std::pair<RTLIL::Cell*, std::set<RTLIL::SigBit>> &drv = drivers.at(out);
			if (ez_cells.count(drv.first) == 0) {
				satgen.setContext(&sigmap, "A");
				if (!satgen.importCell(drv.first))
					log_error("Can't create SAT model for cell %s (%s)!\n", RTLIL::id2cstr(drv.first->name), RTLIL::id2cstr(drv.first->type));
				satgen.setContext(&sigmap, "B");
				if (!satgen.importCell(drv.first))
					log_abort();
				ez_cells.insert(drv.first);
			}
			for (auto &bit : drv.second)
				register_cone_worker(pi, sigdone, bit);
		} else {
			register_pi_bit(out);
			pi.insert(out);
		}
	}

	void register_cone(std::vector<RTLIL::SigBit> &pi, RTLIL::SigBit out)
	{
		std::set<RTLIL::SigBit> pi_set, sigdone;
		register_cone_worker(pi_set, sigdone, out);
		pi.clear();
		pi.insert(pi.end(), pi_set.begin(), pi_set.end());
	}

	void analyze(std::vector<RTLIL::SigBit> &reduced_inputs, RTLIL::SigBit output, int prec)
	{
		if (verbose_level >= 1)
			log("[%2d%%]  Analyzing input cone for signal %s:\n", prec, log_signal(output));

		std::vector<RTLIL::SigBit> pi;
		register_cone(pi, output);

		if (verbose_level >= 1)
			log("         Found %d input signals and %d cells.\n", int(pi.size()), int(ez_cells.size()));

		satgen.setContext(&sigmap, "A");
		int output_a = satgen.importSigSpec(output).front();
		int output_undef_a = satgen.importUndefSigSpec(output).front();

		satgen.setContext(&sigmap, "B");
		int output_b = satgen.importSigSpec(output).front();
		int output_undef_b = satgen.importUndefSigSpec(output).front();

		std::set<int> unused_pi_idx;

		for (size_t i = 0; i < pi.size(); i++)
			unused_pi_idx.insert(i);

		while (1)
		{
			std::vector<int> model_pi_idx;
			std::vector<int> model_expr;
			std::vector<bool> model;

			for (size_t i = 0; i < pi.size(); i++)
				if (unused_pi_idx.count(i) != 0) {
					model_pi_idx.push_back(i);
					model_expr.push_back(sat_pi.at(pi[i]));
				}

			if (!ez->solve(model_expr, model, ez->expression(ezSAT::OpOr, model_expr), ez->XOR(output_a, output_b), ez->NOT(output_undef_a), ez->NOT(output_undef_b)))
				break;

			int found_count = 0;
			for (size_t i = 0; i < model_pi_idx.size(); i++)
				if (model[i]) {
					if (verbose_level >= 2)
						log("         Found relevant input: %s\n", log_signal(pi[model_pi_idx[i]]));
					unused_pi_idx.erase(model_pi_idx[i]);
					found_count++;
				}
			log_assert(found_count == 1);
		}

		for (size_t i = 0; i < pi.size(); i++)
			if (unused_pi_idx.count(i) == 0)
				reduced_inputs.push_back(pi[i]);

		if (verbose_level >= 1)
			log("         Reduced input cone contains %d inputs.\n", int(reduced_inputs.size()));
	}
};

struct PerformReduction
{
	SigMap &sigmap;
	drivers_t &drivers;
	std::set<std::pair<RTLIL::SigBit, RTLIL::SigBit>> &inv_pairs;
	pool<SigBit> recursion_guard;

	ezSatPtr ez;
	SatGen satgen;

	std::vector<int> sat_pi, sat_out, sat_def;
	std::vector<RTLIL::SigBit> out_bits, pi_bits;
	std::vector<bool> out_inverted;
	std::vector<int> out_depth;
	int cone_size;

	int register_cone_worker(std::set<RTLIL::Cell*> &celldone, std::map<RTLIL::SigBit, int> &sigdepth, RTLIL::SigBit out)
	{
		if (out.wire == NULL)
			return 0;
		if (sigdepth.count(out) != 0)
			return sigdepth.at(out);

		if (recursion_guard.count(out)) {
			string loop_signals;
			for (auto loop_bit : recursion_guard)
				loop_signals += string(" ") + log_signal(loop_bit);
			log_error("Found logic loop:%s\n", loop_signals.c_str());
		}

		recursion_guard.insert(out);

		if (drivers.count(out) != 0) {
			std::pair<RTLIL::Cell*, std::set<RTLIL::SigBit>> &drv = drivers.at(out);
			if (celldone.count(drv.first) == 0) {
				if (!satgen.importCell(drv.first))
					log_error("Can't create SAT model for cell %s (%s)!\n", RTLIL::id2cstr(drv.first->name), RTLIL::id2cstr(drv.first->type));
				celldone.insert(drv.first);
			}
			int max_child_depth = 0;
			for (auto &bit : drv.second)
				max_child_depth = max(register_cone_worker(celldone, sigdepth, bit), max_child_depth);
			sigdepth[out] = max_child_depth + 1;
		} else {
			pi_bits.push_back(out);
			sat_pi.push_back(satgen.importSigSpec(out).front());
			ez->assume(ez->NOT(satgen.importUndefSigSpec(out).front()));
			sigdepth[out] = 0;
		}

		recursion_guard.erase(out);
		return sigdepth.at(out);
	}

	PerformReduction(SigMap &sigmap, drivers_t &drivers, std::set<std::pair<RTLIL::SigBit, RTLIL::SigBit>> &inv_pairs, std::vector<RTLIL::SigBit> &bits, int cone_size) :
			sigmap(sigmap), drivers(drivers), inv_pairs(inv_pairs), satgen(ez.get(), &sigmap), out_bits(bits), cone_size(cone_size)
	{
		satgen.model_undef = true;

		std::set<RTLIL::Cell*> celldone;
		std::map<RTLIL::SigBit, int> sigdepth;

		for (auto &bit : bits) {
			out_depth.push_back(register_cone_worker(celldone, sigdepth, bit));
			sat_out.push_back(satgen.importSigSpec(bit).front());
			sat_def.push_back(ez->NOT(satgen.importUndefSigSpec(bit).front()));
		}

		if (inv_mode && cone_size > 0) {
			if (!ez->solve(sat_out, out_inverted, ez->expression(ezSAT::OpAnd, sat_def)))
				log_error("Solving for initial model failed!\n");
			for (size_t i = 0; i < sat_out.size(); i++)
				if (out_inverted.at(i))
					sat_out[i] = ez->NOT(sat_out[i]);
		} else
			out_inverted = std::vector<bool>(sat_out.size(), false);
	}

	void analyze_const(std::vector<std::vector<equiv_bit_t>> &results, int idx)
	{
		if (verbose_level == 1)
			log("    Finding const value for %s.\n", log_signal(out_bits[idx]));

		bool can_be_set = ez->solve(ez->AND(sat_out[idx], sat_def[idx]));
		bool can_be_clr = ez->solve(ez->AND(ez->NOT(sat_out[idx]), sat_def[idx]));
		log_assert(!can_be_set || !can_be_clr);

		RTLIL::SigBit value(RTLIL::State::Sx);
		if (can_be_set)
			value = RTLIL::State::S1;
		if (can_be_clr)
			value = RTLIL::State::S0;
		if (verbose_level == 1)
			log("      Constant value for this signal: %s\n", log_signal(value));

		int result_idx = -1;
		for (size_t i = 0; i < results.size(); i++) {
			if (results[i].front().bit == value) {
				result_idx = i;
				break;
			}
		}

		if (result_idx == -1) {
			result_idx = results.size();
			results.push_back(std::vector<equiv_bit_t>());
			equiv_bit_t bit;
			bit.depth = 0;
			bit.inverted = false;
			bit.drv = NULL;
			bit.bit = value;
			results.back().push_back(bit);
		}

		equiv_bit_t bit;
		bit.depth = 1;
		bit.inverted = false;
		bit.drv = drivers.count(out_bits[idx]) ? drivers.at(out_bits[idx]).first : NULL;
		bit.bit = out_bits[idx];
		results[result_idx].push_back(bit);
	}

	void analyze(std::vector<std::set<int>> &results, std::map<int, int> &results_map, std::vector<int> &bucket, std::string indent1, std::string indent2)
	{
		std::string indent = indent1 + indent2;
		const char *indt = indent.c_str();

		if (bucket.size() <= 1)
			return;

		if (verbose_level == 1)
			log("%s  Trying to shatter bucket with %d signals.\n", indt, int(bucket.size()));

		if (verbose_level > 1) {
			std::vector<RTLIL::SigBit> bucket_sigbits;
			for (int idx : bucket)
				bucket_sigbits.push_back(out_bits[idx]);
			log("%s  Trying to shatter bucket with %d signals: %s\n", indt, int(bucket.size()), log_signal(bucket_sigbits));
		}

		std::vector<int> sat_set_list, sat_clr_list;
		for (int idx : bucket) {
			sat_set_list.push_back(ez->AND(sat_out[idx], sat_def[idx]));
			sat_clr_list.push_back(ez->AND(ez->NOT(sat_out[idx]), sat_def[idx]));
		}

		std::vector<int> modelVars = sat_out;
		std::vector<bool> model;

		modelVars.insert(modelVars.end(), sat_def.begin(), sat_def.end());
		if (verbose_level >= 2)
			modelVars.insert(modelVars.end(), sat_pi.begin(), sat_pi.end());

		if (ez->solve(modelVars, model, ez->expression(ezSAT::OpOr, sat_set_list), ez->expression(ezSAT::OpOr, sat_clr_list)))
		{
			int iter_count = 1;

			while (1)
			{
				sat_set_list.clear();
				sat_clr_list.clear();

				std::vector<int> sat_def_list;

				for (int idx : bucket)
					if (!model[sat_out.size() + idx]) {
						sat_set_list.push_back(ez->AND(sat_out[idx], sat_def[idx]));
						sat_clr_list.push_back(ez->AND(ez->NOT(sat_out[idx]), sat_def[idx]));
					} else {
						sat_def_list.push_back(sat_def[idx]);
					}

				if (!ez->solve(modelVars, model, ez->expression(ezSAT::OpOr, sat_set_list), ez->expression(ezSAT::OpOr, sat_clr_list), ez->expression(ezSAT::OpAnd, sat_def_list)))
					break;
				iter_count++;
			}

			if (verbose_level >= 1) {
				int count_set = 0, count_clr = 0, count_undef = 0;
				for (int idx : bucket)
					if (!model[sat_out.size() + idx])
						count_undef++;
					else if (model[idx])
						count_set++;
					else
						count_clr++;
				log("%s    After %d iterations: %d set vs. %d clr vs %d undef\n", indt, iter_count, count_set, count_clr, count_undef);
			}

			if (verbose_level >= 2) {
				for (size_t i = 0; i < pi_bits.size(); i++)
					log("%s       -> PI  %c == %s\n", indt, model[2*sat_out.size() + i] ? '1' : '0', log_signal(pi_bits[i]));
				for (int idx : bucket)
					log("%s       -> OUT %c == %s%s\n", indt, model[sat_out.size() + idx] ? model[idx] ? '1' : '0' : 'x',
							out_inverted.at(idx) ? "~" : "", log_signal(out_bits[idx]));
			}

			std::vector<int> buckets_a;
			std::vector<int> buckets_b;

			for (int idx : bucket) {
				if (!model[sat_out.size() + idx] || model[idx])
					buckets_a.push_back(idx);
				if (!model[sat_out.size() + idx] || !model[idx])
					buckets_b.push_back(idx);
			}
			analyze(results, results_map, buckets_a, indent1 + ".", indent2 + "  ");
			analyze(results, results_map, buckets_b, indent1 + "x", indent2 + "  ");
		}
		else
		{
			std::vector<int> undef_slaves;

			for (int idx : bucket) {
				std::vector<int> sat_def_list;
				for (int idx2 : bucket)
					if (idx != idx2)
						sat_def_list.push_back(sat_def[idx2]);
				if (ez->solve(ez->NOT(sat_def[idx]), ez->expression(ezSAT::OpOr, sat_def_list)))
					undef_slaves.push_back(idx);
			}

			if (undef_slaves.size() == bucket.size()) {
				if (verbose_level >= 1)
					log("%s    Complex undef overlap. None of the signals covers the others.\n", indt);
				// FIXME: We could try to further shatter a group with complex undef overlaps
				return;
			}

			for (int idx : undef_slaves)
				out_depth[idx] = std::numeric_limits<int>::max();

			if (verbose_level >= 1) {
				log("%s    Found %d equivalent signals:", indt, int(bucket.size()));
				for (int idx : bucket)
					log("%s%s%s", idx == bucket.front() ? " " : ", ", out_inverted[idx] ? "~" : "", log_signal(out_bits[idx]));
				log("\n");
			}

			int result_idx = -1;
			for (int idx : bucket) {
				if (results_map.count(idx) == 0)
					continue;
				if (result_idx == -1) {
					result_idx = results_map.at(idx);
					continue;
				}
				int result_idx2 = results_map.at(idx);
				results[result_idx].insert(results[result_idx2].begin(), results[result_idx2].end());
				for (int idx2 : results[result_idx2])
					results_map[idx2] = result_idx;
				results[result_idx2].clear();
			}

			if (result_idx == -1) {
				result_idx = results.size();
				results.push_back(std::set<int>());
			}

			results[result_idx].insert(bucket.begin(), bucket.end());
		}
	}

	void analyze(std::vector<std::vector<equiv_bit_t>> &results, int perc)
	{
		std::vector<int> bucket;
		for (size_t i = 0; i < sat_out.size(); i++)
			bucket.push_back(i);

		std::vector<std::set<int>> results_buf;
		std::map<int, int> results_map;
		analyze(results_buf, results_map, bucket, stringf("[%2d%%] %d ", perc, cone_size), "");

		for (auto &r : results_buf)
		{
			if (r.size() <= 1)
				continue;

			if (verbose_level >= 1) {
				std::vector<RTLIL::SigBit> r_sigbits;
				for (int idx : r)
					r_sigbits.push_back(out_bits[idx]);
				log("  Found group of %d equivalent signals: %s\n", int(r.size()), log_signal(r_sigbits));
			}

			std::vector<int> undef_slaves;

			for (int idx : r) {
				std::vector<int> sat_def_list;
				for (int idx2 : r)
					if (idx != idx2)
						sat_def_list.push_back(sat_def[idx2]);
				if (ez->solve(ez->NOT(sat_def[idx]), ez->expression(ezSAT::OpOr, sat_def_list)))
					undef_slaves.push_back(idx);
			}

			if (undef_slaves.size() == bucket.size()) {
				if (verbose_level >= 1)
					log("    Complex undef overlap. None of the signals covers the others.\n");
				// FIXME: We could try to further shatter a group with complex undef overlaps
				return;
			}

			for (int idx : undef_slaves)
				out_depth[idx] = std::numeric_limits<int>::max();

			std::vector<equiv_bit_t> result;

			for (int idx : r) {
				equiv_bit_t bit;
				bit.depth = out_depth[idx];
				bit.inverted = out_inverted[idx];
				bit.drv = drivers.count(out_bits[idx]) ? drivers.at(out_bits[idx]).first : NULL;
				bit.bit = out_bits[idx];
				result.push_back(bit);
			}

			std::sort(result.begin(), result.end());

			if (result.front().inverted)
				for (auto &bit : result)
					bit.inverted = !bit.inverted;

			for (size_t i = 1; i < result.size(); i++) {
				std::pair<RTLIL::SigBit, RTLIL::SigBit> p(result[0].bit, result[i].bit);
				if (inv_pairs.count(p) != 0)
					result.erase(result.begin() + i);
			}

			if (result.size() > 1)
				results.push_back(result);
		}
	}
};

struct FreduceWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;

	SigMap sigmap;
	drivers_t drivers;
	std::set<std::pair<RTLIL::SigBit, RTLIL::SigBit>> inv_pairs;

	FreduceWorker(RTLIL::Design *design, RTLIL::Module *module) : design(design), module(module), sigmap(module)
	{
	}

	bool find_bit_in_cone(std::set<RTLIL::Cell*> &celldone, RTLIL::SigBit needle, RTLIL::SigBit haystack)
	{
		if (needle == haystack)
			return true;
		if (haystack.wire == NULL || needle.wire == NULL || drivers.count(haystack) == 0)
			return false;

		std::pair<RTLIL::Cell*, std::set<RTLIL::SigBit>> &drv = drivers.at(haystack);

		if (celldone.count(drv.first))
			return false;
		celldone.insert(drv.first);

		for (auto &bit : drv.second)
			if (find_bit_in_cone(celldone, needle, bit))
				return true;
		return false;
	}

	bool find_bit_in_cone(RTLIL::SigBit needle, RTLIL::SigBit haystack)
	{
		std::set<RTLIL::Cell*> celldone;
		return find_bit_in_cone(celldone, needle, haystack);
	}

	void dump()
	{
		std::string filename = stringf("%s_%s_%05d.il", dump_prefix.c_str(), RTLIL::id2cstr(module->name), reduce_counter);
		log("%s    Writing dump file `%s'.\n", reduce_counter ? "  " : "", filename.c_str());
		Pass::call(design, stringf("dump -outfile %s %s", filename.c_str(), design->selected_active_module.empty() ? module->name.c_str() : ""));
	}

	int run()
	{
		log("Running functional reduction on module %s:\n", RTLIL::id2cstr(module->name));

		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();

		int bits_full_total = 0;
		std::vector<std::set<RTLIL::SigBit>> batches;
		for (auto &it : module->wires_)
			if (it.second->port_input) {
				batches.push_back(sigmap(it.second).to_sigbit_set());
				bits_full_total += it.second->width;
			}
		for (auto &it : module->cells_) {
			if (ct.cell_known(it.second->type)) {
				std::set<RTLIL::SigBit> inputs, outputs;
				for (auto &port : it.second->connections()) {
					std::vector<RTLIL::SigBit> bits = sigmap(port.second).to_sigbit_vector();
					if (ct.cell_output(it.second->type, port.first))
						outputs.insert(bits.begin(), bits.end());
					else
						inputs.insert(bits.begin(), bits.end());
				}
				std::pair<RTLIL::Cell*, std::set<RTLIL::SigBit>> drv(it.second, inputs);
				for (auto &bit : outputs)
					drivers[bit] = drv;
				batches.push_back(outputs);
				bits_full_total += outputs.size();
			}
			if (inv_mode && it.second->type == "$_NOT_")
				inv_pairs.insert(std::pair<RTLIL::SigBit, RTLIL::SigBit>(sigmap(it.second->getPort("\\A")), sigmap(it.second->getPort("\\Y"))));
		}

		int bits_count = 0;
		int bits_full_count = 0;
		std::map<std::vector<RTLIL::SigBit>, std::vector<RTLIL::SigBit>> buckets;
		for (auto &batch : batches)
		{
			for (auto &bit : batch)
				if (bit.wire != NULL && design->selected(module, bit.wire))
					goto found_selected_wire;
			bits_full_count += batch.size();
			continue;

		found_selected_wire:
			log("  Finding reduced input cone for signal batch %s%c\n",
					log_signal(batch), verbose_level ? ':' : '.');

			FindReducedInputs infinder(sigmap, drivers);
			for (auto &bit : batch) {
				std::vector<RTLIL::SigBit> inputs;
				infinder.analyze(inputs, bit, 100 * bits_full_count / bits_full_total);
				buckets[inputs].push_back(bit);
				bits_full_count++;
				bits_count++;
			}
		}
		log("  Sorted %d signal bits into %d buckets.\n", bits_count, int(buckets.size()));

		int bucket_count = 0;
		std::vector<std::vector<equiv_bit_t>> equiv;
		for (auto &bucket : buckets)
		{
			bucket_count++;

			if (bucket.second.size() == 1)
				continue;

			if (bucket.first.size() == 0) {
				log("  Finding const values for bucket %s%c\n", log_signal(bucket.second), verbose_level ? ':' : '.');
				PerformReduction worker(sigmap, drivers, inv_pairs, bucket.second, bucket.first.size());
				for (size_t idx = 0; idx < bucket.second.size(); idx++)
					worker.analyze_const(equiv, idx);
			} else {
				log("  Trying to shatter bucket %s%c\n", log_signal(bucket.second), verbose_level ? ':' : '.');
				PerformReduction worker(sigmap, drivers, inv_pairs, bucket.second, bucket.first.size());
				worker.analyze(equiv, 100 * bucket_count / (buckets.size() + 1));
			}
		}

		std::map<RTLIL::SigBit, int> bitusage;
		module->rewrite_sigspecs(CountBitUsage(sigmap, bitusage));

		if (!dump_prefix.empty())
			dump();

		log("  Rewiring %d equivalent groups:\n", int(equiv.size()));
		int rewired_sigbits = 0;
		for (auto &grp : equiv)
		{
			log("    [%05d] Using as master for group: %s\n", ++reduce_counter, log_signal(grp.front().bit));

			RTLIL::SigSpec inv_sig;
			for (size_t i = 1; i < grp.size(); i++)
			{
				if (!design->selected(module, grp[i].bit.wire)) {
					log("      Skipping not-selected slave: %s\n", log_signal(grp[i].bit));
					continue;
				}

				if (grp[i].bit.wire->port_id == 0 && bitusage[grp[i].bit] <= 1) {
					log("      Skipping unused slave: %s\n", log_signal(grp[i].bit));
					continue;
				}

				if (find_bit_in_cone(grp[i].bit, grp.front().bit)) {
					log("      Skipping dependency of master: %s\n", log_signal(grp[i].bit));
					continue;
				}

				log("      Connect slave%s: %s\n", grp[i].inverted ? " using inverter" : "", log_signal(grp[i].bit));

				RTLIL::Cell *drv = drivers.at(grp[i].bit).first;
				RTLIL::Wire *dummy_wire = module->addWire(NEW_ID);
				for (auto &port : drv->connections_)
					if (ct.cell_output(drv->type, port.first))
						sigmap(port.second).replace(grp[i].bit, dummy_wire, &port.second);

				if (grp[i].inverted)
				{
					if (inv_sig.size() == 0)
					{
						inv_sig = module->addWire(NEW_ID);

						RTLIL::Cell *inv_cell = module->addCell(NEW_ID, "$_NOT_");
						inv_cell->setPort("\\A", grp[0].bit);
						inv_cell->setPort("\\Y", inv_sig);
					}

					module->connect(RTLIL::SigSig(grp[i].bit, inv_sig));
				}
				else
					module->connect(RTLIL::SigSig(grp[i].bit, grp[0].bit));

				rewired_sigbits++;
			}

			if (!dump_prefix.empty())
				dump();

			if (reduce_counter == reduce_stop_at) {
				log("    Reached limit passed using -stop option. Skipping all further reductions.\n");
				break;
			}
		}

		log("  Rewired a total of %d signal bits in module %s.\n", rewired_sigbits, RTLIL::id2cstr(module->name));
		return rewired_sigbits;
	}
};

struct FreducePass : public Pass {
	FreducePass() : Pass("freduce", "perform functional reduction") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    freduce [options] [selection]\n");
		log("\n");
		log("This pass performs functional reduction in the circuit. I.e. if two nodes are\n");
		log("equivalent, they are merged to one node and one of the redundant drivers is\n");
		log("disconnected. A subsequent call to 'clean' will remove the redundant drivers.\n");
		log("\n");
		log("    -v, -vv\n");
		log("        enable verbose or very verbose output\n");
		log("\n");
		log("    -inv\n");
		log("        enable explicit handling of inverted signals\n");
		log("\n");
		log("    -stop <n>\n");
		log("        stop after <n> reduction operations. this is mostly used for\n");
		log("        debugging the freduce command itself.\n");
		log("\n");
		log("    -dump <prefix>\n");
		log("        dump the design to <prefix>_<module>_<num>.il after each reduction\n");
		log("        operation. this is mostly used for debugging the freduce command.\n");
		log("\n");
		log("This pass is undef-aware, i.e. it considers don't-care values for detecting\n");
		log("equivalent nodes.\n");
		log("\n");
		log("All selected wires are considered for rewiring. The selected cells cover the\n");
		log("circuit that is analyzed.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		reduce_counter = 0;
		reduce_stop_at = 0;
		verbose_level = 0;
		inv_mode = false;
		dump_prefix = std::string();

		log_header(design, "Executing FREDUCE pass (perform functional reduction).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-v") {
				verbose_level = 1;
				continue;
			}
			if (args[argidx] == "-vv") {
				verbose_level = 2;
				continue;
			}
			if (args[argidx] == "-inv") {
				inv_mode = true;
				continue;
			}
			if (args[argidx] == "-stop" && argidx+1 < args.size()) {
				reduce_stop_at = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-dump" && argidx+1 < args.size()) {
				dump_prefix = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int bitcount = 0;
		for (auto &mod_it : design->modules_) {
			RTLIL::Module *module = mod_it.second;
			if (design->selected(module))
				bitcount += FreduceWorker(design, module).run();
		}

		log("Rewired a total of %d signal bits.\n", bitcount);
	}
} FreducePass;

PRIVATE_NAMESPACE_END
