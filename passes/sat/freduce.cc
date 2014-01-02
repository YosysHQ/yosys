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

namespace {

bool inv_mode;
int verbose_level;
typedef std::map<RTLIL::SigBit, std::pair<RTLIL::Cell*, std::set<RTLIL::SigBit>>> drivers_t;

struct equiv_bit_t
{
	int depth;
	bool inverted;
	RTLIL::SigBit bit;

	bool operator<(const equiv_bit_t &other) const {
		if (depth != other.depth)
			return depth < other.depth;
		if (inverted != other.inverted)
			return inverted < other.inverted;
		return bit < other.bit;
	}
};

struct FindReducedInputs
{
	SigMap &sigmap;
	drivers_t &drivers;

	ezDefaultSAT ez;
	std::set<RTLIL::Cell*> ez_cells;
	SatGen satgen;

	FindReducedInputs(SigMap &sigmap, drivers_t &drivers) :
			sigmap(sigmap), drivers(drivers), satgen(&ez, &sigmap)
	{
		satgen.model_undef = true;
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
		} else
			pi.insert(out);
	}

	void register_cone(std::vector<RTLIL::SigBit> &pi, RTLIL::SigBit out)
	{
		std::set<RTLIL::SigBit> pi_set, sigdone;
		register_cone_worker(pi_set, sigdone, out);
		pi.clear();
		pi.insert(pi.end(), pi_set.begin(), pi_set.end());
	}

	void analyze(std::vector<RTLIL::SigBit> &reduced_inputs, RTLIL::SigBit output)
	{
		if (verbose_level >= 1)
			log("    Analyzing input cone for signal %s:\n", log_signal(output));

		std::vector<RTLIL::SigBit> pi;
		register_cone(pi, output);

		if (verbose_level >= 1)
			log("      Found %d input signals and %d cells.\n", int(pi.size()), int(ez_cells.size()));

		satgen.setContext(&sigmap, "A");
		int output_a = satgen.importSigSpec(output).front();
		int output_undef_a = satgen.importUndefSigSpec(output).front();
		ez.assume(ez.NOT(ez.expression(ezSAT::OpOr, satgen.importUndefSigSpec(pi))));

		satgen.setContext(&sigmap, "B");
		int output_b = satgen.importSigSpec(output).front();
		int output_undef_b = satgen.importUndefSigSpec(output).front();
		ez.assume(ez.NOT(ez.expression(ezSAT::OpOr, satgen.importUndefSigSpec(pi))));

		for (size_t i = 0; i < pi.size(); i++)
		{
			RTLIL::SigSpec test_sig(pi[i]);
			RTLIL::SigSpec rest_sig(pi);
			rest_sig.remove(i, 1);

			int test_sig_a, test_sig_b;
			std::vector<int> rest_sig_a, rest_sig_b;

			satgen.setContext(&sigmap, "A");
			test_sig_a = satgen.importSigSpec(test_sig).front();
			rest_sig_a = satgen.importSigSpec(rest_sig);

			satgen.setContext(&sigmap, "B");
			test_sig_b = satgen.importSigSpec(test_sig).front();
			rest_sig_b = satgen.importSigSpec(rest_sig);

			if (ez.solve(ez.vec_eq(rest_sig_a, rest_sig_b), ez.XOR(output_a, output_b), ez.XOR(test_sig_a, test_sig_b), ez.NOT(output_undef_a), ez.NOT(output_undef_b))) {
				if (verbose_level >= 2)
					log("      Result for input %s: pass\n", log_signal(test_sig));
				reduced_inputs.push_back(pi[i]);
			} else {
				if (verbose_level >= 2)
					log("      Result for input %s: strip\n", log_signal(test_sig));
			}
		}

		if (verbose_level >= 1)
			log("      Reduced input cone contains %d inputs.\n", int(reduced_inputs.size()));
	}
};

struct PerformReduction
{
	SigMap &sigmap;
	drivers_t &drivers;
	std::set<std::pair<RTLIL::SigBit, RTLIL::SigBit>> &inv_pairs;

	ezDefaultSAT ez;
	SatGen satgen;

	std::vector<int> sat_pi, sat_out, sat_def;
	std::vector<RTLIL::SigBit> out_bits, pi_bits;
	std::vector<bool> out_inverted;
	std::vector<int> out_depth;

	int register_cone_worker(std::set<RTLIL::Cell*> &celldone, std::map<RTLIL::SigBit, int> &sigdepth, RTLIL::SigBit out)
	{
		if (out.wire == NULL)
			return 0;
		if (sigdepth.count(out) != 0)
			return sigdepth.at(out);
		sigdepth[out] = 0;

		if (drivers.count(out) != 0) {
			std::pair<RTLIL::Cell*, std::set<RTLIL::SigBit>> &drv = drivers.at(out);
			if (celldone.count(drv.first) == 0) {
				if (!satgen.importCell(drv.first))
					log_error("Can't create SAT model for cell %s (%s)!\n", RTLIL::id2cstr(drv.first->name), RTLIL::id2cstr(drv.first->type));
				celldone.insert(drv.first);
			}
			int max_child_dept = 0;
			for (auto &bit : drv.second)
				max_child_dept = std::max(register_cone_worker(celldone, sigdepth, bit), max_child_dept);
			sigdepth[out] = max_child_dept + 1;
		} else {
			pi_bits.push_back(out);
			sat_pi.push_back(satgen.importSigSpec(out).front());
			ez.assume(ez.NOT(satgen.importUndefSigSpec(out).front()));
		}

		return sigdepth[out];
	}

	PerformReduction(SigMap &sigmap, drivers_t &drivers, std::set<std::pair<RTLIL::SigBit, RTLIL::SigBit>> &inv_pairs, std::vector<RTLIL::SigBit> &bits) :
			sigmap(sigmap), drivers(drivers), inv_pairs(inv_pairs), satgen(&ez, &sigmap), out_bits(bits)
	{
		satgen.model_undef = true;

		std::set<RTLIL::Cell*> celldone;
		std::map<RTLIL::SigBit, int> sigdepth;

		for (auto &bit : bits) {
			out_depth.push_back(register_cone_worker(celldone, sigdepth, bit));
			sat_out.push_back(satgen.importSigSpec(bit).front());
			sat_def.push_back(ez.NOT(satgen.importUndefSigSpec(bit).front()));
		}

		if (inv_mode) {
			if (!ez.solve(sat_out, out_inverted, ez.expression(ezSAT::OpAnd, sat_def)))
				log_error("Solving for initial model failed!\n");
			for (size_t i = 0; i < sat_out.size(); i++)
				if (out_inverted.at(i))
					sat_out[i] = ez.NOT(sat_out[i]);
		} else
			out_inverted = std::vector<bool>(sat_out.size(), false);
	}

	void analyze(std::vector<std::vector<equiv_bit_t>> &results, std::vector<int> &bucket, int level)
	{
		if (bucket.size() <= 1)
			return;

		if (verbose_level >= 1)
			log("%*s  Trying to shatter bucket with %d signals.\n", 2*level, "", int(bucket.size()));

		std::vector<int> sat_list, sat_inv_list;
		for (int idx : bucket) {
			sat_list.push_back(ez.AND(sat_out[idx], sat_def[idx]));
			sat_inv_list.push_back(ez.AND(ez.NOT(sat_out[idx]), sat_def[idx]));
		}

		std::vector<int> modelVars = sat_out;
		std::vector<bool> model;

		if (verbose_level >= 2) {
			modelVars.insert(modelVars.end(), sat_def.begin(), sat_def.end());
			modelVars.insert(modelVars.end(), sat_pi.begin(), sat_pi.end());
		}

		if (ez.solve(modelVars, model, ez.expression(ezSAT::OpOr, sat_list), ez.expression(ezSAT::OpOr, sat_inv_list)))
		{
			if (verbose_level >= 2) {
				for (size_t i = 0; i < pi_bits.size(); i++)
					log("%*s       -> PI  %c == %s\n", 2*level, "", model[2*sat_out.size() + i] ? '1' : '0', log_signal(pi_bits[i]));
				for (int idx : bucket)
					log("%*s       -> OUT %c == %s%s\n", 2*level, "", model[sat_out.size() + idx] ? model[idx] ? '1' : '0' : 'x',
							out_inverted.at(idx) ? "~" : "", log_signal(out_bits[idx]));
			}

			std::vector<int> buckets[2];
			for (int idx : bucket)
				buckets[model[idx] ? 1 : 0].push_back(idx);
			analyze(results, buckets[0], level+1);
			analyze(results, buckets[1], level+1);
		}
		else
		{
			if (verbose_level >= 1) {
				log("%*s    Found %d equivialent signals:", 2*level, "", int(bucket.size()));
				for (int idx : bucket)
					log("%s%s%s", idx == bucket.front() ? " " : ", ", out_inverted[idx] ? "~" : "", log_signal(out_bits[idx]));
				log("\n");
			}

			std::vector<equiv_bit_t> result;
			for (int idx : bucket) {
				equiv_bit_t bit;
				bit.depth = out_depth[idx];
				bit.inverted = out_inverted[idx];
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

	void analyze(std::vector<std::vector<equiv_bit_t>> &results)
	{
		std::vector<int> bucket;
		for (size_t i = 0; i < sat_out.size(); i++)
			bucket.push_back(i);
		analyze(results, bucket, 1);
	}
};

struct FreduceHelper
{
	RTLIL::Module *module;

	SigMap sigmap;
	drivers_t drivers;
	std::set<std::pair<RTLIL::SigBit, RTLIL::SigBit>> inv_pairs;

	FreduceHelper(RTLIL::Module *module) : module(module), sigmap(module)
	{
	}

	int run()
	{
		log("Running functional reduction on module %s:\n", RTLIL::id2cstr(module->name));

		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();

		std::vector<std::set<RTLIL::SigBit>> batches;
		for (auto &it : module->cells) {
			if (ct.cell_known(it.second->type)) {
				std::set<RTLIL::SigBit> inputs, outputs;
				for (auto &port : it.second->connections) {
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
			}
			if (inv_mode && it.second->type == "$_INV_")
				inv_pairs.insert(std::pair<RTLIL::SigBit, RTLIL::SigBit>(sigmap(it.second->connections.at("\\A")), sigmap(it.second->connections.at("\\Y"))));
		}

		int bits_count = 0;
		std::map<std::vector<RTLIL::SigBit>, std::vector<RTLIL::SigBit>> buckets;
		for (auto &batch : batches)
		{
			RTLIL::SigSpec batch_sig(std::vector<RTLIL::SigBit>(batch.begin(), batch.end()));
			batch_sig.optimize();

			log("  Finding reduced input cone for signal batch %s%c\n", log_signal(batch_sig), verbose_level ? ':' : '.');

			FindReducedInputs infinder(sigmap, drivers);
			for (auto &bit : batch) {
				std::vector<RTLIL::SigBit> inputs;
				infinder.analyze(inputs, bit);
				buckets[inputs].push_back(bit);
				bits_count++;
			}
		}
		log("  Sorted %d signal bits into %d buckets.\n", bits_count, int(buckets.size()));

		std::vector<std::vector<equiv_bit_t>> equiv;
		for (auto &bucket : buckets)
		{
			if (bucket.second.size() == 1)
				continue;

			RTLIL::SigSpec bucket_sig(bucket.second);
			bucket_sig.optimize();

			log("  Trying to shatter bucket %s%c\n", log_signal(bucket_sig), verbose_level ? ':' : '.');
			PerformReduction worker(sigmap, drivers, inv_pairs, bucket.second);
			worker.analyze(equiv);
		}

		log("  Rewiring %d equivialent groups:\n", int(equiv.size()));
		int rewired_sigbits = 0;
		for (auto &grp : equiv)
		{
			log("    Using as master for group: %s\n", log_signal(grp.front().bit));

			RTLIL::SigSpec inv_sig;
			for (size_t i = 1; i < grp.size(); i++)
			{
				log("      Connect slave%s: %s\n", grp[i].inverted ? " using inverter" : "", log_signal(grp[i].bit));

				RTLIL::Cell *drv = drivers.at(grp[i].bit).first;
				RTLIL::Wire *dummy_wire = module->new_wire(1, NEW_ID);
				for (auto &port : drv->connections)
					sigmap(port.second).replace(grp[i].bit, dummy_wire, &port.second);

				if (grp[i].inverted)
				{
					if (inv_sig.width == 0)
					{
						inv_sig = module->new_wire(1, NEW_ID);

						RTLIL::Cell *inv_cell = new RTLIL::Cell;
						inv_cell->name = NEW_ID;
						inv_cell->type = "$_INV_";
						inv_cell->connections["\\A"] = grp[0].bit;
						inv_cell->connections["\\Y"] = inv_sig;
						module->add(inv_cell);
					}

					module->connections.push_back(RTLIL::SigSig(grp[i].bit, inv_sig));
				}
				else
					module->connections.push_back(RTLIL::SigSig(grp[i].bit, grp[0].bit));

				rewired_sigbits++;
			}
		}

		log("  Rewired a total of %d signal bits in module %s.\n", rewired_sigbits, RTLIL::id2cstr(module->name));
		return rewired_sigbits;
	}
};

} /* namespace */

struct FreducePass : public Pass {
	FreducePass() : Pass("freduce", "perform functional reduction") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    freduce [options] [selection]\n");
		log("\n");
		log("This pass performs functional reduction in the circuit. I.e. if two nodes are\n");
		log("equivialent, they are merged to one node and one of the redundant drivers is\n");
		log("removed.\n");
		log("\n");
		log("    -v, -vv\n");
		log("        enable verbose or very verbose output\n");
		log("\n");
		log("    -inv\n");
		log("        enable explicit handling of inverted signals\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		verbose_level = 0;
		inv_mode = false;

		log_header("Executing FREDUCE pass (perform functional reduction).\n");

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
			break;
		}
		extra_args(args, argidx, design);

		int bitcount = 0;
		for (auto &mod_it : design->modules) {
			RTLIL::Module *module = mod_it.second;
			if (design->selected(module))
				bitcount += FreduceHelper(module).run();
		}

		log("Rewired a total of %d signal bits.\n", bitcount);
	}
} FreducePass;
 
