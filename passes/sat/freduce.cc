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

#define NUM_INITIAL_RANDOM_TEST_VECTORS 10

namespace {

struct FreduceHelper
{
	RTLIL::Design *design;
	RTLIL::Module *module;

	ezDefaultSAT ez;
	SigMap sigmap;
	CellTypes ct;
	SatGen satgen;
	ConstEval ce;

	SigPool inputs, nodes;
	RTLIL::SigSpec input_sigs;

	SigSet<RTLIL::SigSpec> driver_inputs;
	std::vector<RTLIL::Const> test_vectors;
	std::map<RTLIL::SigSpec, RTLIL::Const> node_to_data;
	std::map<RTLIL::SigSpec, RTLIL::SigSpec> node_result;

	std::vector<RTLIL::SigSig> result_groups;
	SigPool groups_unlink;

	uint32_t xorshift32_state;

        uint32_t xorshift32() {
		xorshift32_state ^= xorshift32_state << 13;
		xorshift32_state ^= xorshift32_state >> 17;
		xorshift32_state ^= xorshift32_state << 5;
		return xorshift32_state;
	}

	FreduceHelper(RTLIL::Design *design, RTLIL::Module *module) :
			design(design), module(module), sigmap(module), satgen(&ez, design, &sigmap), ce(module)
	{
		ct.setup_internals();
		ct.setup_stdcells();

		xorshift32_state = 123456789;
		xorshift32();
		xorshift32();
		xorshift32();
	}

	void run_test(RTLIL::SigSpec test_vec)
	{
		ce.clear();
		ce.set(input_sigs, test_vec.as_const());

		for (auto &bit : nodes.bits) {
			RTLIL::SigSpec nodesig(bit.first, 1, bit.second), nodeval = nodesig;
			if (!ce.eval(nodeval))
				log_error("Evaluation of node %s failed!\n", log_signal(nodesig));
			node_to_data[nodesig].bits.push_back(nodeval.as_const().bits.at(0));
		}
	}

	void dump_node_data()
	{
		int max_node_len = 20;
		for (auto &it : node_to_data)
			max_node_len = std::max(max_node_len, int(strlen(log_signal(it.first))));
		for (auto &it : node_to_data)
			log("  %-*s %s\n", max_node_len+5, log_signal(it.first), log_signal(it.second));
	}

	void check(RTLIL::SigSpec sig1, RTLIL::SigSpec sig2)
	{
		log("  performing SAT proof:  %s == %s  ->", log_signal(sig1), log_signal(sig2));

		std::vector<int> vec1 = satgen.importSigSpec(sig1);
		std::vector<int> vec2 = satgen.importSigSpec(sig2);
		std::vector<int> model = satgen.importSigSpec(input_sigs);
		std::vector<bool> testvect;

		if (ez.solve(model, testvect, ez.vec_ne(vec1, vec2))) {
			RTLIL::SigSpec testvect_sig;
			for (int i = 0; i < input_sigs.width; i++)
				testvect_sig.append(testvect.at(i) ? RTLIL::State::S1 : RTLIL::State::S0);
			testvect_sig.optimize();
			log(" failed: %s\n", log_signal(testvect_sig));
			test_vectors.push_back(testvect_sig.as_const());
			run_test(testvect_sig);
		} else {
			log(" success.\n");
			if (!sig1.is_fully_const())
				node_result[sig1].append(sig2);
			if (!sig2.is_fully_const())
				node_result[sig2].append(sig1);
		}
	}

	void analyze_const()
	{
		for (auto &it : node_to_data)
		{
			if (node_result.count(it.first))
				continue;
			if (it.second == RTLIL::Const(RTLIL::State::S0, it.second.bits.size()))
				check(it.first, RTLIL::SigSpec(RTLIL::State::S0));
			if (it.second == RTLIL::Const(RTLIL::State::S1, it.second.bits.size()))
				check(it.first, RTLIL::SigSpec(RTLIL::State::S1));
		}
	}

	void analyze_alias()
	{
	restart:
		std::map<RTLIL::Const, RTLIL::SigSpec> reverse_map;

		for (auto &it : node_to_data) {
			if (node_result.count(it.first) && node_result.at(it.first).is_fully_const())
				continue;
			reverse_map[it.second].append(it.first);
		}

		for (auto &it : reverse_map)
		{
			if (it.second.width <= 1)
				continue;

			it.second.expand();
			for (int i = 0; i < it.second.width; i++)
			for (int j = i+1; j < it.second.width; j++) {
				RTLIL::SigSpec sig1 = it.second.chunks.at(i), sig2 = it.second.chunks.at(j);
				if (node_result.count(sig1) && node_result.count(sig2))
					continue;
				if (node_to_data.at(sig1) != node_to_data.at(sig2))
					goto restart;
				check(it.second.chunks.at(i), it.second.chunks.at(j));
			}
		}
	}

	bool topsort_helper(RTLIL::SigSpec cursor, RTLIL::SigSpec stoplist)
	{
		if (stoplist.extract(cursor).width != 0)
			return false;

		stoplist.append(cursor);
		std::set<RTLIL::SigSpec> next = driver_inputs.find(cursor);

		for (auto &it : next)
			if (!topsort_helper(it, stoplist))
				return false;

		return true;
	}

	// KISS topological sort of bits in signal. return one element of sig
	// without dependencies to the others (or empty if input is not a DAG).
	RTLIL::SigSpec topsort(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (auto &c : sig.chunks) {
			RTLIL::SigSpec stoplist = sig;
			stoplist.remove(c);
			if (topsort_helper(c, stoplist))
				return c;
		}
		return RTLIL::SigSpec();
	}

	void analyze_groups()
	{
		SigMap to_group_major;
		for (auto &it : node_result) {
			it.second.expand();
			for (auto &c : it.second.chunks)
				to_group_major.add(it.first, c);
		}

		std::map<RTLIL::SigSpec, RTLIL::SigSpec> major_to_rest;
		for (auto &it : node_result)
			major_to_rest[to_group_major(it.first)].append(it.first);

		for (auto &it : major_to_rest)
		{
			RTLIL::SigSig group = it;

			if (!it.first.is_fully_const()) {
				group.first = topsort(it.second);
				if (group.first.width == 0)
					log_error("Operating on non-DAG input: failed to find topological root for `%s'.\n", log_signal(it.second));
				group.second.remove(group.first);
			}

			group.first.optimize();
			group.second.sort_and_unify();
			result_groups.push_back(group);
		}
	}

	void run()
	{
		log("\nFunctionally reduce module %s:\n", RTLIL::id2cstr(module->name));
		
		// find inputs and nodes (nets driven by internal cells)
		// add all internal cells to sat solver

		for (auto &cell_it : module->cells) {
			RTLIL::Cell *cell = cell_it.second;
			if (!ct.cell_known(cell->type))
				continue;
			RTLIL::SigSpec cell_inputs, cell_outputs;
			for (auto &conn : cell->connections)
				if (ct.cell_output(cell->type, conn.first)) {
					nodes.add(sigmap(conn.second));
					cell_outputs.append(sigmap(conn.second));
				} else {
					inputs.add(sigmap(conn.second));
					cell_inputs.append(sigmap(conn.second));
				}
			cell_inputs.sort_and_unify();
			cell_outputs.sort_and_unify();
			cell_inputs.expand();
			for (auto &c : cell_inputs.chunks)
				if (c.wire != NULL)
					driver_inputs.insert(cell_outputs, c);
			if (!satgen.importCell(cell))
				log_error("Failed to import cell to SAT solver: %s (%s)\n",
						RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
		}
		inputs.del(nodes);
		nodes.add(inputs);
		log("  found %d nodes (%d inputs).\n", int(nodes.size()), int(inputs.size()));

		// initialise input_sigs and add all-zero, all-one and a few random test vectors

		input_sigs = inputs.export_all();
		test_vectors.push_back(RTLIL::SigSpec(RTLIL::State::S0, input_sigs.width).as_const());
		test_vectors.push_back(RTLIL::SigSpec(RTLIL::State::S1, input_sigs.width).as_const());

		for (int i = 0; i < NUM_INITIAL_RANDOM_TEST_VECTORS; i++) {
			RTLIL::SigSpec sig;
			for (int j = 0; j < input_sigs.width; j++)
				sig.append(xorshift32() % 2 ? RTLIL::State::S1 : RTLIL::State::S0);
			sig.optimize();
			assert(sig.width == input_sigs.width);
			test_vectors.push_back(sig.as_const());
		}

		for (auto &test_vec : test_vectors)
			run_test(test_vec);

		// run the analysis

		analyze_const();
		analyze_alias();

		log("  input vector: %s\n", log_signal(input_sigs));
		for (auto &test_vec : test_vectors)
			log("  test vector: %s\n", log_signal(test_vec));

		analyze_groups();

		for (auto &it : result_groups) {
			log("  found group: %s -> %s\n", log_signal(it.first), log_signal(it.second));
			groups_unlink.add(it.second);
		}

		for (auto &cell_it : module->cells) {
			RTLIL::Cell *cell = cell_it.second;
			if (!ct.cell_known(cell->type))
				continue;
			for (auto &conn : cell->connections)
				if (ct.cell_output(cell->type, conn.first)) {
					RTLIL::SigSpec sig = sigmap(conn.second);
					sig.expand();
					bool did_something = false;
					for (auto &c : sig.chunks) {
						if (c.wire == NULL || !groups_unlink.check_any(c))
							continue;
						c.wire = new RTLIL::Wire;
						c.wire->name = NEW_ID;
						module->add(c.wire);
						assert(c.width == 1);
						c.offset = 0;
						did_something = true;
					}
					if (did_something) {
						sig.optimize();
						conn.second = sig;
					}
				}
		}

		for (auto &it : result_groups) {
			it.second.expand();
			for (auto &c : it.second.chunks)
				module->connections.push_back(RTLIL::SigSig(c, it.first));
		}
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
		// log("    -enable_invert\n");
		// log("        also detect nodes that are inverse to each other.\n");
		// log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool enable_invert = false;

		log_header("Executing FREDUCE pass (perform functional reduction).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-enable_invert") {
				enable_invert = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules)
		{
			RTLIL::Module *module = mod_it.second;
			if (design->selected(module))
				FreduceHelper(design, module).run();
		}
	}
} FreducePass;
 
