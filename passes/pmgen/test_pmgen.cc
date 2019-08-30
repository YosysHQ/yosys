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

// for peepopt_pm
bool did_something;

#include "passes/pmgen/test_pmgen_pm.h"
#include "passes/pmgen/ice40_dsp_pm.h"
#include "passes/pmgen/xilinx_srl_pm.h"
#include "passes/pmgen/peepopt_pm.h"

void reduce_chain(test_pmgen_pm &pm)
{
	auto &st = pm.st_reduce;
	auto &ud = pm.ud_reduce;

	if (ud.longest_chain.empty())
		return;

	log("Found chain of length %d (%s):\n", GetSize(ud.longest_chain), log_id(st.first->type));

	SigSpec A;
	SigSpec Y = ud.longest_chain.front().first->getPort(ID(Y));
	auto last_cell = ud.longest_chain.back().first;

	for (auto it : ud.longest_chain) {
		auto cell = it.first;
		if (cell == last_cell) {
			A.append(cell->getPort(ID(A)));
			A.append(cell->getPort(ID(B)));
		} else {
			A.append(cell->getPort(it.second == ID(A) ? ID(B) : ID(A)));
		}
		log("    %s\n", log_id(cell));
		pm.autoremove(cell);
	}

	Cell *c;

	if (last_cell->type == ID($_AND_))
		c = pm.module->addReduceAnd(NEW_ID, A, Y);
	else if (last_cell->type == ID($_OR_))
		c = pm.module->addReduceOr(NEW_ID, A, Y);
	else if (last_cell->type == ID($_XOR_))
		c = pm.module->addReduceXor(NEW_ID, A, Y);
	else
		log_abort();

	log("    -> %s (%s)\n", log_id(c), log_id(c->type));
}

void reduce_tree(test_pmgen_pm &pm)
{
	auto &st = pm.st_reduce;
	auto &ud = pm.ud_reduce;

	if (ud.longest_chain.empty())
		return;

	SigSpec A = ud.leaves;
	SigSpec Y = st.first->getPort(ID(Y));
	pm.autoremove(st.first);

	log("Found %s tree with %d leaves for %s (%s).\n", log_id(st.first->type),
			GetSize(A), log_signal(Y), log_id(st.first));

	Cell *c;

	if (st.first->type == ID($_AND_))
		c = pm.module->addReduceAnd(NEW_ID, A, Y);
	else if (st.first->type == ID($_OR_))
		c = pm.module->addReduceOr(NEW_ID, A, Y);
	else if (st.first->type == ID($_XOR_))
		c = pm.module->addReduceXor(NEW_ID, A, Y);
	else
		log_abort();

	log("    -> %s (%s)\n", log_id(c), log_id(c->type));
}

void opt_eqpmux(test_pmgen_pm &pm)
{
	auto &st = pm.st_eqpmux;

	SigSpec Y = st.pmux->getPort(ID::Y);
	int width = GetSize(Y);

	SigSpec EQ = st.pmux->getPort(ID::B).extract(st.pmux_slice_eq*width, width);
	SigSpec NE = st.pmux->getPort(ID::B).extract(st.pmux_slice_ne*width, width);

	log("Found eqpmux circuit driving %s (eq=%s, ne=%s, pmux=%s).\n",
			log_signal(Y), log_id(st.eq), log_id(st.ne), log_id(st.pmux));

	pm.autoremove(st.pmux);
	Cell *c = pm.module->addMux(NEW_ID, NE, EQ, st.eq->getPort(ID::Y), Y);
	log("    -> %s (%s)\n", log_id(c), log_id(c->type));
}

#define GENERATE_PATTERN(pmclass, pattern) \
	generate_pattern<pmclass>([](pmclass &pm, std::function<void()> f){ return pm.run_ ## pattern(f); }, #pmclass, #pattern, design)

void pmtest_addports(Module *module)
{
	pool<SigBit> driven_bits, used_bits;
	SigMap sigmap(module);
	int icnt = 0, ocnt = 0;

	for (auto cell : module->cells())
	for (auto conn : cell->connections())
	{
		if (cell->input(conn.first))
			for (auto bit : sigmap(conn.second))
				used_bits.insert(bit);
		if (cell->output(conn.first))
			for (auto bit : sigmap(conn.second))
				driven_bits.insert(bit);
	}

	for (auto wire : vector<Wire*>(module->wires()))
	{
		SigSpec ibits, obits;
		for (auto bit : sigmap(wire)) {
			if (!used_bits.count(bit))
				obits.append(bit);
			if (!driven_bits.count(bit))
				ibits.append(bit);
		}
		if (!ibits.empty()) {
			Wire *w = module->addWire(stringf("\\i%d", icnt++), GetSize(ibits));
			w->port_input = true;
			module->connect(ibits, w);
		}
		if (!obits.empty()) {
			Wire *w = module->addWire(stringf("\\o%d", ocnt++), GetSize(obits));
			w->port_output = true;
			module->connect(w, obits);
		}
	}

	module->fixup_ports();
}

template <class pm>
void generate_pattern(std::function<void(pm&,std::function<void()>)> run, const char *pmclass, const char *pattern, Design *design)
{
	log("Generating \"%s\" patterns for pattern matcher \"%s\".\n", pattern, pmclass);

	int modcnt = 0;
	int maxmodcnt = 100;
	int maxsubcnt = 4;
	int timeout = 0;
	vector<Module*> mods;

	while (modcnt < maxmodcnt)
	{
		int submodcnt = 0, itercnt = 0, cellcnt = 0;
		Module *mod = design->addModule(NEW_ID);

		while (modcnt < maxmodcnt && submodcnt < maxsubcnt && itercnt++ < 1000)
		{
			if (timeout++ > 10000)
				log_error("pmgen generator is stuck: 10000 iterations with no matching module generated.\n");

			pm matcher(mod, mod->cells());

			matcher.rng(1);
			matcher.rngseed += modcnt;
			matcher.rng(1);
			matcher.rngseed += submodcnt;
			matcher.rng(1);
			matcher.rngseed += itercnt;
			matcher.rng(1);
			matcher.rngseed += cellcnt;
			matcher.rng(1);

			if (GetSize(mod->cells()) != cellcnt)
			{
				bool found_match = false;
				run(matcher, [&](){ found_match = true; });
				cellcnt = GetSize(mod->cells());

				if (found_match) {
					Module *m = design->addModule(stringf("\\pmtest_%s_%s_%05d",
							pmclass, pattern, modcnt++));
					log("Creating module %s with %d cells.\n", log_id(m), cellcnt);
					mod->cloneInto(m);
					pmtest_addports(m);
					mods.push_back(m);
					submodcnt++;
					timeout = 0;
				}
			}

			matcher.generate_mode = true;
			run(matcher, [](){});
		}

		if (submodcnt && maxsubcnt < (1 << 16))
			maxsubcnt *= 2;

		design->remove(mod);
	}

	Module *m = design->addModule(stringf("\\pmtest_%s_%s", pmclass, pattern));
	log("Creating module %s with %d cells.\n", log_id(m), GetSize(mods));
	for (auto mod : mods) {
		Cell *c = m->addCell(mod->name, mod->name);
		for (auto port : mod->ports) {
			Wire *w = m->addWire(NEW_ID, GetSize(mod->wire(port)));
			c->setPort(port, w);
		}
	}
	pmtest_addports(m);
}

struct TestPmgenPass : public Pass {
	TestPmgenPass() : Pass("test_pmgen", "test pass for pmgen") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_pmgen -reduce_chain [options] [selection]\n");
		log("\n");
		log("Demo for recursive pmgen patterns. Map chains of AND/OR/XOR to $reduce_*.\n");
		log("\n");

		log("\n");
		log("    test_pmgen -reduce_tree [options] [selection]\n");
		log("\n");
		log("Demo for recursive pmgen patterns. Map trees of AND/OR/XOR to $reduce_*.\n");
		log("\n");

		log("\n");
		log("    test_pmgen -eqpmux [options] [selection]\n");
		log("\n");
		log("Demo for recursive pmgen patterns. Optimize EQ/NE/PMUX circuits.\n");
		log("\n");

		log("\n");
		log("    test_pmgen -generate [options] <pattern_name>\n");
		log("\n");
		log("Create modules that match the specified pattern.\n");
		log("\n");
	}

	void execute_reduce_chain(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing TEST_PMGEN pass (-reduce_chain).\n");

		size_t argidx;
		for (argidx = 2; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			while (test_pmgen_pm(module, module->selected_cells()).run_reduce(reduce_chain)) {}
	}

	void execute_reduce_tree(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing TEST_PMGEN pass (-reduce_tree).\n");

		size_t argidx;
		for (argidx = 2; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			test_pmgen_pm(module, module->selected_cells()).run_reduce(reduce_tree);
	}

	void execute_eqpmux(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing TEST_PMGEN pass (-eqpmux).\n");

		size_t argidx;
		for (argidx = 2; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			test_pmgen_pm(module, module->selected_cells()).run_eqpmux(opt_eqpmux);
	}

	void execute_generate(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing TEST_PMGEN pass (-generate).\n");

		size_t argidx;
		for (argidx = 2; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}

		if (argidx+1 != args.size())
			log_cmd_error("Expected exactly one pattern.\n");

		string pattern = args[argidx];

		if (pattern == "reduce")
			return GENERATE_PATTERN(test_pmgen_pm, reduce);

		if (pattern == "eqpmux")
			return GENERATE_PATTERN(test_pmgen_pm, eqpmux);

		if (pattern == "ice40_dsp")
			return GENERATE_PATTERN(ice40_dsp_pm, ice40_dsp);

		if (pattern == "xilinx_srl.fixed")
			return GENERATE_PATTERN(xilinx_srl_pm, fixed);
		if (pattern == "xilinx_srl.variable")
			return GENERATE_PATTERN(xilinx_srl_pm, variable);

		if (pattern == "peepopt-muldiv")
			return GENERATE_PATTERN(peepopt_pm, muldiv);

		if (pattern == "peepopt-shiftmul")
			return GENERATE_PATTERN(peepopt_pm, shiftmul);

		log_cmd_error("Unknown pattern: %s\n", pattern.c_str());
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		if (GetSize(args) > 1)
		{
			if (args[1] == "-reduce_chain")
				return execute_reduce_chain(args, design);
			if (args[1] == "-reduce_tree")
				return execute_reduce_tree(args, design);
			if (args[1] == "-eqpmux")
				return execute_eqpmux(args, design);
			if (args[1] == "-generate")
				return execute_generate(args, design);
		}
		help();
		log_cmd_error("Missing or unsupported mode parameter.\n");
	}
} TestPmgenPass;

PRIVATE_NAMESPACE_END
