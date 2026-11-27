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

#include "kernel/yosys.h"
#include "passes/pmgen/test_pmgen.h"
#include "techlibs/xilinx/xilinx_srl.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "generate.h"

void reduce_chain(TestPmgenReduce &pm, const TestPmgenReduce::Match &st)
{
	if (pm.longest_chain.empty())
		return;

	log("Found chain of length %d (%s):\n", GetSize(pm.longest_chain), st.first->type.unescape());

	SigSpec A;
	SigSpec Y = pm.longest_chain.front().first->getPort(ID::Y);
	auto last_cell = pm.longest_chain.back().first;

	for (auto it : pm.longest_chain) {
		auto cell = it.first;
		if (cell == last_cell) {
			A.append(cell->getPort(ID::A));
			A.append(cell->getPort(ID::B));
		} else {
			A.append(cell->getPort(it.second == ID::A ? ID::B : ID::A));
		}
		log("    %s\n", cell);
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

	log("    -> %s (%s)\n", c, c->type.unescape());
}

void reduce_tree(TestPmgenReduce &pm, const TestPmgenReduce::Match &st)
{
	if (pm.longest_chain.empty())
		return;

	SigSpec A = pm.leaves;
	SigSpec Y = st.first->getPort(ID::Y);
	pm.autoremove(st.first);

	log("Found %s tree with %d leaves for %s (%s).\n", st.first->type.unescape(),
			GetSize(A), log_signal(Y), st.first);

	Cell *c;

	if (st.first->type == ID($_AND_))
		c = pm.module->addReduceAnd(NEW_ID, A, Y);
	else if (st.first->type == ID($_OR_))
		c = pm.module->addReduceOr(NEW_ID, A, Y);
	else if (st.first->type == ID($_XOR_))
		c = pm.module->addReduceXor(NEW_ID, A, Y);
	else
		log_abort();

	log("    -> %s (%s)\n", c, c->type.unescape());
}

void opt_eqpmux(TestPmgenEqpmux &pm, const TestPmgenEqpmux::Match &st)
{
	SigSpec Y = st.pmux->getPort(ID::Y);
	int width = GetSize(Y);

	SigSpec EQ = st.pmux->getPort(ID::B).extract(st.pmux_slice_eq*width, width);
	SigSpec NE = st.pmux->getPort(ID::B).extract(st.pmux_slice_ne*width, width);

	log("Found eqpmux circuit driving %s (eq=%s, ne=%s, pmux=%s).\n",
			log_signal(Y), st.eq, st.ne, st.pmux);

	pm.autoremove(st.pmux);
	Cell *c = pm.module->addMux(NEW_ID, NE, EQ, st.eq->getPort(ID::Y), Y);
	log("    -> %s (%s)\n", c, c->type.unescape());
}

struct TestPmgenPass : public Pass {
	TestPmgenPass() : Pass("test_pmgen", "test pass for pattern matchers") {
		internal();
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_pmgen -reduce_chain [options] [selection]\n");
		log("\n");
		log("Demo for recursive pattern matchers. Map chains of AND/OR/XOR to $reduce_*.\n");
		log("\n");

		log("\n");
		log("    test_pmgen -reduce_tree [options] [selection]\n");
		log("\n");
		log("Demo for recursive pattern matchers. Map trees of AND/OR/XOR to $reduce_*.\n");
		log("\n");

		log("\n");
		log("    test_pmgen -eqpmux [options] [selection]\n");
		log("\n");
		log("Demo for recursive pattern matchers. Optimize EQ/NE/PMUX circuits.\n");
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

		for (auto module : design->selected_modules()) {
			bool found_match = true;
			while (found_match) {
				MatchContext ctx(module);
				found_match = TestPmgenReduce(ctx, module->selected_cells()).run(reduce_chain) > 0;
			}
		}
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

		for (auto module : design->selected_modules()) {
			MatchContext ctx(module);
			TestPmgenReduce(ctx, module->selected_cells()).run(reduce_tree);
		}
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

		for (auto module : design->selected_modules()) {
			MatchContext ctx(module);
			TestPmgenEqpmux(ctx, module->selected_cells()).run(opt_eqpmux);
		}
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
			return generate_pattern<TestPmgenReduce>("test_pmgen_pm", "reduce", design);

		if (pattern == "eqpmux")
			return generate_pattern<TestPmgenEqpmux>("test_pmgen_pm", "eqpmux", design);

		if (pattern == "xilinx_srl.fixed")
			return generate_pattern<XilinxSrlFixed>("xilinx_srl_pm", "fixed", design);
		if (pattern == "xilinx_srl.variable")
			return generate_pattern<XilinxSrlVariable>("xilinx_srl_pm", "variable", design);

		log_cmd_error("Unknown pattern: %s\n", pattern);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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
