#include "kernel/yosys.h"
#include "libs/ezsat/ezcmdline.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EzCmdlineTestPass : public Pass {
	EzCmdlineTestPass() : Pass("ezcmdline_test", "smoke-test ezCmdlineSAT") { }
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string cmd;
		size_t argidx = 1;

		while (argidx < args.size()) {
			if (args[argidx] == "-cmd" && argidx + 1 < args.size()) {
				cmd = args[argidx + 1];
				argidx += 2;
				continue;
			}
			break;
		}

		extra_args(args, argidx, design);

		if (cmd.empty())
			log_error("Missing -cmd <solver> argument.\n");

		ezCmdlineSAT sat(cmd);
		sat.non_incremental();

		// assume("A") adds a permanent CNF clause "A".
		sat.assume(sat.VAR("A"));

		std::vector<int> model_expressions;
		std::vector<bool> model_values;
		model_expressions.push_back(sat.VAR("A"));

		// Expect SAT with A=true.
		if (!sat.solve(model_expressions, model_values))
			log_error("ezCmdlineSAT SAT case failed.\n");
		if (model_values.size() != 1 || !model_values[0])
			log_error("ezCmdlineSAT SAT model mismatch.\n");

		// Passing NOT("A") here adds a temporary unit clause for this solve call,
		// so the solver sees A && !A and must return UNSAT.
		if (sat.solve(model_expressions, model_values, sat.NOT("A")))
			log_error("ezCmdlineSAT UNSAT case failed.\n");

		log("ezcmdline_test passed!\n");
	}
} EzCmdlineTestPass;

PRIVATE_NAMESPACE_END
