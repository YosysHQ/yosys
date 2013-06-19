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
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>

namespace {

/* this should only be used for regression testing of ConstEval -- see tests/xsthammer */
struct BruteForceEquivChecker
{
	RTLIL::Module *mod1, *mod2;
	RTLIL::SigSpec mod1_inputs, mod1_outputs;
	RTLIL::SigSpec mod2_inputs, mod2_outputs;
	int counter, errors;

	void run_checker(RTLIL::SigSpec &inputs)
	{
		if (inputs.width < mod1_inputs.width) {
			RTLIL::SigSpec inputs0 = inputs, inputs1 = inputs;
			inputs0.append(RTLIL::Const(0, 1));
			inputs1.append(RTLIL::Const(1, 1));
			run_checker(inputs0);
			run_checker(inputs1);
			return;
		}

		inputs.optimize();

		ConstEval ce1(mod1), ce2(mod2);
		ce1.set(mod1_inputs, inputs.as_const());
		ce2.set(mod2_inputs, inputs.as_const());

		RTLIL::SigSpec sig1 = mod1_outputs, undef1;
		RTLIL::SigSpec sig2 = mod2_outputs, undef2;

		if (!ce1.eval(sig1, undef1))
			log("Failed ConstEval of module 1 outputs at signal %s (input: %s = %s).\n",
					log_signal(undef1), log_signal(mod1_inputs), log_signal(inputs));
		if (!ce2.eval(sig2, undef2))
			log("Failed ConstEval of module 2 outputs at signal %s (input: %s = %s).\n",
					log_signal(undef2), log_signal(mod1_inputs), log_signal(inputs));

		if (sig1 != sig2) {
			log("Found counter-example:\n");
			log("  Module 1:  %s = %s  =>  %s = %s\n", log_signal(mod1_inputs), log_signal(inputs), log_signal(mod1_outputs), log_signal(sig1));
			log("  Module 2:  %s = %s  =>  %s = %s\n", log_signal(mod2_inputs), log_signal(inputs), log_signal(mod2_outputs), log_signal(sig2));
			errors++;
		}

		counter++;
	}

	BruteForceEquivChecker(RTLIL::Module *mod1, RTLIL::Module *mod2) :
			mod1(mod1), mod2(mod2), counter(0), errors(0)
	{
		log("Checking for equivialence (brute-force): %s vs %s\n", mod1->name.c_str(), mod2->name.c_str());
		for (auto &w : mod1->wires)
		{
			RTLIL::Wire *wire1 = w.second;
			if (wire1->port_id == 0)
				continue;

			if (mod2->wires.count(wire1->name) == 0)
				log_cmd_error("Port %s in module 1 has no counterpart in module 2!\n", wire1->name.c_str());

			RTLIL::Wire *wire2 = mod2->wires.at(wire1->name);
			if (wire1->width != wire2->width || wire1->port_input != wire2->port_input || wire1->port_output != wire2->port_output)
				log_cmd_error("Port %s in module 1 does not match its counterpart in module 2!\n", wire1->name.c_str());

			if (wire1->port_input) {
				mod1_inputs.append(wire1);
				mod2_inputs.append(wire2);
			} else {
				mod1_outputs.append(wire1);
				mod2_outputs.append(wire2);
			}
		}

		RTLIL::SigSpec inputs;
		run_checker(inputs);
	}
};

} /* namespace */

struct EvalPass : public Pass {
	EvalPass() : Pass("eval", "evaluate the circuit given an input") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    eval [options] [selection]\n");
		log("\n");
		log("This command evaluates the value of a signal given the value of all required\n");
		log("inputs.\n");
		log("\n");
		log("    -set <signal> <value>\n");
		log("        set the specified signal to the specified value.\n");
		log("\n");
		log("    -show <signal>\n");
		log("        show the value for the specified signal. if no -show option is passed\n");
		log("        then all output ports of the current module are used.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<std::pair<std::string, std::string>> sets;
		std::vector<std::string> shows;

		log_header("Executing EVAL pass (evaluate the circuit given an input).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-set" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx].c_str();
				std::string rhs = args[++argidx].c_str();
				sets.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-show" && argidx+1 < args.size()) {
				shows.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-brute_force_equiv_checker" && argidx+2 < args.size()) {
				/* this should only be used for regression testing of ConstEval -- see tests/xsthammer */
				std::string mod1_name = RTLIL::escape_id(args[++argidx]);
				std::string mod2_name = RTLIL::escape_id(args[++argidx]);
				if (design->modules.count(mod1_name) == 0)
					log_error("Can't find module `%s'!\n", mod1_name.c_str());
				if (design->modules.count(mod2_name) == 0)
					log_error("Can't find module `%s'!\n", mod2_name.c_str());
				BruteForceEquivChecker checker(design->modules.at(mod1_name), design->modules.at(mod2_name));
				if (checker.errors > 0)
					log_cmd_error("Modules are not equivialent!\n");
				log("Verified %s = %s (using brute-force check on %d cases).\n",
						mod1_name.c_str(), mod2_name.c_str(), checker.counter);
				return;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Module *module = NULL;
		for (auto &mod_it : design->modules)
			if (design->selected(mod_it.second)) {
				if (module)
					log_cmd_error("Only one module must be selected for the EVAL pass! (selected: %s and %s)\n",
							RTLIL::id2cstr(module->name), RTLIL::id2cstr(mod_it.first));
				module = mod_it.second;
			}
		if (module == NULL) 
			log_cmd_error("Can't perform EVAL on an empty selection!\n");

		ConstEval ce(module);
		RTLIL::SigSpec show_signal, show_value, undef_signal;

		for (auto &it : sets) {
			RTLIL::SigSpec lhs, rhs;
			if (!RTLIL::SigSpec::parse(lhs, module, it.first))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", it.first.c_str());
			if (!RTLIL::SigSpec::parse(rhs, module, it.second))
				log_cmd_error("Failed to parse rhs set expression `%s'.\n", it.second.c_str());
			if (!rhs.is_fully_const())
				log_cmd_error("Right-hand-side set expression `%s' is not constant.\n", it.second.c_str());
			if (lhs.width != rhs.width)
				log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
						it.first.c_str(), log_signal(lhs), lhs.width, it.second.c_str(), log_signal(rhs), rhs.width);
			ce.set(lhs, rhs.as_const());
		}

		for (auto &it : shows) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse(sig, module, it))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", it.c_str());
			show_signal.append(sig);
		}

		if (shows.size() == 0) {
			for (auto &it : module->wires)
				if (it.second->port_output)
					show_signal.append(it.second);
		}

		show_signal.optimize();
		show_value = show_signal;

		if (!ce.eval(show_value, undef_signal))
			log("Failed to evaluate signal %s: Missing value for %s.\n", log_signal(show_signal), log_signal(undef_signal));
		else
			log("Eval result: %s = %s.\n", log_signal(show_signal), log_signal(show_value));
	}
} EvalPass;
 
