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

// [[CITE]] VlogHammer Verilog Regression Test Suite
// http://www.clifford.at/yosys/vloghammer.html

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/consteval.h"
#include "kernel/sigtools.h"
#include "kernel/satgen.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <algorithm>

namespace {

/* this should only be used for regression testing of ConstEval -- see vloghammer */
struct BruteForceEquivChecker
{
	RTLIL::Module *mod1, *mod2;
	RTLIL::SigSpec mod1_inputs, mod1_outputs;
	RTLIL::SigSpec mod2_inputs, mod2_outputs;
	int counter, errors;
	bool ignore_x_mod1;

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

		if (ignore_x_mod1) {
			sig1.expand(), sig2.expand();
			for (size_t i = 0; i < sig1.chunks.size(); i++)
				if (sig1.chunks.at(i) == RTLIL::SigChunk(RTLIL::State::Sx))
					sig2.chunks.at(i) = RTLIL::SigChunk(RTLIL::State::Sx);
			sig1.optimize(), sig2.optimize();
		}

		if (sig1 != sig2) {
			log("Found counter-example (ignore_x_mod1 = %s):\n", ignore_x_mod1 ? "active" : "inactive");
			log("  Module 1:  %s = %s  =>  %s = %s\n", log_signal(mod1_inputs), log_signal(inputs), log_signal(mod1_outputs), log_signal(sig1));
			log("  Module 2:  %s = %s  =>  %s = %s\n", log_signal(mod2_inputs), log_signal(inputs), log_signal(mod2_outputs), log_signal(sig2));
			errors++;
		}

		counter++;
	}

	BruteForceEquivChecker(RTLIL::Module *mod1, RTLIL::Module *mod2, bool ignore_x_mod1) :
			mod1(mod1), mod2(mod2), counter(0), errors(0), ignore_x_mod1(ignore_x_mod1)
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

/* this should only be used for regression testing of ConstEval -- see vloghammer */
struct VlogHammerReporter
{
	RTLIL::Design *design;
	std::vector<RTLIL::Module*> modules;
	std::vector<std::string> module_names;
	std::vector<RTLIL::IdString> inputs;
	std::vector<int> input_widths;
	std::vector<RTLIL::Const> patterns;
	int total_input_width;

	std::vector<std::string> split(std::string text, const char *delim)
	{
		std::vector<std::string> list;
		char *p = strdup(text.c_str());
		char *t = strtok(p, delim);
		while (t != NULL) {
			list.push_back(t);
			t = strtok(NULL, delim);
		}
		free(p);
		return list;
	}

	void sat_check(RTLIL::Module *module, RTLIL::SigSpec recorded_set_vars, RTLIL::Const recorded_set_vals, RTLIL::SigSpec expected_y)
	{
		log("Verifying SAT model..\n");

		ezDefaultSAT ez;
		SigMap sigmap(module);
		SatGen satgen(&ez, design, &sigmap);

		for (auto &c : module->cells)
			if (!satgen.importCell(c.second))
				log_error("Failed to import cell %s (type %s) to SAT database.\n", RTLIL::id2cstr(c.first), RTLIL::id2cstr(c.second->type));

		std::vector<int> rec_var_vec = satgen.importSigSpec(recorded_set_vars);
		std::vector<int> rec_val_vec = satgen.importSigSpec(recorded_set_vals);
		ez.assume(ez.vec_eq(rec_var_vec, rec_val_vec));

		std::vector<int> y_vec = satgen.importSigSpec(module->wires.at("\\y"));
		std::vector<bool> y_values;

		log("  Created SAT problem with %d variables and %d clauses.\n",
				ez.numCnfVariables(), ez.numCnfClauses());

		if (!ez.solve(y_vec, y_values))
			log_error("Failed to find solution to SAT problem.\n");

		expected_y.expand();
		assert(expected_y.chunks.size() == y_vec.size());
		for (size_t i = 0; i < y_vec.size(); i++) {
			RTLIL::State bit = expected_y.chunks.at(i).data.bits.at(0);
			if ((bit == RTLIL::State::S0 || bit == RTLIL::State::S1) && ((bit == RTLIL::State::S1) != y_values.at(i)))
				log_error("Found error in SAT model: y[%d] = %d, should be %d.\n",
						int(i), int(y_values.at(i)), int(bit == RTLIL::State::S1));
		}

		log("  SAT model verified.\n");
	}

	void run()
	{
		for (int idx = 0; idx < int(patterns.size()); idx++)
		{
			log("Creating report for pattern %d: %s\n", idx, log_signal(patterns[idx]));
			std::string input_pattern_list;
			RTLIL::SigSpec rtl_sig;

			for (int mod = 0; mod < int(modules.size()); mod++)
			{
				RTLIL::SigSpec recorded_set_vars;
				RTLIL::Const recorded_set_vals;
				RTLIL::Module *module = modules[mod];
				std::string module_name = module_names[mod].c_str();
				ConstEval ce(module);

				std::vector<RTLIL::State> bits(patterns[idx].bits.begin(), patterns[idx].bits.begin() + total_input_width);
				for (int i = 0; i < int(inputs.size()); i++) {
					RTLIL::Wire *wire = module->wires.at(inputs[i]);
					for (int j = input_widths[i]-1; j >= 0; j--) {
						ce.set(RTLIL::SigSpec(wire, 1, j), bits.back());
						recorded_set_vars.append(RTLIL::SigSpec(wire, 1, j));
						recorded_set_vals.bits.push_back(bits.back());
						bits.pop_back();
					}
					if (module == modules.front()) {
						RTLIL::SigSpec sig(wire);
						if (!ce.eval(sig))
							log_error("Can't read back value for port %s!\n", RTLIL::id2cstr(inputs[i]));
						input_pattern_list += stringf(" %s", sig.as_const().as_string().c_str());
						log("++PAT++ %d %s %s #\n", idx, RTLIL::id2cstr(inputs[i]), sig.as_const().as_string().c_str());
					}
				}

				if (module->wires.count("\\y") == 0)
					log_error("No output wire (y) found in module %s!\n", RTLIL::id2cstr(module->name));

				RTLIL::SigSpec sig(module->wires.at("\\y"));
				RTLIL::SigSpec undef;

				while (!ce.eval(sig, undef)) {
					// log_error("Evaluation of y in module %s failed: sig=%s, undef=%s\n", RTLIL::id2cstr(module->name), log_signal(sig), log_signal(undef));
					log("Warning: Setting signal %s in module %s to undef.\n", log_signal(undef), RTLIL::id2cstr(module->name));
					ce.set(undef, RTLIL::Const(RTLIL::State::Sx, undef.width));
				}

				log("++VAL++ %d %s %s #\n", idx, module_name.c_str(), sig.as_const().as_string().c_str());

				if (module_name == "rtl") {
					rtl_sig = sig;
					rtl_sig.expand();
					sat_check(module, recorded_set_vars, recorded_set_vals, sig);
				} else if (rtl_sig.width > 0) {
					sig.expand();
					if (rtl_sig.width != sig.width)
						log_error("Output (y) has a different width in module %s compared to rtl!\n", RTLIL::id2cstr(module->name));
					for (int i = 0; i < sig.width; i++)
						if (rtl_sig.chunks.at(i).data.bits.at(0) == RTLIL::State::Sx)
							sig.chunks.at(i).data.bits.at(0) = RTLIL::State::Sx;
				}

				log("++RPT++ %d%s %s %s\n", idx, input_pattern_list.c_str(), sig.as_const().as_string().c_str(), module_name.c_str());
			}

			log("++RPT++ ----\n");
		}
		log("++OK++\n");
	}

	VlogHammerReporter(RTLIL::Design *design, std::string module_prefix, std::string module_list, std::string input_list, std::string pattern_list) : design(design)
	{
		for (auto name : split(module_list, ",")) {
			RTLIL::IdString esc_name = RTLIL::escape_id(module_prefix + name);
			if (design->modules.count(esc_name) == 0)
				log_error("Can't find module %s in current design!\n", name.c_str());
			log("Using module %s (%s).\n", esc_name.c_str(), name.c_str());
			modules.push_back(design->modules.at(esc_name));
			module_names.push_back(name);
		}

		total_input_width = 0;
		for (auto name : split(input_list, ",")) {
			int width = -1;
			RTLIL::IdString esc_name = RTLIL::escape_id(name);
			for (auto mod : modules) {
				if (mod->wires.count(esc_name) == 0)
					log_error("Can't find input %s in module %s!\n", name.c_str(), RTLIL::id2cstr(mod->name));
				RTLIL::Wire *port = mod->wires.at(esc_name);
				if (!port->port_input || port->port_output)
					log_error("Wire %s in module %s is not an input!\n", name.c_str(), RTLIL::id2cstr(mod->name));
				if (width >= 0 && width != port->width)
					log_error("Port %s has different sizes in the different modules!\n", name.c_str());
				width = port->width;
			}
			log("Using input port %s with width %d.\n", esc_name.c_str(), width);
			inputs.push_back(esc_name);
			input_widths.push_back(width);
			total_input_width += width;
		}

		for (auto pattern : split(pattern_list, ",")) {
			RTLIL::SigSpec sig;
			bool invert_pattern = false;
			if (pattern.size() > 0 && pattern[0] == '~') {
				invert_pattern = true;
				pattern = pattern.substr(1);
			}
			if (!RTLIL::SigSpec::parse(sig, NULL, pattern) || !sig.is_fully_const())
				log_error("Failed to parse pattern %s!\n", pattern.c_str());
			if (sig.width < total_input_width)
				log_error("Pattern %s is to short!\n", pattern.c_str());
			patterns.push_back(sig.as_const());
			if (invert_pattern) {
				for (auto &bit : patterns.back().bits)
					if (bit == RTLIL::State::S0)
						bit = RTLIL::State::S1;
					else if (bit == RTLIL::State::S1)
						bit = RTLIL::State::S0;
			}
			log("Using pattern %s.\n", patterns.back().as_string().c_str());
		}
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
			if ((args[argidx] == "-brute_force_equiv_checker" || args[argidx] == "-brute_force_equiv_checker_x") && argidx+3 == args.size()) {
				/* this should only be used for regression testing of ConstEval -- see vloghammer */
				std::string mod1_name = RTLIL::escape_id(args[++argidx]);
				std::string mod2_name = RTLIL::escape_id(args[++argidx]);
				if (design->modules.count(mod1_name) == 0)
					log_error("Can't find module `%s'!\n", mod1_name.c_str());
				if (design->modules.count(mod2_name) == 0)
					log_error("Can't find module `%s'!\n", mod2_name.c_str());
				BruteForceEquivChecker checker(design->modules.at(mod1_name), design->modules.at(mod2_name), args[argidx-2] == "-brute_force_equiv_checker_x");
				if (checker.errors > 0)
					log_cmd_error("Modules are not equivialent!\n");
				log("Verified %s = %s (using brute-force check on %d cases).\n",
						mod1_name.c_str(), mod2_name.c_str(), checker.counter);
				return;
			}
			if (args[argidx] == "-vloghammer_report" && argidx+5 == args.size()) {
				/* this should only be used for regression testing of ConstEval -- see vloghammer */
				std::string module_prefix = args[++argidx];
				std::string module_list = args[++argidx];
				std::string input_list = args[++argidx];
				std::string pattern_list = args[++argidx];
				VlogHammerReporter reporter(design, module_prefix, module_list, input_list, pattern_list);
				reporter.run();
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
 
