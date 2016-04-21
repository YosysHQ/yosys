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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

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
		if (inputs.size() < mod1_inputs.size()) {
			RTLIL::SigSpec inputs0 = inputs, inputs1 = inputs;
			inputs0.append(RTLIL::Const(0, 1));
			inputs1.append(RTLIL::Const(1, 1));
			run_checker(inputs0);
			run_checker(inputs1);
			return;
		}

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
			for (int i = 0; i < GetSize(sig1); i++)
				if (sig1[i] == RTLIL::State::Sx)
					sig2[i] = RTLIL::State::Sx;
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
		log("Checking for equivalence (brute-force): %s vs %s\n", mod1->name.c_str(), mod2->name.c_str());
		for (auto &w : mod1->wires_)
		{
			RTLIL::Wire *wire1 = w.second;
			if (wire1->port_id == 0)
				continue;

			if (mod2->wires_.count(wire1->name) == 0)
				log_cmd_error("Port %s in module 1 has no counterpart in module 2!\n", wire1->name.c_str());

			RTLIL::Wire *wire2 = mod2->wires_.at(wire1->name);
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

	void sat_check(RTLIL::Module *module, RTLIL::SigSpec recorded_set_vars, RTLIL::Const recorded_set_vals, RTLIL::SigSpec expected_y, bool model_undef)
	{
		log("Verifying SAT model (%s)..\n", model_undef ? "with undef" : "without undef");

		ezSatPtr ez;
		SigMap sigmap(module);
		SatGen satgen(ez.get(), &sigmap);
		satgen.model_undef = model_undef;

		for (auto &c : module->cells_)
			if (!satgen.importCell(c.second))
				log_error("Failed to import cell %s (type %s) to SAT database.\n", RTLIL::id2cstr(c.first), RTLIL::id2cstr(c.second->type));

		ez->assume(satgen.signals_eq(recorded_set_vars, recorded_set_vals));

		std::vector<int> y_vec = satgen.importDefSigSpec(module->wires_.at("\\y"));
		std::vector<bool> y_values;

		if (model_undef) {
			std::vector<int> y_undef_vec = satgen.importUndefSigSpec(module->wires_.at("\\y"));
			y_vec.insert(y_vec.end(), y_undef_vec.begin(), y_undef_vec.end());
		}

		log("  Created SAT problem with %d variables and %d clauses.\n",
				ez->numCnfVariables(), ez->numCnfClauses());

		if (!ez->solve(y_vec, y_values))
			log_error("Failed to find solution to SAT problem.\n");

		for (int i = 0; i < expected_y.size(); i++) {
			RTLIL::State solution_bit = y_values.at(i) ? RTLIL::State::S1 : RTLIL::State::S0;
			RTLIL::State expected_bit = expected_y[i].data;
			if (model_undef) {
				if (y_values.at(expected_y.size()+i))
					solution_bit = RTLIL::State::Sx;
			} else {
				if (expected_bit == RTLIL::State::Sx)
					continue;
			}
			if (solution_bit != expected_bit) {
				std::string sat_bits, rtl_bits;
				for (int k = expected_y.size()-1; k >= 0; k--) {
					if (model_undef && y_values.at(expected_y.size()+k))
						sat_bits += "x";
					else
						sat_bits += y_values.at(k) ? "1" : "0";
					rtl_bits += expected_y[k] == RTLIL::State::Sx ? "x" : expected_y[k] == RTLIL::State::S1 ? "1" : "0";
				}
				log_error("Found error in SAT model: y[%d] = %s, should be %s:\n   SAT: %s\n   RTL: %s\n        %*s^\n",
						int(i), log_signal(solution_bit), log_signal(expected_bit),
						sat_bits.c_str(), rtl_bits.c_str(), expected_y.size()-i-1, "");
			}
		}

		if (model_undef)
		{
			std::vector<int> cmp_vars;
			std::vector<bool> cmp_vals;

			std::vector<bool> y_undef(y_values.begin() + expected_y.size(), y_values.end());

			for (int i = 0; i < expected_y.size(); i++)
				if (y_undef.at(i))
				{
					log("    Toggling undef bit %d to test undef gating.\n", i);
					if (!ez->solve(y_vec, y_values, ez->IFF(y_vec.at(i), y_values.at(i) ? ez->CONST_FALSE : ez->CONST_TRUE)))
						log_error("Failed to find solution with toggled bit!\n");

					cmp_vars.push_back(y_vec.at(expected_y.size() + i));
					cmp_vals.push_back(true);
				}
				else
				{
					cmp_vars.push_back(y_vec.at(i));
					cmp_vals.push_back(y_values.at(i));

					cmp_vars.push_back(y_vec.at(expected_y.size() + i));
					cmp_vals.push_back(false);
				}

			log("    Testing if SAT solution is unique.\n");
			ez->assume(ez->vec_ne(cmp_vars, ez->vec_const(cmp_vals)));
			if (ez->solve(y_vec, y_values))
				log_error("Found two distinct solutions to SAT problem.\n");
		}
		else
		{
			log("    Testing if SAT solution is unique.\n");
			ez->assume(ez->vec_ne(y_vec, ez->vec_const(y_values)));
			if (ez->solve(y_vec, y_values))
				log_error("Found two distinct solutions to SAT problem.\n");
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
					RTLIL::Wire *wire = module->wires_.at(inputs[i]);
					for (int j = input_widths[i]-1; j >= 0; j--) {
						ce.set(RTLIL::SigSpec(wire, j), bits.back());
						recorded_set_vars.append(RTLIL::SigSpec(wire, j));
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

				if (module->wires_.count("\\y") == 0)
					log_error("No output wire (y) found in module %s!\n", RTLIL::id2cstr(module->name));

				RTLIL::SigSpec sig(module->wires_.at("\\y"));
				RTLIL::SigSpec undef;

				while (!ce.eval(sig, undef)) {
					// log_error("Evaluation of y in module %s failed: sig=%s, undef=%s\n", RTLIL::id2cstr(module->name), log_signal(sig), log_signal(undef));
					log_warning("Setting signal %s in module %s to undef.\n", log_signal(undef), RTLIL::id2cstr(module->name));
					ce.set(undef, RTLIL::Const(RTLIL::State::Sx, undef.size()));
				}

				log("++VAL++ %d %s %s #\n", idx, module_name.c_str(), sig.as_const().as_string().c_str());

				if (module_name == "rtl") {
					rtl_sig = sig;
					sat_check(module, recorded_set_vars, recorded_set_vals, sig, false);
					sat_check(module, recorded_set_vars, recorded_set_vals, sig, true);
				} else if (rtl_sig.size() > 0) {
					if (rtl_sig.size() != sig.size())
						log_error("Output (y) has a different width in module %s compared to rtl!\n", RTLIL::id2cstr(module->name));
					for (int i = 0; i < GetSize(sig); i++)
						if (rtl_sig[i] == RTLIL::State::Sx)
							sig[i] = RTLIL::State::Sx;
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
			if (design->modules_.count(esc_name) == 0)
				log_error("Can't find module %s in current design!\n", name.c_str());
			log("Using module %s (%s).\n", esc_name.c_str(), name.c_str());
			modules.push_back(design->modules_.at(esc_name));
			module_names.push_back(name);
		}

		total_input_width = 0;
		for (auto name : split(input_list, ",")) {
			int width = -1;
			RTLIL::IdString esc_name = RTLIL::escape_id(name);
			for (auto mod : modules) {
				if (mod->wires_.count(esc_name) == 0)
					log_error("Can't find input %s in module %s!\n", name.c_str(), RTLIL::id2cstr(mod->name));
				RTLIL::Wire *port = mod->wires_.at(esc_name);
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
			if (sig.size() < total_input_width)
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
		log("    -set-undef\n");
		log("        set all unspecified source signals to undef (x)\n");
		log("\n");
		log("    -table <signal>\n");
		log("        create a truth table using the specified input signals\n");
		log("\n");
		log("    -show <signal>\n");
		log("        show the value for the specified signal. if no -show option is passed\n");
		log("        then all output ports of the current module are used.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<std::pair<std::string, std::string>> sets;
		std::vector<std::string> shows, tables;
		bool set_undef = false;

		log_header(design, "Executing EVAL pass (evaluate the circuit given an input).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-set" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx].c_str();
				std::string rhs = args[++argidx].c_str();
				sets.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-set-undef") {
				set_undef = true;
				continue;
			}
			if (args[argidx] == "-show" && argidx+1 < args.size()) {
				shows.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-table" && argidx+1 < args.size()) {
				tables.push_back(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-brute_force_equiv_checker" || args[argidx] == "-brute_force_equiv_checker_x") && argidx+3 == args.size()) {
				/* this should only be used for regression testing of ConstEval -- see vloghammer */
				std::string mod1_name = RTLIL::escape_id(args[++argidx]);
				std::string mod2_name = RTLIL::escape_id(args[++argidx]);
				if (design->modules_.count(mod1_name) == 0)
					log_error("Can't find module `%s'!\n", mod1_name.c_str());
				if (design->modules_.count(mod2_name) == 0)
					log_error("Can't find module `%s'!\n", mod2_name.c_str());
				BruteForceEquivChecker checker(design->modules_.at(mod1_name), design->modules_.at(mod2_name), args[argidx-2] == "-brute_force_equiv_checker_x");
				if (checker.errors > 0)
					log_cmd_error("Modules are not equivalent!\n");
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
		for (auto &mod_it : design->modules_)
			if (design->selected(mod_it.second)) {
				if (module)
					log_cmd_error("Only one module must be selected for the EVAL pass! (selected: %s and %s)\n",
							RTLIL::id2cstr(module->name), RTLIL::id2cstr(mod_it.first));
				module = mod_it.second;
			}
		if (module == NULL)
			log_cmd_error("Can't perform EVAL on an empty selection!\n");

		ConstEval ce(module);

		for (auto &it : sets) {
			RTLIL::SigSpec lhs, rhs;
			if (!RTLIL::SigSpec::parse_sel(lhs, design, module, it.first))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", it.first.c_str());
			if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, it.second))
				log_cmd_error("Failed to parse rhs set expression `%s'.\n", it.second.c_str());
			if (!rhs.is_fully_const())
				log_cmd_error("Right-hand-side set expression `%s' is not constant.\n", it.second.c_str());
			if (lhs.size() != rhs.size())
				log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
						it.first.c_str(), log_signal(lhs), lhs.size(), it.second.c_str(), log_signal(rhs), rhs.size());
			ce.set(lhs, rhs.as_const());
		}

		if (shows.size() == 0) {
			for (auto &it : module->wires_)
				if (it.second->port_output)
					shows.push_back(it.second->name.str());
		}

		if (tables.empty())
		{
			for (auto &it : shows) {
				RTLIL::SigSpec signal, value, undef;
				if (!RTLIL::SigSpec::parse_sel(signal, design, module, it))
					log_cmd_error("Failed to parse show expression `%s'.\n", it.c_str());
				value = signal;
				if (set_undef) {
					while (!ce.eval(value, undef)) {
						log("Failed to evaluate signal %s: Missing value for %s. -> setting to undef\n", log_signal(signal), log_signal(undef));
						ce.set(undef, RTLIL::Const(RTLIL::State::Sx, undef.size()));
						undef = RTLIL::SigSpec();
					}
					log("Eval result: %s = %s.\n", log_signal(signal), log_signal(value));
				} else {
					if (!ce.eval(value, undef))
						log("Failed to evaluate signal %s: Missing value for %s.\n", log_signal(signal), log_signal(undef));
					else
						log("Eval result: %s = %s.\n", log_signal(signal), log_signal(value));
				}
			}
		}
		else
		{
			RTLIL::SigSpec tabsigs, signal, value, undef;
			std::vector<std::vector<std::string>> tab;
			int tab_sep_colidx = 0;

			for (auto &it : shows) {
				RTLIL::SigSpec sig;
				if (!RTLIL::SigSpec::parse_sel(sig, design, module, it))
					log_cmd_error("Failed to parse show expression `%s'.\n", it.c_str());
				signal.append(sig);
			}

			for (auto &it : tables) {
				RTLIL::SigSpec sig;
				if (!RTLIL::SigSpec::parse_sel(sig, design, module, it))
					log_cmd_error("Failed to parse table expression `%s'.\n", it.c_str());
				tabsigs.append(sig);
			}

			std::vector<std::string> tab_line;
			for (auto &c : tabsigs.chunks())
				tab_line.push_back(log_signal(c));
			tab_sep_colidx = tab_line.size();
			for (auto &c : signal.chunks())
				tab_line.push_back(log_signal(c));
			tab.push_back(tab_line);
			tab_line.clear();

			RTLIL::Const tabvals(0, tabsigs.size());
			do
			{
				ce.push();
				ce.set(tabsigs, tabvals);
				value = signal;

				RTLIL::SigSpec this_undef;
				while (!ce.eval(value, this_undef)) {
					if (!set_undef) {
						log("Failed to evaluate signal %s at %s = %s: Missing value for %s.\n", log_signal(signal),
								log_signal(tabsigs), log_signal(tabvals), log_signal(this_undef));
						return;
					}
					ce.set(this_undef, RTLIL::Const(RTLIL::State::Sx, this_undef.size()));
					undef.append(this_undef);
					this_undef = RTLIL::SigSpec();
				}

				int pos = 0;
				for (auto &c : tabsigs.chunks()) {
					tab_line.push_back(log_signal(RTLIL::SigSpec(tabvals).extract(pos, c.width)));
					pos += c.width;
				}

				pos = 0;
				for (auto &c : signal.chunks()) {
					tab_line.push_back(log_signal(value.extract(pos, c.width)));
					pos += c.width;
				}

				tab.push_back(tab_line);
				tab_line.clear();
				ce.pop();

				tabvals = RTLIL::const_add(tabvals, RTLIL::Const(1), false, false, tabvals.bits.size());
			}
			while (tabvals.as_bool());

			std::vector<int> tab_column_width;
			for (auto &row : tab) {
				if (tab_column_width.size() < row.size())
					tab_column_width.resize(row.size());
				for (size_t i = 0; i < row.size(); i++)
					tab_column_width[i] = max(tab_column_width[i], int(row[i].size()));
			}

			log("\n");
			bool first = true;
			for (auto &row : tab) {
				for (size_t i = 0; i < row.size(); i++) {
					int k = int(i) < tab_sep_colidx ? tab_sep_colidx - i - 1 : i;
					log(" %s%*s", k == tab_sep_colidx ? "| " : "", tab_column_width[k], row[k].c_str());
				}
				log("\n");
				if (first) {
					for (size_t i = 0; i < row.size(); i++) {
						int k = int(i) < tab_sep_colidx ? tab_sep_colidx - i - 1 : i;
						log(" %s", k == tab_sep_colidx ? "| " : "");
						for (int j = 0; j < tab_column_width[k]; j++)
							log("-");
					}
					log("\n");
					first = false;
				}
			}

			log("\n");
			if (undef.size() > 0) {
				undef.sort_and_unify();
				log("Assumed undef (x) value for the following signals: %s\n\n", log_signal(undef));
			}
		}
	}
} EvalPass;

PRIVATE_NAMESPACE_END
