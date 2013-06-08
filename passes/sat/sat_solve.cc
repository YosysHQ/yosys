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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/satgen.h"
#include "frontends/verilog/verilog_frontend.h"
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>

static void split(std::vector<std::string> &tokens, const std::string &text, char sep)
{
	size_t start = 0, end = 0;
	while ((end = text.find(sep, start)) != std::string::npos) {
		tokens.push_back(text.substr(start, end - start));
		start = end + 1;
	}
	tokens.push_back(text.substr(start));
}

bool parse_sigstr(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str)
{
	std::vector<std::string> tokens;
	split(tokens, str, ',');

	sig = RTLIL::SigSpec();
	for (auto &tok : tokens)
	{
		std::string netname = tok;
		std::string indices;

		if (netname.size() == 0)
			continue;

		if ('0' <= netname[0] && netname[0] <= '9') {
			AST::AstNode *ast = VERILOG_FRONTEND::const2ast(netname);
			if (ast == NULL)
				return false;
			sig.append(RTLIL::Const(ast->bits));
			delete ast;
			continue;
		}

		if (netname[0] != '$' && netname[0] != '\\')
			netname = "\\" + netname;

		if (module->wires.count(netname) == 0) {
			size_t indices_pos = netname.size()-1;
			if (indices_pos > 2 && netname[indices_pos] == ']')
			{
				indices_pos--;
				while (indices_pos > 0 && ('0' <= netname[indices_pos] && netname[indices_pos] <= '9')) indices_pos--;
				if (indices_pos > 0 && netname[indices_pos] == ':') {
					indices_pos--;
					while (indices_pos > 0 && ('0' <= netname[indices_pos] && netname[indices_pos] <= '9')) indices_pos--;
				}
				if (indices_pos > 0 && netname[indices_pos] == '[') {
					indices = netname.substr(indices_pos);
					netname = netname.substr(0, indices_pos);
				}
			}
		}

		if (module->wires.count(netname) == 0)
			return false;

		RTLIL::Wire *wire = module->wires.at(netname);
		if (!indices.empty()) {
			std::vector<std::string> index_tokens;
			split(index_tokens, indices.substr(1, indices.size()-2), ':');
			if (index_tokens.size() == 1)
				sig.append(RTLIL::SigSpec(wire, 1, atoi(index_tokens.at(0).c_str())));
			else {
				int a = atoi(index_tokens.at(0).c_str());
				int b = atoi(index_tokens.at(1).c_str());
				if (a > b) {
					int tmp = a;
					a = b, b = tmp;
				}
				sig.append(RTLIL::SigSpec(wire, b-a+1, a));
			}
		} else
			sig.append(wire);
	}

	return true;
}

struct SatSolvePass : public Pass {
	SatSolvePass() : Pass("sat_solve", "solve a SAT problem in the circuit") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sat_solve [options] [selection]\n");
		log("\n");
		log("This command solves a SAT problem defined over the currently selected circuit\n");
		log("and additional constraints passed as parameters.\n");
		log("\n");
		log("    -all\n");
		log("        show all solutions to the problem (this can grow exponentially, use\n");
		log("        -max <N> instead to get <N> solutions)\n");
		log("\n");
		log("    -max <N>\n");
		log("        like -all, but limit number of solutions to <N>\n");
		log("\n");
		log("    -set <signal> <value>\n");
		log("        set the specified signal to the specified value.\n");
		log("\n");
		log("    -show <signal>\n");
		log("        show the model for the specified signal. if no -show option is\n");
		log("        passed then a set of signals to be shown is automatically selected.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<std::pair<std::string, std::string>> sets;
		std::vector<std::string> shows;
		int loopcount = 0;

		log_header("Executing SAT_SOLVE pass (solving SAT problems in the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-all") {
				loopcount = -1;
				continue;
			}
			if (args[argidx] == "-max" && argidx+1 < args.size()) {
				loopcount = atoi(args[++argidx].c_str());
				continue;
			}
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
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Module *module = NULL;
		for (auto &mod_it : design->modules)
			if (design->selected(mod_it.second)) {
				if (module)
					log_cmd_error("Only one module must be selected for the SAT_SOLVE pass! (selected: %s and %s)\n",
							RTLIL::id2cstr(module->name), RTLIL::id2cstr(mod_it.first));
				module = mod_it.second;
			}
		if (module == NULL)
			log_cmd_error("Can't perform SAT_SOLVE on an empty selection!\n");

		ezDefaultSAT ez;
		SigMap sigmap(module);
		SatGen satgen(&ez, design, &sigmap);

		// when no -show is passed, the set signals and other data is collected in
		// this variables, which is then used to generate the list of signals
		// on the  input cone on the set signals and used as show signals
		SigPool show_signal_pool;
		SigSet<RTLIL::Cell*> show_drivers;
		std::map<RTLIL::Cell*,RTLIL::SigSpec> show_driven;
		CellTypes ct(design);

		for (auto &s : sets)
		{
			RTLIL::SigSpec lhs, rhs;

			if (!parse_sigstr(lhs, module, s.first))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.first.c_str());
			if (!parse_sigstr(rhs, module, s.second))
				log_cmd_error("Failed to parse rhs set expression `%s'.\n", s.second.c_str());
			show_signal_pool.add(sigmap(lhs));
			show_signal_pool.add(sigmap(rhs));

			if (lhs.width != rhs.width)
				log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
					s.first.c_str(), log_signal(lhs), lhs.width, s.second.c_str(), log_signal(rhs), rhs.width);

			log("Import constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));

			std::vector<int> lhs_vec = satgen.importSigSpec(lhs);
			std::vector<int> rhs_vec = satgen.importSigSpec(rhs);
			ez.assume(ez.vec_eq(lhs_vec, rhs_vec));
		}

		int import_cell_counter = 0;
		for (auto &c : module->cells)
			if (design->selected(module, c.second) && ct.cell_known(c.second->type)) {
				// log("Import cell: %s\n", RTLIL::id2cstr(c.first));
				if (satgen.importCell(c.second)) {
					for (auto &p : c.second->connections)
						if (ct.cell_output(c.second->type, p.first))
							show_drivers.insert(sigmap(p.second), c.second);
						else
							show_driven[c.second].append(sigmap(p.second));
					import_cell_counter++;
				} else
					log("Warning: failed to import cell %s (type %s) to SAT database.\n", RTLIL::id2cstr(c.first), RTLIL::id2cstr(c.second->type));
			}
		log("Imported %d cells to SAT database.\n", import_cell_counter);

		RTLIL::SigSpec modelSig;
		std::vector<int> modelExpressions;
		std::vector<bool> modelValues;

		if (shows.size() == 0) {
			SigPool handled_signals, final_signals;
			for (auto &s : show_driven)
				s.second.sort_and_unify();
			while (show_signal_pool.size() > 0) {
				RTLIL::SigSpec sig = show_signal_pool.export_one();
				show_signal_pool.del(sig);
				handled_signals.add(sig);
				std::set<RTLIL::Cell*> drivers = show_drivers.find(sig);
				if (drivers.size() == 0) {
					final_signals.add(sig);
				} else {
					for (auto &d : drivers)
					for (auto &p : d->connections)
						show_signal_pool.add(handled_signals.remove(p.second));
				}
			}
			modelSig = final_signals.export_all();
		} else {
			for (auto &s : shows) {
				RTLIL::SigSpec sig;
				if (!parse_sigstr(sig, module, s))
					log_cmd_error("Failed to parse show expression `%s'.\n", s.c_str());
				log("Import show expression: %s\n", log_signal(sig));
				modelSig.append(sig);
			}
		}

		modelSig.expand();
		for (auto &c : modelSig.chunks)
			if (c.wire != NULL) {
				RTLIL::SigSpec chunksig = c;
				std::vector<int> vec = satgen.importSigSpec(chunksig);
				log_assert(vec.size() == 1);
				modelExpressions.push_back(vec[0]);
			}

rerun_solver:
		log("Solving problem with %d variables and %d clauses..\n", ez.numCnfVariables(), ez.numCnfClauses());
		if (ez.solve(modelExpressions, modelValues))
		{
			log("SAT solving finished - model found:\n\n");

			int modelIdx = 0;
			int maxModelName = 10;
			int maxModelWidth = 10;

			modelSig.optimize();
			for (auto &c : modelSig.chunks)
				if (c.wire != NULL) {
					maxModelName = std::max(maxModelName, int(c.wire->name.size()));
					maxModelWidth = std::max(maxModelWidth, c.width);
				}

			const char *hline = "--------------------------------------------------------";
			log("  %-*s %10s %10s %*s\n", maxModelName+10, "Signal Name", "Dec", "Hex", maxModelWidth+5, "Bin");
			log("  %*.*s %10.10s %10.10s %*.*s\n", maxModelName+10, maxModelName+10,
					hline, hline, hline, maxModelWidth+5, maxModelWidth+5, hline);

			for (auto &c : modelSig.chunks) {
				if (c.wire == NULL)
					continue;
				RTLIL::Const value;
				for (int i = 0; i < c.width; i++)
					value.bits.push_back(modelValues.at(modelIdx+i) ? RTLIL::State::S1 : RTLIL::State::S0);
				if (c.width <= 32)
					log("  %-*s %10d %10x %*s\n", maxModelName+10, log_signal(c), value.as_int(), value.as_int(), maxModelWidth+5, value.as_string().c_str());
				else
					log("  %-*s %10s %10s %*s\n", maxModelName+10, log_signal(c), "--", "--", maxModelWidth+5, value.as_string().c_str());
				modelIdx += c.width;
			}

			if (loopcount != 0) {
				log("\n");
				std::vector<int> clause;
				for (size_t i = 0; i < modelExpressions.size(); i++)
					clause.push_back(modelValues.at(i) ? ez.NOT(modelExpressions.at(i)) : modelExpressions.at(i));
				ez.assume(ez.expression(ezSAT::OpOr, clause));
				loopcount--;
				goto rerun_solver;
			}
		}
		else
			log("SAT solving finished - no model found.\n");
	}
} SatSolvePass;
 
