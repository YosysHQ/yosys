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
		log("    -set <signal> <value>\n");
		log("        set the specified signal to the specified value.\n");
		log("\n");
		log("    -show <signal>n");
		log("        show the model for the specified signal. if no -show option\n");
		log("        is passed then all selected signals will be shown.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<std::pair<std::string, std::string>> sets;
		std::vector<std::string> shows;

		log_header("Executing SAT_SOLVE pass (detecting logic loops).\n");

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

		for (auto &s : sets)
		{
			RTLIL::SigSpec lhs, rhs;

			if (!parse_sigstr(lhs, module, s.first))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.first.c_str());
			if (!parse_sigstr(rhs, module, s.second))
				log_cmd_error("Failed to parse rhs set expression `%s'.\n", s.second.c_str());

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
			if (design->selected(module, c.second)) {
				// log("Import cell: %s\n", RTLIL::id2cstr(c.first));
				satgen.importCell(c.second);
				import_cell_counter++;
			}
		log("Imported %d cells.\n", import_cell_counter);

		std::vector<int> modelExpressions;
		std::vector<bool> modelValues;
		std::vector<std::string> modelNames;
		int maxModelName = 0;

		if (shows.size() == 0) {
			for (auto &w : module->wires)
				if (design->selected(module, w.second)) {
					RTLIL::Wire *wire = w.second;
					for (int i = 0; i < wire->width; i++) {
						RTLIL::SigSpec sig = RTLIL::SigSpec(wire, 1, i);
						std::vector<int> vec = satgen.importSigSpec(sig);
						log_assert(vec.size() == 1);
						modelExpressions.push_back(vec[0]);
						modelNames.push_back(log_signal(sig));
						maxModelName = std::max(maxModelName, int(modelNames.back().size()));
					}
				}
		} else {
			for (auto &s : shows) {
				RTLIL::SigSpec sig;
				if (!parse_sigstr(sig, module, s))
					log_cmd_error("Failed to parse show expression `%s'.\n", s.c_str());
				sig.expand();
				log("Import show expression: %s\n", log_signal(sig));
				for (auto &c : sig.chunks) {
					RTLIL::SigSpec chunksig = c;
					std::vector<int> vec = satgen.importSigSpec(chunksig);
					log_assert(vec.size() == 1);
					modelExpressions.push_back(vec[0]);
					modelNames.push_back(log_signal(chunksig));
					maxModelName = std::max(maxModelName, int(modelNames.back().size()));
				}
			}
		}

		log("Solving problem with %d variables and %d clauses..\n", ez.numCnfVariables(), int(ez.cnf().size()));
		if (ez.solve(modelExpressions, modelValues))
		{
			log("SAT solving finished - model found:\n");
			for (size_t i = 0; i < modelNames.size(); i++)
				log("  %-*s %s\n", maxModelName, modelNames.at(i).c_str(), modelValues.at(i) ? "1" : "0");
		}
		else
			log("SAT solving finished - no model found.\n");
	}
} SatSolvePass;
 
