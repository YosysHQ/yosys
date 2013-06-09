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

static bool parse_sigstr(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str)
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

struct SatHelper
{
	RTLIL::Design *design;
	RTLIL::Module *module;

	ezDefaultSAT ez;
	SigMap sigmap;
	CellTypes ct;
	SatGen satgen;

	// additional constraints
	std::vector<std::pair<std::string, std::string>> sets, prove;
	std::map<int, std::vector<std::pair<std::string, std::string>>> sets_at;
	std::map<int, std::vector<std::string>> unsets_at;

	// model variables
	std::vector<std::string> shows;
	SigPool show_signal_pool;
	SigSet<RTLIL::Cell*> show_drivers;
	std::map<RTLIL::Cell*,RTLIL::SigSpec> show_driven;
	int max_timestep;

	SatHelper(RTLIL::Design *design, RTLIL::Module *module) :
		design(design), module(module), sigmap(module), ct(design), satgen(&ez, design, &sigmap)
	{
		max_timestep = -1;
	}

	void setup(int timestep = -1)
	{
		if (timestep > 0)
			log ("\nSetting up time step %d:\n", timestep);
		else
			log ("\nSetting up SAT problem:\n");

		if (timestep > max_timestep)
			max_timestep = timestep;

		RTLIL::SigSpec big_lhs, big_rhs;

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

			log("Import set-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
			big_lhs.remove2(lhs, &big_rhs);
			big_lhs.append(lhs);
			big_rhs.append(rhs);
		}

		for (auto &s : sets_at[timestep])
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

			log("Import set-constraint for timestep: %s = %s\n", log_signal(lhs), log_signal(rhs));
			big_lhs.remove2(lhs, &big_rhs);
			big_lhs.append(lhs);
			big_rhs.append(rhs);
		}

		for (auto &s : unsets_at[timestep])
		{
			RTLIL::SigSpec lhs;

			if (!parse_sigstr(lhs, module, s))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.c_str());
			show_signal_pool.add(sigmap(lhs));

			log("Import unset-constraint for timestep: %s\n", log_signal(lhs));
			big_lhs.remove2(lhs, &big_rhs);
		}

		log("Final constraint equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));

		std::vector<int> lhs_vec = satgen.importSigSpec(big_lhs, timestep);
		std::vector<int> rhs_vec = satgen.importSigSpec(big_rhs, timestep);
		ez.assume(ez.vec_eq(lhs_vec, rhs_vec));

		int import_cell_counter = 0;
		for (auto &c : module->cells)
			if (design->selected(module, c.second) && ct.cell_known(c.second->type)) {
				// log("Import cell: %s\n", RTLIL::id2cstr(c.first));
				if (satgen.importCell(c.second, timestep)) {
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
	}

	void setup_proof(int timestep = -1)
	{
		if (prove.size() == 0)
			return;

		RTLIL::SigSpec big_lhs, big_rhs;

		for (auto &s : prove)
		{
			RTLIL::SigSpec lhs, rhs;

			if (!parse_sigstr(lhs, module, s.first))
				log_cmd_error("Failed to parse lhs proof expression `%s'.\n", s.first.c_str());
			if (!parse_sigstr(rhs, module, s.second))
				log_cmd_error("Failed to parse rhs proof expression `%s'.\n", s.second.c_str());
			show_signal_pool.add(sigmap(lhs));
			show_signal_pool.add(sigmap(rhs));

			if (lhs.width != rhs.width)
				log_cmd_error("Proof expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
					s.first.c_str(), log_signal(lhs), lhs.width, s.second.c_str(), log_signal(rhs), rhs.width);

			log("Import proof-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
			big_lhs.remove2(lhs, &big_rhs);
			big_lhs.append(lhs);
			big_rhs.append(rhs);
		}

		log("Final proof equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));

		std::vector<int> lhs_vec = satgen.importSigSpec(big_lhs, timestep);
		std::vector<int> rhs_vec = satgen.importSigSpec(big_rhs, timestep);
		ez.assume(ez.vec_ne(lhs_vec, rhs_vec));
	}

	bool solve()
	{
		return ez.solve(modelExpressions, modelValues);
	}

	struct ModelBlockInfo {
		int timestep, offset, width;
		std::string description;
		bool operator < (const ModelBlockInfo &other) const {
			if (timestep != other.timestep)
				return timestep < other.timestep;
			if (description != other.description)
				return description < other.description;
			if (offset != other.offset)
				return offset < other.offset;
			if (width != other.width)
				return width < other.width;
			return false;
		}
	};

	std::vector<int> modelExpressions;
	std::vector<bool> modelValues;
	std::set<ModelBlockInfo> modelInfo;

	void generate_model()
	{
		RTLIL::SigSpec modelSig;

		// Add "normal" show signals for every timestep

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

		modelSig.sort_and_unify();
		// log("Model signals: %s\n", log_signal(modelSig));

		for (auto &c : modelSig.chunks)
			if (c.wire != NULL) {
				ModelBlockInfo info;
				RTLIL::SigSpec chunksig = c;
				info.width = chunksig.width;
				info.description = log_signal(chunksig);

				for (int timestep = -1; timestep <= max_timestep; timestep++) {
					if ((timestep == -1 && max_timestep > 0) || timestep == 0)
						continue;
					std::vector<int> vec = satgen.importSigSpec(chunksig, timestep);
					info.timestep = timestep;
					info.offset = modelExpressions.size();
					modelExpressions.insert(modelExpressions.end(), vec.begin(), vec.end());
					modelInfo.insert(info);
				}
			}

		// Add zero step signals as collected by satgen

		modelSig = satgen.initial_signals.export_all();
		for (auto &c : modelSig.chunks)
			if (c.wire != NULL) {
				ModelBlockInfo info;
				RTLIL::SigSpec chunksig = c;
				info.timestep = 0;
				info.offset = modelExpressions.size();
				info.width = chunksig.width;
				info.description = log_signal(chunksig);
				std::vector<int> vec = satgen.importSigSpec(chunksig, 1);
				modelExpressions.insert(modelExpressions.end(), vec.begin(), vec.end());
				modelInfo.insert(info);
			}
	}

	void print_model()
	{
		int maxModelName = 10;
		int maxModelWidth = 10;

		for (auto &info : modelInfo) {
			maxModelName = std::max(maxModelName, int(info.description.size()));
			maxModelWidth = std::max(maxModelWidth, info.width);
		}

		log("\n");

		int last_timestep = -2;
		for (auto &info : modelInfo)
		{
			RTLIL::Const value;
			for (int i = 0; i < info.width; i++) {
				value.bits.push_back(modelValues.at(info.offset+i) ? RTLIL::State::S1 : RTLIL::State::S0);
				if (modelValues.size() == 2*modelExpressions.size() && modelValues.at(modelExpressions.size()+info.offset+i))
					value.bits.back() = RTLIL::State::Sx;
			}

			if (info.timestep != last_timestep) {
				const char *hline = "---------------------------------------------------------------------------------------------------"
						    "---------------------------------------------------------------------------------------------------"
						    "---------------------------------------------------------------------------------------------------";
				if (last_timestep == -2) {
					log(max_timestep > 0 ? "  Time " : "  ");
					log("%-*s %10s %10s %*s\n", maxModelName+10, "Signal Name", "Dec", "Hex", maxModelWidth+5, "Bin");
				}
				log(max_timestep > 0 ? "  ---- " : "  ");
				log("%*.*s %10.10s %10.10s %*.*s\n", maxModelName+10, maxModelName+10,
						hline, hline, hline, maxModelWidth+5, maxModelWidth+5, hline);
				last_timestep = info.timestep;
			}

			if (max_timestep > 0) {
				if (info.timestep > 0)
					log("  %4d ", info.timestep);
				else
					log("  init ");
			} else
				log("  ");

			if (info.width <= 32)
				log("%-*s %10d %10x %*s\n", maxModelName+10, info.description.c_str(), value.as_int(), value.as_int(), maxModelWidth+5, value.as_string().c_str());
			else
				log("%-*s %10s %10s %*s\n", maxModelName+10, info.description.c_str(), "--", "--", maxModelWidth+5, value.as_string().c_str());
		}

		if (last_timestep == -2)
			log("  no model variables selected for display.\n");
	}

	void invalidate_model()
	{
		std::vector<int> clause;
		for (size_t i = 0; i < modelExpressions.size(); i++)
			clause.push_back(modelValues.at(i) ? ez.NOT(modelExpressions.at(i)) : modelExpressions.at(i));
		ez.assume(ez.expression(ezSAT::OpOr, clause));
	}
};

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
		log("The following options can be used to set up a sequential problem:\n");
		log("\n");
		log("    -seq <N>\n");
		log("        set up a sequential problem with <N> time steps. The steps will\n");
		log("        be numbered from 1 to N.\n");
		log("\n");
		log("    -set-at <N> <signal> <value>\n");
		log("    -unset-at <N> <signal>\n");
		log("        set or unset the specified signal to the specified value in the\n");
		log("        given timestep. this has priority over a -set for the same signal.\n");
		log("\n");
		log("The following additional options can be used to set up a proof. If also -seq\n");
		log("is passed, a temporal induction proof is performed.\n");
		log("\n");
		log("    -prove <signal> <value>\n");
		log("        Attempt to proof that <signal> is always <value>. In a temporal\n");
		log("        induction proof it is proven that the condition holds forever after\n");
		log("        the number of time steps passed using -seq.\n");
		log("\n");
		log("    -verify\n");
		log("        Return an error and stop the synthesis script if the proof fails.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<std::pair<std::string, std::string>> sets, prove;
		std::map<int, std::vector<std::pair<std::string, std::string>>> sets_at;
		std::map<int, std::vector<std::string>> unsets_at;
		std::vector<std::string> shows;
		int loopcount = 0, seq_len = 0;
		bool verify = false;

		log_header("Executing SAT_SOLVE pass (solving SAT problems in the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-all") {
				loopcount = -1;
				continue;
			}
			if (args[argidx] == "-verify") {
				verify = true;
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
			if (args[argidx] == "-prove" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx].c_str();
				std::string rhs = args[++argidx].c_str();
				prove.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-seq" && argidx+1 < args.size()) {
				seq_len = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-set-at" && argidx+3 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				std::string lhs = args[++argidx].c_str();
				std::string rhs = args[++argidx].c_str();
				sets_at[timestep].push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-unset-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				std::string lhs = args[++argidx].c_str();
				unsets_at[timestep].push_back(lhs);
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

		if (prove.size() == 0 && verify)
			log_cmd_error("Got -verify but nothing to prove!\n");

		if (prove.size() > 0 && seq_len > 0)
		{
			log_cmd_error("Temporal induction proofs are not implemented yet!\n");
		}
		else
		{
			SatHelper sathelper(design, module);
			sathelper.sets = sets;
			sathelper.prove = prove;
			sathelper.sets_at = sets_at;
			sathelper.unsets_at = unsets_at;
			sathelper.shows = shows;

			if (seq_len == 0) {
				sathelper.setup();
				sathelper.setup_proof();
			} else {
				for (int timestep = 1; timestep <= seq_len; timestep++)
					sathelper.setup(timestep);
			}
			sathelper.generate_model();

#if 0
			// print CNF for debugging
			sathelper.ez.printDIMACS(stdout, true);
#endif

rerun_solver:
			log("\nSolving problem with %d variables and %d clauses..\n",
					sathelper.ez.numCnfVariables(), sathelper.ez.numCnfClauses());

			if (sathelper.solve())
			{
				if (prove.size() == 0) {
					log("SAT solving finished - model found:\n");
				} else {
					log("SAT proof finished - model found: FAIL!\n");
					log("\n");
					log("   ______                   ___       ___       _ _            _ _ \n");
					log("  (_____ \\                 / __)     / __)     (_) |          | | |\n");
					log("   _____) )___ ___   ___ _| |__    _| |__ _____ _| | _____  __| | |\n");
					log("  |  ____/ ___) _ \\ / _ (_   __)  (_   __|____ | | || ___ |/ _  |_|\n");
					log("  | |   | |  | |_| | |_| || |       | |  / ___ | | || ____( (_| |_ \n");
					log("  |_|   |_|   \\___/ \\___/ |_|       |_|  \\_____|_|\\_)_____)\\____|_|\n");
					log("\n");
				}

				sathelper.print_model();

				if (verify) {
					log("\n");
					log_error("Called with -verify and proof did fail!\n");
				}

				if (loopcount != 0) {
					loopcount--;
					sathelper.invalidate_model();
					goto rerun_solver;
				}
			}
			else
			{
				if (prove.size() == 0)
					log("SAT solving finished - no model found.\n");
				else
					log("SAT proof finished - no model found: SUCCESS!\n");
			}
		}
	}
} SatSolvePass;
 
