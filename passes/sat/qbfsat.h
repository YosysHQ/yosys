/* -*- c++ -*-
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Alberto Gonzalez <boqwxp@airmail.cc>
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

#ifndef QBFSAT_H
#define QBFSAT_H

#include "kernel/yosys.h"
#include <numeric>

YOSYS_NAMESPACE_BEGIN

struct QbfSolveOptions {
	bool specialize = false, specialize_from_file = false, write_solution = false, nocleanup = false;
	bool dump_final_smt2 = false, assume_outputs = false, assume_neg = false, nooptimize = false;
	bool nobisection = false, sat = false, unsat = false, show_smtbmc = false;
	enum Solver{Z3, Yices, CVC4} solver = Yices;
	enum OptimizationLevel{O0, O1, O2} oflag = O0;
	dict<std::string, std::string> solver_options;
	int timeout = 0;
	std::string specialize_soln_file = "";
	std::string write_soln_soln_file = "";
	std::string dump_final_smt2_file = "";
	size_t argidx = 0;

	std::string get_solver_name() const {
		if (solver == Solver::Z3)
			return "z3";
		else if (solver == Solver::Yices)
			return "yices";
		else if (solver == Solver::CVC4)
			return "cvc4";

		log_cmd_error("unknown solver specified.\n");
		return "";
	}
};

struct QbfSolutionType {
	std::vector<std::string> stdout_lines = {};
	dict<pool<std::string>, std::string> hole_to_value = {};
	double solver_time = 0;
	bool sat = false;
	bool unknown = true; //true if neither 'sat' nor 'unsat'

	dict<std::pair<pool<std::string>, int>, RTLIL::SigBit> get_hole_loc_idx_sigbit_map(RTLIL::Module *module) const {
		dict<std::pair<pool<std::string>, int>, RTLIL::SigBit> hole_loc_idx_to_sigbit;
		pool<RTLIL::SigBit> anyconst_sigbits;
		dict<RTLIL::SigBit, RTLIL::SigBit> anyconst_sigbit_to_wire_sigbit;

		for (auto cell : module->cells()) {
			pool<std::string> cell_src = cell->get_strpool_attribute(ID::src);
			auto pos = hole_to_value.find(cell_src);
			if (pos != hole_to_value.end() && cell->type.in("$anyconst", "$anyseq")) {
				RTLIL::SigSpec port_y = cell->getPort(ID::Y);
				for (int i = GetSize(port_y) - 1; i >= 0; --i) {
					hole_loc_idx_to_sigbit[std::make_pair(pos->first, i)] = port_y[i];
					anyconst_sigbits.insert(port_y[i]);
				}
			}
		}

		for (auto &conn : module->connections()) {
			auto lhs = conn.first;
			auto rhs = conn.second;
			for (auto i = 0; i < GetSize(rhs); ++i) {
				if (anyconst_sigbits[rhs[i]]) {
					auto pos = anyconst_sigbit_to_wire_sigbit.find(rhs[i]);
					if (pos != anyconst_sigbit_to_wire_sigbit.end())
						log_cmd_error("conflicting names for hole $anyconst sigbit %s\n", log_signal(rhs[i]));
					anyconst_sigbit_to_wire_sigbit[rhs[i]] = lhs[i];
				}
			}
		}

		for (auto &it : hole_loc_idx_to_sigbit) {
			auto pos = anyconst_sigbit_to_wire_sigbit.find(it.second);
			if (pos != anyconst_sigbit_to_wire_sigbit.end())
				it.second = pos->second;
		}

		return hole_loc_idx_to_sigbit;
	}

	void dump_model(RTLIL::Module *module) const {
		log("Satisfiable model:\n");
		auto hole_loc_idx_to_sigbit = get_hole_loc_idx_sigbit_map(module);
		for (auto &it : hole_to_value) {
			pool<std::string> hole_loc = it.first;
			std::string hole_value = it.second;

			for (unsigned int i = 0; i < hole_value.size(); ++i) {
				int bit_idx = GetSize(hole_value) - 1 - i;
				auto it = hole_loc_idx_to_sigbit.find(std::make_pair(hole_loc, i));
				log_assert(it != hole_loc_idx_to_sigbit.end());

				RTLIL::SigBit hole_sigbit = it->second;
				log("\t%s = 1'b%c\n", log_signal(hole_sigbit), hole_value[bit_idx]);
			}
		}
	}

	void write_solution(RTLIL::Module *module, const std::string &file) const {
		std::ofstream fout(file.c_str());
		if (!fout)
			log_cmd_error("could not open solution file for writing.\n");

		//There is a question here: How exactly shall we identify holes?
		//There are at least two reasonable options:
		//1. By the source location of the $anyconst cells
		//2. By the name(s) of the wire(s) connected to each SigBit of the $anyconst cell->getPort(ID::Y) SigSpec.
		//
		//Option 1 has the benefit of being very precise.  There is very limited potential for confusion, as long
		//as the source attribute has been set.  However, if the source attribute is not set, this won't work.
		//More importantly, we want to have the ability to port hole assignments to other modules with compatible
		//hole names and widths.  Obviously in those cases source locations of the $anyconst cells will not match.
		//
		//Option 2 has the benefits previously described, but wire names can be changed automatically by 
		//optimization or techmapping passes, especially when (ex/im)porting from BLIF for optimization with ABC.
		//
		//The approach taken here is to allow both options.  We write the assignment information for each bit of
		//the solution on a separate line.  Each line is of one of two forms:
		//
		//location bit name = value
		//location bit name [offset] = value
		//
		//where '[', ']', and '=' are literal symbols, "location" is the $anyconst cell source location attribute,
		//"bit" is the index of the $anyconst cell, "name" is the `wire->name` field of the SigBit corresponding
		//to the current bit of the $anyconst cell->getPort(ID::Y), "offset" is the `offset` field of that same
		//SigBit, and "value", which is either '0' or '1', represents the assignment for that bit.
		auto hole_loc_idx_to_sigbit = get_hole_loc_idx_sigbit_map(module);
		for (auto &x : hole_to_value) {
			std::string src_as_str = std::accumulate(x.first.begin(), x.first.end(), std::string(), [](const std::string &a, const std::string &b){return a + "|" + b;});
			for (auto i = 0; i < GetSize(x.second); ++i)
				fout << src_as_str.c_str() << " " << i << " " << log_signal(hole_loc_idx_to_sigbit[std::make_pair(x.first, i)]) << " = " << x.second[GetSize(x.second) - 1 - i] << std::endl;
		}
	}

	void recover_solution() {
		YS_REGEX_TYPE sat_regex = YS_REGEX_COMPILE("Status: PASSED");
		YS_REGEX_TYPE unsat_regex = YS_REGEX_COMPILE("Solver Error.*model is not available");
		YS_REGEX_TYPE unsat_regex2 = YS_REGEX_COMPILE("Status: FAILED");
		YS_REGEX_TYPE timeout_regex = YS_REGEX_COMPILE("No solution found! \\(timeout\\)");
		YS_REGEX_TYPE timeout_regex2 = YS_REGEX_COMPILE("No solution found! \\(interrupted\\)");
		YS_REGEX_TYPE unknown_regex = YS_REGEX_COMPILE("No solution found! \\(unknown\\)");
		YS_REGEX_TYPE unknown_regex2 = YS_REGEX_COMPILE("Unexpected EOF response from solver");
		YS_REGEX_TYPE memout_regex = YS_REGEX_COMPILE("Solver Error:.*error \"out of memory\"");
		YS_REGEX_TYPE hole_value_regex = YS_REGEX_COMPILE_WITH_SUBS("Value for anyconst in [a-zA-Z0-9_]* \\(([^:]*:[^\\)]*)\\): (.*)");
#ifndef NDEBUG
		YS_REGEX_TYPE hole_loc_regex = YS_REGEX_COMPILE("[^:]*:[0-9]+.[0-9]+-[0-9]+.[0-9]+");
		YS_REGEX_TYPE hole_val_regex = YS_REGEX_COMPILE("[0-9]+");
#endif
		YS_REGEX_MATCH_TYPE m;
		bool sat_regex_found = false;
		bool unsat_regex_found = false;
		dict<std::string, bool> hole_value_recovered;
		for (const std::string &x : stdout_lines) {
			if(YS_REGEX_NS::regex_search(x, m, hole_value_regex)) {
				std::string loc = m[1].str();
				std::string val = m[2].str();
#ifndef NDEBUG
				log_assert(YS_REGEX_NS::regex_search(loc, hole_loc_regex));
				log_assert(YS_REGEX_NS::regex_search(val, hole_val_regex));
#endif
				auto locs = split_tokens(loc, "|");
				pool<std::string> loc_pool(locs.begin(), locs.end());
				hole_to_value[loc_pool] = val;
			}
			else if (YS_REGEX_NS::regex_search(x, sat_regex)) {
				sat_regex_found = true;
				sat = true;
				unknown = false;
			}
			else if (YS_REGEX_NS::regex_search(x, unsat_regex)) {
				unsat_regex_found = true;
				sat = false;
				unknown = false;
			}
			else if (YS_REGEX_NS::regex_search(x, memout_regex)) {
				unknown = true;
				log_warning("solver ran out of memory\n");
			}
			else if (YS_REGEX_NS::regex_search(x, timeout_regex)) {
				unknown = true;
				log_warning("solver timed out\n");
			}
			else if (YS_REGEX_NS::regex_search(x, timeout_regex2)) {
				unknown = true;
				log_warning("solver timed out\n");
			}
			else if (YS_REGEX_NS::regex_search(x, unknown_regex)) {
				unknown = true;
				log_warning("solver returned \"unknown\"\n");
			}
			else if (YS_REGEX_NS::regex_search(x, unsat_regex2)) {
				unsat_regex_found = true;
				sat = false;
				unknown = false;
			}
			else if (YS_REGEX_NS::regex_search(x, unknown_regex2)) {
				unknown = true;
			}
		}
		log_assert(!unknown && sat? sat_regex_found : true);
		log_assert(!unknown && !sat? unsat_regex_found : true);
	}
};

void print_proof_failed()
{
	log("\n");
	log("   ______                   ___       ___       _ _            _ _ \n");
	log("  (_____ \\                 / __)     / __)     (_) |          | | |\n");
	log("   _____) )___ ___   ___ _| |__    _| |__ _____ _| | _____  __| | |\n");
	log("  |  ____/ ___) _ \\ / _ (_   __)  (_   __|____ | | || ___ |/ _  |_|\n");
	log("  | |   | |  | |_| | |_| || |       | |  / ___ | | || ____( (_| |_ \n");
	log("  |_|   |_|   \\___/ \\___/ |_|       |_|  \\_____|_|\\_)_____)\\____|_|\n");
	log("\n");
}

void print_qed()
{
	log("\n");
	log("                  /$$$$$$      /$$$$$$$$     /$$$$$$$    \n");
	log("                 /$$__  $$    | $$_____/    | $$__  $$   \n");
	log("                | $$  \\ $$    | $$          | $$  \\ $$   \n");
	log("                | $$  | $$    | $$$$$       | $$  | $$   \n");
	log("                | $$  | $$    | $$__/       | $$  | $$   \n");
	log("                | $$/$$ $$    | $$          | $$  | $$   \n");
	log("                |  $$$$$$/ /$$| $$$$$$$$ /$$| $$$$$$$//$$\n");
	log("                 \\____ $$$|__/|________/|__/|_______/|__/\n");
	log("                       \\__/                              \n");
	log("\n");
}

YOSYS_NAMESPACE_END

#endif
