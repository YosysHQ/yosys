/*
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

#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "kernel/consteval.h"
#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "kernel/register.h"
#include <algorithm>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct QbfSolutionType {
	std::vector<std::string> stdout_lines;
	dict<std::string, std::string> hole_to_value;
	bool sat;
	bool unknown; //true if neither 'sat' nor 'unsat'

	QbfSolutionType() : sat(false), unknown(true) {}
};

struct QbfSolveOptions {
	bool specialize, specialize_from_file, write_solution, nocleanup, dump_final_smt2, assume_outputs, assume_neg;
	bool nooptimize, nobisection;
	bool sat, unsat, show_smtbmc;
	enum Solver{Z3, Yices, CVC4} solver;
	int timeout;
	std::string specialize_soln_file;
	std::string write_soln_soln_file;
	std::string dump_final_smt2_file;
	size_t argidx;
	QbfSolveOptions() : specialize(false), specialize_from_file(false), write_solution(false),
			nocleanup(false), dump_final_smt2(false), assume_outputs(false), assume_neg(false),
			nooptimize(false), nobisection(false), sat(false), unsat(false), show_smtbmc(false),
			solver(Yices), timeout(0), argidx(0) {};
};

std::string get_solver_name(const QbfSolveOptions &opt) {
	if (opt.solver == opt.Solver::Z3)
		return "z3";
	else if (opt.solver == opt.Solver::Yices)
		return "yices";
	else if (opt.solver == opt.Solver::CVC4)
		return "cvc4";
	else
		log_cmd_error("unknown solver specified.\n");
	return "";
}

void recover_solution(QbfSolutionType &sol) {
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
	for (const std::string &x : sol.stdout_lines) {
		if(YS_REGEX_NS::regex_search(x, m, hole_value_regex)) {
			std::string loc = m[1].str();
			std::string val = m[2].str();
#ifndef NDEBUG
			log_assert(YS_REGEX_NS::regex_search(loc, hole_loc_regex));
			log_assert(YS_REGEX_NS::regex_search(val, hole_val_regex));
#endif
			sol.hole_to_value[loc] = val;
		}
		else if (YS_REGEX_NS::regex_search(x, sat_regex)) {
			sat_regex_found = true;
			sol.sat = true;
			sol.unknown = false;
		}
		else if (YS_REGEX_NS::regex_search(x, unsat_regex)) {
			unsat_regex_found = true;
			sol.sat = false;
			sol.unknown = false;
		}
		else if (YS_REGEX_NS::regex_search(x, memout_regex)) {
			sol.unknown = true;
			log_warning("solver ran out of memory\n");
		}
		else if (YS_REGEX_NS::regex_search(x, timeout_regex)) {
			sol.unknown = true;
			log_warning("solver timed out\n");
		}
		else if (YS_REGEX_NS::regex_search(x, timeout_regex2)) {
			sol.unknown = true;
			log_warning("solver timed out\n");
		}
		else if (YS_REGEX_NS::regex_search(x, unknown_regex)) {
			sol.unknown = true;
			log_warning("solver returned \"unknown\"\n");
		}
		else if (YS_REGEX_NS::regex_search(x, unsat_regex2)) {
			unsat_regex_found = true;
			sol.sat = false;
			sol.unknown = false;
		}
		else if (YS_REGEX_NS::regex_search(x, unknown_regex2)) {
			sol.unknown = true;
		}
	}
#ifndef NDEBUG
	log_assert(!sol.unknown && sol.sat? sat_regex_found : true);
	log_assert(!sol.unknown && !sol.sat? unsat_regex_found : true);
#endif
}

dict<std::string, std::string> get_hole_loc_name_map(RTLIL::Module *module, const QbfSolutionType &sol) {
	dict<std::string, std::string> hole_loc_to_name;
	for (auto cell : module->cells()) {
		std::string cell_src = cell->get_src_attribute();
		auto pos = sol.hole_to_value.find(cell_src);
		if (pos != sol.hole_to_value.end() && cell->type.in("$anyconst", "$anyseq")) {
			log_assert(hole_loc_to_name.find(pos->first) == hole_loc_to_name.end());
			hole_loc_to_name[pos->first] = cell->getPort(ID::Y).as_wire()->name.str();
		}
	}

	return hole_loc_to_name;
}

pool<std::string> validate_design_and_get_inputs(RTLIL::Module *module, const QbfSolveOptions &opt) {
	bool found_input = false;
	bool found_hole = false;
	bool found_1bit_output = false;
	bool found_assert_assume = false;
	pool<std::string> input_wires;
	for (auto wire : module->wires()) {
		if (wire->port_input) {
			found_input = true;
			input_wires.insert(wire->name.str());
		}
		if (wire->port_output && wire->width == 1)
			found_1bit_output = true;
	}
	for (auto cell : module->cells()) {
		if (cell->type == "$allconst")
			found_input = true;
		if (cell->type == "$anyconst")
			found_hole = true;
		if (cell->type.in("$assert", "$assume"))
			found_assert_assume = true;
	}
	if (!found_input)
		log_cmd_error("Can't perform QBF-SAT on a miter with no inputs!\n");
	if (!found_hole)
		log_cmd_error("Did not find any existentially-quantified variables. Use 'sat' instead.\n");
	if (!found_1bit_output && !found_assert_assume)
		log_cmd_error("Did not find any single-bit outputs or $assert/$assume cells. Is this a miter circuit?\n");
	if (!found_assert_assume && !opt.assume_outputs)
		log_cmd_error("Did not find any $assert/$assume cells. Single-bit outputs were found, but `-assume-outputs` was not specified.\n");

	return input_wires;
}

void write_solution(RTLIL::Module *module, const QbfSolutionType &sol, const std::string &file) {
	std::ofstream fout(file.c_str());
	if (!fout)
		log_cmd_error("could not open solution file for writing.\n");

	dict<std::string, std::string> hole_loc_to_name = get_hole_loc_name_map(module, sol);
	for(auto &x : sol.hole_to_value)
		fout << hole_loc_to_name[x.first] << "=" << x.second << std::endl;
}

void specialize_from_file(RTLIL::Module *module, const std::string &file) {
	YS_REGEX_TYPE hole_assn_regex = YS_REGEX_COMPILE_WITH_SUBS("^(.*)=([01]+)$");
	YS_REGEX_MATCH_TYPE m;
	pool<RTLIL::Cell *> anyconsts_to_remove;
	dict<std::string, std::string> hole_name_to_value;
	std::ifstream fin(file.c_str());
	if (!fin)
		log_cmd_error("could not read solution file.\n");

	std::string buf;
	while (std::getline(fin, buf)) {
		log_assert(YS_REGEX_NS::regex_search(buf, m, hole_assn_regex));
		std::string hole_name = m[1].str();
		std::string hole_value = m[2].str();
		hole_name_to_value[hole_name] = hole_value;
	}

	for (auto cell : module->cells())
		if (cell->type == "$anyconst") {
			auto anyconst_port_y = cell->getPort(ID::Y).as_wire();
			if (anyconst_port_y == nullptr)
				continue;
			if (hole_name_to_value.find(anyconst_port_y->name.str()) != hole_name_to_value.end())
				anyconsts_to_remove.insert(cell);
		}
	for (auto cell : anyconsts_to_remove)
		module->remove(cell);

	for (auto &it : hole_name_to_value) {
		std::string hole_name = it.first;
		std::string hole_value = it.second;
		RTLIL::Wire *wire = module->wire(hole_name);
#ifndef NDEBUG
		log_assert(wire != nullptr);
		log_assert(wire->width > 0 && GetSize(hole_value) == wire->width);
#endif

		log("Specializing %s from file with %s = %d'b%s.\n", module->name.c_str(), hole_name.c_str(), wire->width, hole_value.c_str());
		std::vector<RTLIL::SigBit> value_bv;
		value_bv.reserve(wire->width);
		for (char c : hole_value)
			value_bv.emplace_back(c == '1'? RTLIL::S1 : RTLIL::S0);
		std::reverse(value_bv.begin(), value_bv.end());
		module->connect(wire, value_bv);
	}
}

void specialize(RTLIL::Module *module, const QbfSolutionType &sol, bool quiet = false) {
	dict<std::string, std::string> hole_loc_to_name = get_hole_loc_name_map(module, sol);
	pool<RTLIL::Cell *> anyconsts_to_remove;
	for (auto cell : module->cells())
		if (cell->type == "$anyconst")
			if (hole_loc_to_name.find(cell->get_src_attribute()) != hole_loc_to_name.end())
				anyconsts_to_remove.insert(cell);
	for (auto cell : anyconsts_to_remove)
		module->remove(cell);
	for (auto &it : sol.hole_to_value) {
		std::string hole_loc = it.first;
		std::string hole_value = it.second;

#ifndef NDEBUG
		auto pos = hole_loc_to_name.find(hole_loc);
		log_assert(pos != hole_loc_to_name.end());
#endif

		std::string hole_name = hole_loc_to_name[hole_loc];
		RTLIL::Wire *wire = module->wire(hole_name);
#ifndef NDEBUG
		log_assert(wire != nullptr);
		log_assert(wire->width > 0 && GetSize(hole_value) == wire->width);
#endif

		if (!quiet)
			log("Specializing %s with %s = %d'b%s.\n", module->name.c_str(), hole_name.c_str(), wire->width, hole_value.c_str());
		std::vector<RTLIL::SigBit> value_bv;
		value_bv.reserve(wire->width);
		for (char c : hole_value)
			value_bv.emplace_back(c == '1'? RTLIL::S1 : RTLIL::S0);
		std::reverse(value_bv.begin(), value_bv.end());
		module->connect(wire, value_bv);
	}
}

void dump_model(RTLIL::Module *module, const QbfSolutionType &sol) {
	log("Satisfiable model:\n");
	dict<std::string, std::string> hole_loc_to_name = get_hole_loc_name_map(module, sol);
	for (auto &it : sol.hole_to_value) {
		std::string hole_loc = it.first;
		std::string hole_value = it.second;

#ifndef NDEBUG
		auto pos = hole_loc_to_name.find(hole_loc);
		log_assert(pos != hole_loc_to_name.end());
#endif

		std::string hole_name = hole_loc_to_name[hole_loc];
		log("\t%s = %lu'b%s\n", hole_name.c_str(), hole_value.size(), hole_value.c_str());
		std::vector<RTLIL::SigBit> value_bv;
		value_bv.reserve(hole_value.size());
		for (char c : hole_value)
			value_bv.emplace_back(c == '1'? RTLIL::S1 : RTLIL::S0);
		std::reverse(value_bv.begin(), value_bv.end());
	}
}

void allconstify_inputs(RTLIL::Module *module, const pool<std::string> &input_wires) {
	for (auto &n : input_wires) {
		RTLIL::Wire *input = module->wire(n);
#ifndef NDEBUG
		log_assert(input != nullptr);
#endif

		RTLIL::Cell *allconst = module->addCell("$allconst$" + n, "$allconst");
		allconst->setParam(ID(WIDTH), input->width);
		allconst->setPort(ID::Y, input);
		allconst->set_src_attribute(input->get_src_attribute());
		input->port_input = false;
		log("Replaced input %s with $allconst cell.\n", n.c_str());
	}
	module->fixup_ports();
}

void assume_miter_outputs(RTLIL::Module *module, const QbfSolveOptions &opt) {
	std::vector<RTLIL::Wire *> wires_to_assume;
	for (auto w : module->wires())
		if (w->port_output && w->width == 1)
			wires_to_assume.push_back(w);

	if (wires_to_assume.size() == 0)
		return;
	else {
		log("Adding $assume cell for output(s): ");
		for (auto w : wires_to_assume)
			log("\"%s\" ", w->name.c_str());
		log("\n");
	}

	if (opt.assume_neg) {
		for (unsigned int i = 0; i < wires_to_assume.size(); ++i) {
			RTLIL::SigSpec n_wire = module->LogicNot(wires_to_assume[i]->name.str() + "__n__qbfsat", wires_to_assume[i], false, wires_to_assume[i]->get_src_attribute());
			wires_to_assume[i] = n_wire.as_wire();
		}
	}

	for (auto i = 0; wires_to_assume.size() > 1; ++i) {
		std::vector<RTLIL::Wire *> buf;
		for (auto j = 0; j + 1 < GetSize(wires_to_assume); j += 2) {
			std::stringstream strstr; strstr << i << "_" << j;
			RTLIL::Wire *and_wire = module->addWire("\\_qbfsat_and_" + strstr.str(), 1);
			module->addLogicAnd("$_qbfsat_and_" + strstr.str(), wires_to_assume[j], wires_to_assume[j+1], and_wire, false, wires_to_assume[j]->get_src_attribute());
			buf.push_back(and_wire);
		}
		if (wires_to_assume.size() % 2 == 1)
			buf.push_back(wires_to_assume[wires_to_assume.size() - 1]);
		wires_to_assume.swap(buf);
	}

#ifndef NDEBUG
	log_assert(wires_to_assume.size() == 1);
#endif
	module->addAssume("$assume_qbfsat_miter_outputs", wires_to_assume[0], RTLIL::S1);
}

QbfSolutionType call_qbf_solver(RTLIL::Module *mod, const QbfSolveOptions &opt, const std::string &tempdir_name, const bool quiet = false, const int iter_num = 0) {
	//Execute and capture stdout from `yosys-smtbmc -s z3 -t 1 -g --binary [--dump-smt2 <file>]`
	QbfSolutionType ret;
	const std::string yosys_smtbmc_exe = proc_self_dirname() + "yosys-smtbmc";
	const std::string smt2_command = "write_smt2 -stbv -wires " + tempdir_name + "/problem" + (iter_num != 0? stringf("%d", iter_num) : "") + ".smt2";
	const std::string smtbmc_warning = "z3: WARNING:";
	const std::string smtbmc_cmd = yosys_smtbmc_exe + " -s " + (get_solver_name(opt)) + (opt.timeout != 0? stringf(" --timeout %d", opt.timeout) : "") + " -t 1 -g --binary " + (opt.dump_final_smt2? "--dump-smt2 " + opt.dump_final_smt2_file + " " : "") + tempdir_name + "/problem" + (iter_num != 0? stringf("%d", iter_num) : "") + ".smt2 2>&1";

	Pass::call(mod->design, smt2_command);

	auto process_line = [&ret, &smtbmc_warning, &opt, &quiet](const std::string &line) {
		ret.stdout_lines.push_back(line.substr(0, line.size()-1)); //don't include trailing newline
		auto warning_pos = line.find(smtbmc_warning);
		if (warning_pos != std::string::npos)
			log_warning("%s", line.substr(warning_pos + smtbmc_warning.size() + 1).c_str());
		else
			if (opt.show_smtbmc && !quiet)
				log("smtbmc output: %s", line.c_str());
	};
	log_header(mod->design, "Solving QBF-SAT problem.\n");
	if (!quiet) log("Launching \"%s\".\n", smtbmc_cmd.c_str());
	run_command(smtbmc_cmd, process_line);

	recover_solution(ret);
	return ret;
}

QbfSolutionType qbf_solve(RTLIL::Module *mod, const QbfSolveOptions &opt) {
	QbfSolutionType ret, best_soln;
	const std::string tempdir_name = make_temp_dir("/tmp/yosys-z3-XXXXXX");
	RTLIL::Module *module = mod;
	RTLIL::Design *design = module->design;
	std::string module_name = module->name.str();
	RTLIL::Wire *wire_to_optimize = nullptr;
	RTLIL::IdString wire_to_optimize_name;
	bool maximize = false;
	log_assert(module->design != nullptr);

	Pass::call(design, "design -push-copy");

	//Replace input wires with wires assigned $allconst cells:
	pool<std::string> input_wires = validate_design_and_get_inputs(module, opt);
	allconstify_inputs(module, input_wires);
	if (opt.assume_outputs)
		assume_miter_outputs(module, opt);

	//Find the wire to be optimized, if any:
	for (auto wire : module->wires())
		if (wire->get_bool_attribute("\\maximize") || wire->get_bool_attribute("\\minimize"))
			wire_to_optimize = wire;
	if (wire_to_optimize != nullptr) {
		wire_to_optimize_name = wire_to_optimize->name;
		maximize = wire_to_optimize->get_bool_attribute("\\maximize");
	}

	if (opt.nobisection || opt.nooptimize) {
		if (wire_to_optimize != nullptr && opt.nooptimize) {
			wire_to_optimize->set_bool_attribute("\\maximize", false);
			wire_to_optimize->set_bool_attribute("\\minimize", false);
		}
		ret = call_qbf_solver(module, opt, tempdir_name, false, 0);
	} else {
		//Do the iterated bisection method:
		unsigned int iter_num = 1;
		unsigned int success = 0;
		unsigned int failure = 0;
		unsigned int cur_thresh = 0;

		log_assert(wire_to_optimize != nullptr);
		log("%s wire \"%s\".\n", (maximize? "Maximizing" : "Minimizing"), log_signal(wire_to_optimize));

		//If maximizing, grow until we get a failure.  Then bisect success and failure.
		while (failure == 0 || success - failure > 1) {
			Pass::call(design, "design -push-copy");
			log_header(design, "Preparing QBF-SAT problem.\n");

			if (cur_thresh != 0) {
				//Add thresholding logic (but not on the initial run when we don't have a sense of where to start):
				RTLIL::SigSpec comparator = maximize? module->Ge(NEW_ID, module->wire(wire_to_optimize_name), RTLIL::Const(cur_thresh), false)
				                                    : module->Le(NEW_ID, module->wire(wire_to_optimize_name), RTLIL::Const(cur_thresh), false);

				module->addAssume(wire_to_optimize_name.str() + "__threshold", comparator, RTLIL::Const(1, 1));
				log("Trying to solve with %s %s %d.\n", wire_to_optimize_name.c_str(), (maximize? ">=" : "<="), cur_thresh);
			}

			ret = call_qbf_solver(module, opt, tempdir_name, false, iter_num);
			Pass::call(design, "design -pop");
			module = design->module(module_name);

			if (!ret.unknown && ret.sat) {
				Pass::call(design, "design -push-copy");
				specialize(module, ret, true);

				RTLIL::SigSpec wire, value, undef;
				RTLIL::SigSpec::parse_sel(wire, design, module, wire_to_optimize_name.str());

				ConstEval ce(module);
				value = wire;
				if (!ce.eval(value, undef))
					log_cmd_error("Failed to evaluate signal %s: Missing value for %s.\n", log_signal(wire), log_signal(undef));
				log_assert(value.is_fully_const());
				success = value.as_const().as_int();
				best_soln = ret;
				log("Problem is satisfiable with %s = %d.\n", wire_to_optimize_name.c_str(), success);
				Pass::call(design, "design -pop");
				module = design->module(module_name);

				//sometimes this happens if we get an 'unknown' or timeout
				if (!maximize && success < failure)
					break;
				else if (maximize && success > failure)
					break;
			} else {
				//Treat 'unknown' as UNSAT
				failure = cur_thresh;
				if (failure == 0) {
					log("Problem is NOT satisfiable.\n");
					break;
				}
				else
					log("Problem is NOT satisfiable with %s %s %d.\n", wire_to_optimize_name.c_str(), (maximize? ">=" : "<="), failure);
			}

			iter_num++;
			cur_thresh = (maximize && failure == 0)? 2 * success //growth
			                                       : (success + failure) / 2; //bisection
		}
		if (success != 0 || failure != 0) {
			log("Wire %s is %s at %d.\n", wire_to_optimize_name.c_str(), (maximize? "maximized" : "minimized"), success);
			ret = best_soln;
		}
	}

	if(!opt.nocleanup)
		remove_directory(tempdir_name);

	Pass::call(design, "design -pop");

	return ret;
}

QbfSolveOptions parse_args(const std::vector<std::string> &args) {
	QbfSolveOptions opt;
	for (opt.argidx = 1; opt.argidx < args.size(); opt.argidx++) {
		if (args[opt.argidx] == "-nocleanup") {
			opt.nocleanup = true;
			continue;
		}
		else if (args[opt.argidx] == "-specialize") {
			opt.specialize = true;
			continue;
		}
		else if (args[opt.argidx] == "-assume-outputs") {
			opt.assume_outputs = true;
			continue;
		}
		else if (args[opt.argidx] == "-assume-negative-polarity") {
			opt.assume_neg = true;
			continue;
		}
		else if (args[opt.argidx] == "-nooptimize") {
			opt.nooptimize = true;
			continue;
		}
		else if (args[opt.argidx] == "-nobisection") {
			opt.nobisection = true;
			continue;
		}
		else if (args[opt.argidx] == "-solver") {
			if (args.size() <= opt.argidx + 1)
				log_cmd_error("solver not specified.\n");
			else {
				if (args[opt.argidx+1] == "z3")
					opt.solver = opt.Solver::Z3;
				else if (args[opt.argidx+1] == "yices")
					opt.solver = opt.Solver::Yices;
				else if (args[opt.argidx+1] == "cvc4")
					opt.solver = opt.Solver::CVC4;
				else
					log_cmd_error("Unknown solver \"%s\".\n", args[opt.argidx+1].c_str());
				opt.argidx++;
			}
			continue;
		}
		else if (args[opt.argidx] == "-timeout") {
			if (args.size() <= opt.argidx + 1)
				log_cmd_error("timeout not specified.\n");
			else {
				int timeout = atoi(args[opt.argidx+1].c_str());
				if (timeout > 0)
					opt.timeout = timeout;
				else
					log_cmd_error("timeout must be greater than 0.\n");
				opt.argidx++;
			}
			continue;
		}
		else if (args[opt.argidx] == "-sat") {
			opt.sat = true;
			continue;
		}
		else if (args[opt.argidx] == "-unsat") {
			opt.unsat = true;
			continue;
		}
		else if (args[opt.argidx] == "-show-smtbmc") {
			opt.show_smtbmc = true;
			continue;
		}
		else if (args[opt.argidx] == "-dump-final-smt2") {
			opt.dump_final_smt2 = true;
			if (args.size() <= opt.argidx + 1)
				log_cmd_error("smt2 file not specified.\n");
			else
				opt.dump_final_smt2_file = args[++opt.argidx];
			continue;
		}
		else if (args[opt.argidx] == "-specialize-from-file") {
			opt.specialize_from_file = true;
			if (args.size() <= opt.argidx + 1)
				log_cmd_error("solution file not specified.\n");
			else
				opt.specialize_soln_file = args[++opt.argidx];
			continue;
		}
		else if (args[opt.argidx] == "-write-solution") {
			opt.write_solution = true;
			if (args.size() <= opt.argidx + 1)
				log_cmd_error("solution file not specified.\n");
			else
				opt.write_soln_soln_file = args[++opt.argidx];
			continue;
		}
		break;
	}

	return opt;
}

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

struct QbfSatPass : public Pass {
	QbfSatPass() : Pass("qbfsat", "solve a 2QBF-SAT problem in the circuit") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    qbfsat [options] [selection]\n");
		log("\n");
		log("This command solves an \"exists-forall\" 2QBF-SAT problem defined over the currently\n");
		log("selected module. Existentially-quantified variables are declared by assigning a wire\n");
		log("\"$anyconst\". Universally-quantified variables may be explicitly declared by assigning\n");
		log("a wire \"$allconst\", but module inputs will be treated as universally-quantified\n");
		log("variables by default.\n");
		log("\n");
		log("    -nocleanup\n");
		log("        Do not delete temporary files and directories. Useful for debugging.\n");
		log("\n");
		log("    -dump-final-smt2 <file>\n");
		log("        Pass the --dump-smt2 option to yosys-smtbmc.\n");
		log("\n");
		log("    -assume-outputs\n");
		log("        Add an \"$assume\" cell for the conjunction of all one-bit module output wires.\n");
		log("\n");
		log("    -assume-negative-polarity\n");
		log("        When adding $assume cells for one-bit module output wires, assume they are\n");
		log("        negative polarity signals and should always be low, for example like the\n");
		log("        miters created with the `miter` command.\n");
		log("\n");
		log("    -nooptimize\n");
		log("        Ignore \"\\minimize\" and \"\\maximize\" attributes, do not emit \"(maximize)\" or\n");
		log("        \"(minimize)\" in the SMT-LIBv2, and generally make no attempt to optimize anything.\n");
		log("\n");
		log("    -nobisection\n");
		log("        If a wire is marked with the \"\\minimize\" or \"\\maximize\" attribute, do not\n");
		log("        attempt to optimize that value with the default iterated solving and threshold\n");
		log("        bisection approach. Instead, have yosys-smtbmc emit a \"(minimize)\" or \"(maximize)\"\n");
		log("        command in the SMT-LIBv2 output and hope that the solver supports optimizing\n");
		log("        quantified bitvector problems.\n");
		log("\n");
		log("    -solver <solver>\n");
		log("        Use a particular solver. Choose one of: \"z3\", \"yices\", and \"cvc4\".\n");
		log("\n");
		log("    -timeout <value>\n");
		log("        Set the per-iteration timeout in seconds.\n");
		log("\n");
		log("    -sat\n");
		log("        Generate an error if the solver does not return \"sat\".\n");
		log("\n");
		log("    -unsat\n");
		log("        Generate an error if the solver does not return \"unsat\".\n");
		log("\n");
		log("    -show-smtbmc\n");
		log("        Print the output from yosys-smtbmc.\n");
		log("\n");
		log("    -specialize\n");
		log("        If the problem is satisfiable, replace each \"$anyconst\" cell with its\n");
		log("        corresponding constant value from the model produced by the solver.\n");
		log("\n");
		log("    -specialize-from-file <solution file>\n");
		log("        Do not run the solver, but instead only attempt to replace each \"$anyconst\"\n");
		log("        cell in the current module with a constant value provided by the specified file.\n");
		log("\n");
		log("    -write-solution <solution file>\n");
		log("        If the problem is satisfiable, write the corresponding constant value for each\n");
		log("        \"$anyconst\" cell from the model produced by the solver to the specified file.");
		log("\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing QBFSAT pass (solving QBF-SAT problems in the circuit).\n");
		QbfSolveOptions opt = parse_args(args);
		extra_args(args, opt.argidx, design);

		RTLIL::Module *module = nullptr;
		for (auto mod : design->selected_modules()) {
			if (module)
				log_cmd_error("Only one module must be selected for the QBF-SAT pass! (selected: %s and %s)\n", log_id(module), log_id(mod));
			module = mod;
		}
		if (module == nullptr)
			log_cmd_error("Can't perform QBF-SAT on an empty selection!\n");

		log_push();
		if (!opt.specialize_from_file) {
			//Save the design to restore after modiyfing the current module.
			std::string module_name = module->name.str();

			QbfSolutionType ret = qbf_solve(module, opt);
			module = design->module(module_name);
			if (ret.unknown) {
				if (opt.sat || opt.unsat)
					log_cmd_error("expected problem to be %s\n", opt.sat? "SAT" : "UNSAT");
			}
			else if (ret.sat) {
				print_qed();
				if (opt.write_solution) {
					write_solution(module, ret, opt.write_soln_soln_file);
				}
				if (opt.specialize) {
					specialize(module, ret);
				} else {
					dump_model(module, ret);
				}
				if (opt.unsat)
					log_cmd_error("expected problem to be UNSAT\n");
			}
			else {
				print_proof_failed();
				if (opt.sat)
					log_cmd_error("expected problem to be SAT\n");
			}
		} else
			specialize_from_file(module, opt.specialize_soln_file);
		log_pop();
	}
} QbfSatPass;

PRIVATE_NAMESPACE_END
