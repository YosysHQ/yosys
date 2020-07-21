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

#include "kernel/yosys.h"
#include "kernel/consteval.h"
#include "qbfsat.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static inline unsigned int difference(unsigned int a, unsigned int b) {
	if (a < b)
		return b - a;
	else
		return a - b;
}

pool<std::string> validate_design_and_get_inputs(RTLIL::Module *module, bool assume_outputs) {
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
	if (!found_assert_assume && !assume_outputs)
		log_cmd_error("Did not find any $assert/$assume cells. Single-bit outputs were found, but `-assume-outputs` was not specified.\n");

	return input_wires;
}

void specialize_from_file(RTLIL::Module *module, const std::string &file) {
	YS_REGEX_TYPE hole_bit_assn_regex = YS_REGEX_COMPILE_WITH_SUBS("^(.+) ([0-9]+) ([^ ]+) \\[([0-9]+)] = ([01])$");
	YS_REGEX_TYPE hole_assn_regex = YS_REGEX_COMPILE_WITH_SUBS("^(.+) ([0-9]+) ([^ ]+) = ([01])$"); //if no index specified
	YS_REGEX_MATCH_TYPE bit_m, m;
	dict<pool<std::string>, RTLIL::Cell*> anyconst_loc_to_cell;
	dict<RTLIL::SigBit, RTLIL::State> hole_assignments;

	for (auto cell : module->cells())
		if (cell->type == "$anyconst")
			anyconst_loc_to_cell[cell->get_strpool_attribute(ID::src)] = cell;

	std::ifstream fin(file.c_str());
	if (!fin)
		log_cmd_error("could not read solution file.\n");

	std::string buf;
	while (std::getline(fin, buf)) {
		bool bit_assn = true;
		if (!YS_REGEX_NS::regex_search(buf, bit_m, hole_bit_assn_regex)) {
			bit_assn = false;
			if (!YS_REGEX_NS::regex_search(buf, m, hole_assn_regex))
				log_cmd_error("solution file is not formatted correctly: \"%s\"\n", buf.c_str());
		}

		std::string hole_loc = bit_assn? bit_m[1].str() : m[1].str();
		unsigned int hole_bit = bit_assn? atoi(bit_m[2].str().c_str()) : atoi(m[2].str().c_str());
		std::string hole_name = bit_assn? bit_m[3].str() : m[3].str();
		unsigned int hole_offset = bit_assn? atoi(bit_m[4].str().c_str()) : 0;
		RTLIL::State hole_value = bit_assn? (atoi(bit_m[5].str().c_str()) == 1? RTLIL::State::S1 : RTLIL::State::S0)
		                                  : (atoi(m[4].str().c_str()) == 1? RTLIL::State::S1 : RTLIL::State::S0);

		//We have two options to identify holes.  First, try to match wire names.  If we can't find a matching wire,
		//then try to find a cell with a matching location.
		RTLIL::SigBit hole_sigbit;
		if (module->wire(hole_name) != nullptr) {
			RTLIL::Wire *hole_wire = module->wire(hole_name);
			hole_sigbit = RTLIL::SigSpec(hole_wire)[hole_offset];
		} else {
			auto locs = split_tokens(hole_loc, "|");
			pool<std::string> hole_loc_pool(locs.begin(), locs.end());
			auto hole_cell_it = anyconst_loc_to_cell.find(hole_loc_pool);
			if (hole_cell_it == anyconst_loc_to_cell.end())
				log_cmd_error("cannot find matching wire name or $anyconst cell location for hole spec \"%s\"\n", buf.c_str());

			RTLIL::Cell *hole_cell = hole_cell_it->second;
			hole_sigbit = hole_cell->getPort(ID::Y)[hole_bit];
		}
		hole_assignments[hole_sigbit] = hole_value;
	}

	for (auto &it : anyconst_loc_to_cell)
		module->remove(it.second);

	for (auto &it : hole_assignments) {
		RTLIL::SigSpec lhs(it.first);
		RTLIL::SigSpec rhs(it.second);
		log("Specializing %s from file with %s = %d.\n", module->name.c_str(), log_signal(it.first), it.second == RTLIL::State::S1? 1 : 0);
		module->connect(lhs, rhs);
	}
}

void specialize(RTLIL::Module *module, const QbfSolutionType &sol, bool quiet = false) {
	auto hole_loc_idx_to_sigbit = sol.get_hole_loc_idx_sigbit_map(module);
	pool<RTLIL::Cell *> anyconsts_to_remove;
	for (auto cell : module->cells())
		if (cell->type == "$anyconst")
			if (hole_loc_idx_to_sigbit.find(std::make_pair(cell->get_strpool_attribute(ID::src), 0)) != hole_loc_idx_to_sigbit.end())
				anyconsts_to_remove.insert(cell);
	for (auto cell : anyconsts_to_remove)
		module->remove(cell);
	for (auto &it : sol.hole_to_value) {
		pool<std::string> hole_loc = it.first;
		std::string hole_value = it.second;

		for (unsigned int i = 0; i < hole_value.size(); ++i) {
			int bit_idx = GetSize(hole_value) - 1 - i;
			auto it = hole_loc_idx_to_sigbit.find(std::make_pair(hole_loc, i));
			log_assert(it != hole_loc_idx_to_sigbit.end());

			RTLIL::SigBit hole_sigbit = it->second;
			log_assert(hole_sigbit.wire != nullptr);
			log_assert(hole_value[bit_idx] == '0' || hole_value[bit_idx] == '1');
			RTLIL::SigSpec lhs(hole_sigbit.wire, hole_sigbit.offset, 1);
			RTLIL::State hole_bit_val = hole_value[bit_idx] == '1'? RTLIL::State::S1 : RTLIL::State::S0;
			if (!quiet)
				log("Specializing %s with %s = %d.\n", module->name.c_str(), log_signal(hole_sigbit), hole_bit_val == RTLIL::State::S0? 0 : 1)
;
			module->connect(lhs, hole_bit_val);
		}
	}
}

void allconstify_inputs(RTLIL::Module *module, const pool<std::string> &input_wires) {
	for (auto &n : input_wires) {
		RTLIL::Wire *input = module->wire(n);
		log_assert(input != nullptr);

		RTLIL::Cell *allconst = module->addCell("$allconst$" + n, "$allconst");
		allconst->setParam(ID(WIDTH), input->width);
		allconst->setPort(ID::Y, input);
		allconst->set_src_attribute(input->get_src_attribute());
		input->port_input = false;
		log("Replaced input %s with $allconst cell.\n", n.c_str());
	}
	module->fixup_ports();
}

void assume_miter_outputs(RTLIL::Module *module, bool assume_neg) {
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

	if (assume_neg) {
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

	log_assert(wires_to_assume.size() == 1);
	module->addAssume("$assume_qbfsat_miter_outputs", wires_to_assume[0], RTLIL::S1);
}

QbfSolutionType call_qbf_solver(RTLIL::Module *mod, const QbfSolveOptions &opt, const std::string &tempdir_name, const bool quiet = false, const int iter_num = 0) {
	//Execute and capture stdout from `yosys-smtbmc -s z3 -t 1 -g --binary [--dump-smt2 <file>]`
	QbfSolutionType ret;
	const std::string yosys_smtbmc_exe = proc_self_dirname() + "yosys-smtbmc";
	const std::string smtbmc_warning = "z3: WARNING:";
	const std::string smtbmc_cmd = stringf("%s -s %s %s -t 1 -g --binary %s %s/problem%d.smt2 2>&1",
			yosys_smtbmc_exe.c_str(), opt.get_solver_name().c_str(),
			(opt.timeout != 0? stringf("--timeout %d", opt.timeout) : "").c_str(),
			(opt.dump_final_smt2? "--dump-smt2 " + opt.dump_final_smt2_file : "").c_str(),
			tempdir_name.c_str(), iter_num);

	std::string smt2_command = "write_smt2 -stbv -wires ";
	for (auto &solver_opt : opt.solver_options)
		smt2_command += stringf("-solver-option %s %s ", solver_opt.first.c_str(), solver_opt.second.c_str());
	smt2_command += stringf("%s/problem%d.smt2", tempdir_name.c_str(), iter_num);
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
	int64_t begin = PerformanceTimer::query();
	run_command(smtbmc_cmd, process_line);
	int64_t end = PerformanceTimer::query();
	ret.solver_time = (end - begin) / 1e9f;
	if (!quiet) log("Solver finished in %.3f seconds.\n", ret.solver_time);

	ret.recover_solution();
	return ret;
}

QbfSolutionType qbf_solve(RTLIL::Module *mod, const QbfSolveOptions &opt) {
	QbfSolutionType ret, best_soln;
	const std::string tempdir_name = make_temp_dir("/tmp/yosys-qbfsat-XXXXXX");
	RTLIL::Module *module = mod;
	RTLIL::Design *design = module->design;
	std::string module_name = module->name.str();
	RTLIL::IdString wire_to_optimize_name = "";
	bool maximize = false;
	log_assert(module->design != nullptr);

	Pass::call(design, "design -push-copy");

	//Replace input wires with wires assigned $allconst cells:
	pool<std::string> input_wires = validate_design_and_get_inputs(module, opt.assume_outputs);
	allconstify_inputs(module, input_wires);
	if (opt.assume_outputs)
		assume_miter_outputs(module, opt.assume_neg);

	//Find the wire to be optimized, if any:
	for (auto wire : module->wires()) {
		if (wire->get_bool_attribute("\\maximize") || wire->get_bool_attribute("\\minimize")) {
			wire_to_optimize_name = wire->name;
			maximize = wire->get_bool_attribute("\\maximize");
			if (opt.nooptimize) {
				if (maximize)
					wire->set_bool_attribute("\\maximize", false);
				else
					wire->set_bool_attribute("\\minimize", false);
			}
		}
	}

	//If -O1 or -O2 was specified, use ABC to simplify the problem:
	if (opt.oflag == opt.OptimizationLevel::O1)
		Pass::call(module->design, "abc -g AND,NAND,OR,NOR,XOR,XNOR,MUX,NMUX -script +print_stats;strash;print_stats;drwsat;print_stats;fraig;print_stats;refactor,-N,10,-lz;print_stats;&get,-n;&dch,-pem;&nf;&put " + mod->name.str());
	else if (opt.oflag == opt.OptimizationLevel::O2)
		Pass::call(module->design, "abc -g AND,NAND,OR,NOR,XOR,XNOR,MUX,NMUX -script +print_stats;strash;print_stats;drwsat;print_stats;dch,-S,1000000,-C,100000,-p;print_stats;fraig;print_stats;refactor,-N,15,-lz;print_stats;dc2,-pbl;print_stats;drwsat;print_stats;&get,-n;&dch,-pem;&nf;&put " + mod->name.str());
	if (opt.oflag != opt.OptimizationLevel::O0) {
		Pass::call(module->design, "techmap");
		Pass::call(module->design, "opt");
	}

	if (opt.nobisection || opt.nooptimize || wire_to_optimize_name == "") {
		ret = call_qbf_solver(module, opt, tempdir_name, false, 0);
	} else {
		//Do the iterated bisection method:
		unsigned int iter_num = 1;
		unsigned int success = 0;
		unsigned int failure = 0;
		unsigned int cur_thresh = 0;

		log_assert(wire_to_optimize_name != "");
		log_assert(module->wire(wire_to_optimize_name) != nullptr);
		log("%s wire \"%s\".\n", (maximize? "Maximizing" : "Minimizing"), wire_to_optimize_name.c_str());

		//If maximizing, grow until we get a failure.  Then bisect success and failure.
		while (failure == 0 || difference(success, failure) > 1) {
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
				else if (maximize && failure != 0 && success > failure)
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
			if (maximize && failure == 0 && success == 0)
				cur_thresh = 2;
			else if (maximize && failure == 0)
				cur_thresh = 2 * success; //growth
			else //if (!maximize || failure != 0)
				cur_thresh = (success + failure) / 2; //bisection
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
		else if (args[opt.argidx] == "-solver-option") {
			if (args.size() <= opt.argidx + 2)
				log_cmd_error("solver option name and value not fully specified.\n");
			opt.solver_options.emplace(args[opt.argidx+1], args[opt.argidx+2]);
			opt.argidx += 2;
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
		else if (args[opt.argidx].substr(0, 2) == "-O" && args[opt.argidx].size() == 3) {
			switch (args[opt.argidx][2]) {
				case '0':
					opt.oflag = opt.OptimizationLevel::O0;
				break;
				case '1':
					opt.oflag = opt.OptimizationLevel::O1;
				break;
				case '2':
					opt.oflag = opt.OptimizationLevel::O2;
				break;
				default:
					log_cmd_error("unknown argument %s\n", args[opt.argidx].c_str());
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

struct QbfSatPass : public Pass {
	QbfSatPass() : Pass("qbfsat", "solve a 2QBF-SAT problem in the circuit") { }
	void help() override
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
		log("        (default: yices)\n");
		log("\n");
		log("    -solver-option <name> <value>\n");
		log("        Set the specified solver option in the SMT-LIBv2 problem file.\n");
		log("\n");
		log("    -timeout <value>\n");
		log("        Set the per-iteration timeout in seconds.\n");
		log("        (default: no timeout)\n");
		log("\n");
		log("    -O0, -O1, -O2\n");
		log("        Control the use of ABC to simplify the QBF-SAT problem before solving.\n");
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

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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
					ret.write_solution(module, opt.write_soln_soln_file);
				}
				if (opt.specialize) {
					specialize(module, ret);
				} else {
					ret.dump_model(module);
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
