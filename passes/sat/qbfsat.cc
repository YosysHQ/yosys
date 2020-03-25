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
#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "kernel/register.h"
#include <cstdio>
#include <algorithm>

#if defined(_WIN32)
#  define WIFEXITED(x) 1
#  define WIFSIGNALED(x) 0
#  define WIFSTOPPED(x) 0
#  define WEXITSTATUS(x) ((x) & 0xff)
#  define WTERMSIG(x) SIGTERM
#else
#  include <sys/wait.h>
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct QbfSolutionType {
	std::vector<std::string> stdout;
	std::map<std::string, std::string> hole_to_value;
	bool sat;
	bool unknown; //true if neither 'sat' nor 'unsat'
	bool success; //true if exit code 0

	QbfSolutionType() : sat(false), unknown(true), success(false) {}
};

struct QbfSolveOptions {
	bool timeout, specialize, specialize_from_file, write_solution, nocleanup, dump_final_smt2;
	long timeout_sec;
	std::string specialize_soln_file;
	std::string write_soln_soln_file;
	std::string dump_final_smt2_file;
	size_t argidx;
	QbfSolveOptions() : timeout(false), specialize(false), specialize_from_file(false), write_solution(false),	
				nocleanup(false), dump_final_smt2(false), timeout_sec(-1), argidx(0) {};
};

void recover_solution(QbfSolutionType &sol) {
	YS_REGEX_TYPE sat_regex = YS_REGEX_COMPILE("Status: PASSED");
	YS_REGEX_TYPE unsat_regex = YS_REGEX_COMPILE("Solver Error.*model is not available");
	YS_REGEX_TYPE hole_value_regex = YS_REGEX_COMPILE_WITH_SUBS("Value for anyconst in [a-zA-Z0-9_]* \\(([^:]*:[^\\)]*)\\): (.*)");
	YS_REGEX_TYPE hole_loc_regex = YS_REGEX_COMPILE("[^:]*:[0-9]+.[0-9]+-[0-9]+.[0-9]+");
	YS_REGEX_TYPE hole_val_regex = YS_REGEX_COMPILE("[0-9]+");
	YS_REGEX_MATCH_TYPE m;
	bool sat_regex_found = false;
	bool unsat_regex_found = false;
	std::map<std::string, bool> hole_value_recovered;
	for (const std::string &x : sol.stdout) {
		if(YS_REGEX_NS::regex_search(x, m, hole_value_regex)) {
			std::string loc = m[1].str();
			std::string val = m[2].str();
			log_assert(YS_REGEX_NS::regex_search(loc, hole_loc_regex));
			log_assert(YS_REGEX_NS::regex_search(val, hole_val_regex));
			sol.hole_to_value[loc] = val;
		}
		else if (YS_REGEX_NS::regex_search(x, sat_regex))
			sat_regex_found = true;
		else if (YS_REGEX_NS::regex_search(x, unsat_regex))
			unsat_regex_found = true;
	}
	log_assert(!sol.unknown && sol.sat? sat_regex_found : true);
	log_assert(!sol.unknown && !sol.sat? unsat_regex_found : true);
}

void specialize(RTLIL::Module *module, const QbfSolutionType &ret) {
	std::map<std::string, std::string> hole_loc_to_name;
	for (auto cell : module->cells()) {
		std::string cell_src = cell->get_src_attribute();
		auto pos = ret.hole_to_value.find(cell_src);
		if (pos != ret.hole_to_value.end()) {
			log_assert(cell->type.in("$anyconst", "$anyseq"));
			log_assert(cell->hasPort(ID::Y));
			log_assert(cell->getPort(ID::Y).is_wire());
			hole_loc_to_name[pos->first] = cell->getPort(ID::Y).as_wire()->name.str();
		}
	}
	for (auto &it : ret.hole_to_value) {
		std::string hole_loc = it.first;
		std::string hole_value = it.second;

		auto pos = hole_loc_to_name.find(hole_loc);
		log_assert(pos != hole_loc_to_name.end());

		std::string hole_name = hole_loc_to_name[hole_loc];
		RTLIL::Wire *wire = module->wire(hole_name);
		log_assert(wire != nullptr);

		log("Specializing %s with %s = %d'b%s.\n", module->name.c_str(), hole_name.c_str(), wire->width, hole_value.c_str());
		std::vector<RTLIL::SigBit> value_bv;
		value_bv.reserve(wire->width);
		for (char c : hole_value)
			value_bv.push_back(c == '1'? RTLIL::S1 : RTLIL::S0);
		std::reverse(value_bv.begin(), value_bv.end());
		module->connect(wire, value_bv);
	}
}

void allconstify_inputs(RTLIL::Module *module, const std::set<std::string> &input_wires) {
	for(auto &n : input_wires) {
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

QbfSolutionType qbf_solve(RTLIL::Module *mod, const QbfSolveOptions &opt) {
	QbfSolutionType ret;
	std::string yosys_smtbmc_exe = proc_self_dirname() + "yosys-smtbmc";
	std::string smtbmc_warning = "z3: WARNING:";

	std::string tempdir_name = "/tmp/yosys-z3-XXXXXX";
	tempdir_name = make_temp_dir(tempdir_name);
	std::string smt2_command = "write_smt2 -stbv -wires " + tempdir_name + "/problem.smt2";
	log_assert(mod->design != nullptr);
	Pass::call(mod->design, smt2_command);

	//Execute and capture stdout from `yosys-smtbmc -s z3 -t 1 -g --binary [--dump-smt2 <file>]`
	{
		fflush(stdout);
		bool keep_reading = true;
		int status = 0;
		int retval = 0;
		char buf[1024] = {0};
		std::string linebuf = "";
		std::string cmd = yosys_smtbmc_exe + " -s z3 -t 1 -g --binary " + (opt.dump_final_smt2? "--dump-smt2 " + opt.dump_final_smt2_file + " " : "") + tempdir_name + "/problem.smt2 2>&1";
		log("Launching \"%s\".\n", cmd.c_str());

#ifndef EMSCRIPTEN
		FILE *f = popen(cmd.c_str(), "r");
		if (f == nullptr)
			log_cmd_error("errno %d after popen() returned NULL.\n", errno);
		while (keep_reading) {
			keep_reading = (fgets(buf, sizeof(buf), f) != nullptr);
			linebuf += buf;
			memset(buf, 0, sizeof(buf));

			auto pos = linebuf.find('\n');
			while (pos != std::string::npos) {
				std::string line = linebuf.substr(0, pos);
				linebuf.erase(0, pos + 1);
				ret.stdout.push_back(line);
				auto warning_pos = line.find(smtbmc_warning);
				if(warning_pos != std::string::npos)
					log_warning("%s\n", line.substr(warning_pos + smtbmc_warning.size() + 1).c_str());
				else
					log("smtbmc output: %s\n", line.c_str());

				pos = linebuf.find('\n');
			}
		}
		status = pclose(f);
#endif

		if(WIFEXITED(status)) {
		    retval = WEXITSTATUS(status);
		}
		else if(WIFSIGNALED(status)) {
		    retval = WTERMSIG(status);
		}
		else if(WIFSTOPPED(status)) {
		    retval = WSTOPSIG(status);
		}

		if (retval == 0) {
			ret.sat = true;
			ret.unknown = false;
		} else if (retval == 1) {
			ret.sat = false;
			ret.unknown = false;
		}
	}

	if(!opt.nocleanup)
		remove_directory(tempdir_name);

	recover_solution(ret);

	return ret;
}

std::set<std::string> validate_design_and_get_inputs(RTLIL::Module *module) {
	bool found_input = false;
	bool found_hole = false;
	bool found_1bit_output = false;
	std::set<std::string> input_wires;
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
			found_1bit_output = true;
	}
	if (!found_input)
		log_cmd_error("Can't perform QBF-SAT on a miter with no inputs!\n");
	if (!found_hole)
		log_cmd_error("Did not find any existentially-quantified variables. Use 'sat' instead.\n");
	if (!found_1bit_output)
		log_cmd_error("Did not find any single-bit outputs, assert()s, or assume()s.  Is this a miter circuit?\n");

	return input_wires;
}


QbfSolveOptions parse_args(const std::vector<std::string> &args) {
	QbfSolveOptions opt;
	for (opt.argidx = 1; opt.argidx < args.size(); opt.argidx++) {
		if (args[opt.argidx] == "-timeout") {
			opt.timeout = true;
			if (args.size() <= opt.argidx + 1)
				log_cmd_error("timeout not specified.\n");
			else
				opt.timeout_sec = atol(args[++opt.argidx].c_str());
			continue;
		}
		else if (args[opt.argidx] == "-nocleanup") {
			opt.nocleanup = true;
			continue;
		}
		else if (args[opt.argidx] == "-specialize") {
			opt.specialize = true;
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
		log("This command solves a 2QBF-SAT problem defined over the currently selected module.\n");
		log("Existentially-quantified variables are declared by assigning a wire \"$anyconst\".\n");
		log("Universally-quantified variables may be explicitly declared by assigning a wire\n");
		log("\"$allconst\", but module inputs will be treated as universally-quantified variables\n");
		log("by default.\n");
		log("\n");
		log("    -timeout <seconds>\n");
		log("        Set the solver timeout to the specified number of seconds.\n");
		log("\n");
		log("    -nocleanup\n");
		log("        Do not delete temporary files and directories.  Useful for\n");
		log("        debugging.\n");
		log("\n");
		log("    -dump-final-smt2 <file>\n");
		log("        Pass the --dump-smt2 option to yosys-smtbmc.\n");
		log("\n");
		log("    -specialize\n");
		log("        Replace all \"$anyconst\" cells with constant values determined by the solver.\n");
		log("\n");
		log("    -specialize-from-file <solution file>\n");
		log("        Do not run the solver, but instead only attempt to replace all \"$anyconst\"\n");
		log("        cells in the current module with values provided by the specified file.\n");
		log("\n");
		log("    -write-solution <solution file>\n");
		log("        Write the assignments discovered by the solver for all \"$anyconst\" cells\n");
		log("        to the specified file.");
		log("\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing QBF-SAT pass (solving QBF-SAT problems in the circuit).\n");
		QbfSolveOptions opt = parse_args(args);
		extra_args(args, opt.argidx, design);


		RTLIL::Module *module = NULL;
		for (auto mod : design->selected_modules()) {
			if (module)
				log_cmd_error("Only one module must be selected for the QBF-SAT pass! (selected: %s and %s)\n", log_id(module), log_id(mod));
			module = mod;
		}
		if (module == NULL)
			log_cmd_error("Can't perform QBF-SAT on an empty selection!\n");

		//Save the design to restore after modiyfing the current module.
		std::string module_name = module->name.str();
		Pass::call(design, "design -save _qbfsat_tmp");

		//Replace input wires with wires assigned $allconst cells.
		std::set<std::string> input_wires = validate_design_and_get_inputs(module);
		allconstify_inputs(module, input_wires);

		QbfSolutionType ret = qbf_solve(module, opt);
		Pass::call(design, "design -load _qbfsat_tmp");
		module = design->module(module_name);

		if (ret.unknown)
			log_warning("solver did not give an answer\n");
		else if (ret.sat)
			print_qed();
		else
			print_proof_failed();

		if (opt.specialize) {
			specialize(module, ret);
			Pass::call(design, "opt_clean");
		}
	}
} QbfSatPass;

PRIVATE_NAMESPACE_END
