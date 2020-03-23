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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct QbfSolutionType {
	std::vector<std::string> stdout;
	bool sat;
	bool unknown; //true if neither 'sat' nor 'unsat'
	bool success; //true if exit code 0

	QbfSolutionType() : sat(false), unknown(true), success(false) {}
};

QbfSolutionType qbf_solve(RTLIL::Module *mod) {

	QbfSolutionType ret;

	//TODO: make temporary directory
	//TODO: call `prep`
	//TODO: call `write_smt2`
	//TODO: execute and capture stdout from `yosys-smtbmc`
	//TODO: remove temporary directory

	return ret;
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

void print_timeout()
{
	log("\n");
	log("        _____  _  _      _____ ____  _     _____\n");
	log("       /__ __\\/ \\/ \\__/|/  __//  _ \\/ \\ /\\/__ __\\\n");
	log("         / \\  | || |\\/|||  \\  | / \\|| | ||  / \\\n");
	log("         | |  | || |  |||  /_ | \\_/|| \\_/|  | |\n");
	log("         \\_/  \\_/\\_/  \\|\\____\\\\____/\\____/  \\_/\n");
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
		bool timeout = false, specialize = false, specialize_from_file = false, write_solution = false;
		long timeout_sec = -1;
		std::string specialize_soln_file;
		std::string write_soln_soln_file;

		log_header(design, "Executing QBF-SAT pass (solving QBF-SAT problems in the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-timeout") {
				timeout = true;
				if (args.size() <= argidx + 1)
					log_cmd_error("timeout not specified.\n");
				else
					timeout_sec = atol(args[++argidx].c_str());
				continue;
			}
			else if (args[argidx] == "-specialize") {
				specialize = true;
				continue;
			}
			else if (args[argidx] == "-specialize-from-file") {
				specialize_from_file = true;
				if (args.size() <= argidx + 1)
					log_cmd_error("solution file not specified.\n");
				else
					specialize_soln_file = args[++argidx];
				continue;
			}
			else if (args[argidx] == "-write-solution") {
				write_solution = true;
				if (args.size() <= argidx + 1)
					log_cmd_error("solution file not specified.\n");
				else
					write_soln_soln_file = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Module *module = NULL;
		for (auto mod : design->selected_modules()) {
			if (module)
				log_cmd_error("Only one module must be selected for the QBF-SAT pass! (selected: %s and %s)\n", log_id(module), log_id(mod));
			module = mod;
		}
		if (module == NULL)
			log_cmd_error("Can't perform QBF-SAT on an empty selection!\n");

		bool found_input = false;
		bool found_hole = false;
		bool found_1bit_output = false;
		for (auto wire : module->wires()) {
			if (wire->port_input)
				found_input = true;
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

		QbfSolutionType ret = qbf_solve(module);

		if (ret.unknown)
			log_warning("solver did not give an answer\n");
		else if (ret.sat)
			print_qed();
		else
			print_proof_failed();

		//TODO specialize etc.
	}
} QbfSatPass;

PRIVATE_NAMESPACE_END
