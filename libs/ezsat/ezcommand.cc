
#include "ezcommand.h"

#include "../../kernel/yosys.h"

ezSATCommand::ezSATCommand(const std::string &cmd) : command(cmd) {}

ezSATCommand::~ezSATCommand() {}

bool ezSATCommand::solver(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions)
{
	if (!assumptions.empty()) {
		Yosys::log_error("Assumptions are not supported yet by command-based Sat solver\n");
	}
	const std::string tempdir_name = Yosys::make_temp_dir(Yosys::get_base_tmpdir() + "/yosys-sat-XXXXXX");
	const std::string cnf_filename = Yosys::stringf("%s/problem.cnf", tempdir_name.c_str());
	const std::string sat_command = Yosys::stringf("%s %s", command.c_str(), cnf_filename.c_str());
	FILE *dimacs = fopen(cnf_filename.c_str(), "w");
	printDIMACS(dimacs);
	fclose(dimacs);

	std::vector<int> modelIdx;
	for (auto id : modelExpressions)
		modelIdx.push_back(bind(id));

	bool status_sat = false;
	bool status_unsat = false;
	std::vector<bool> values;

	auto line_callback = [&](const std::string &line) {
		if (line.empty()) {
			return;
		}
		if (line[0] == 's') {
			if (line.substr(0, 5) == "s SAT") {
				status_sat = true;
			}
			if (line.substr(0, 7) == "s UNSAT") {
				status_unsat = true;
			}
			return;
		}
		if (line[0] == 'v') {
			std::stringstream ss(line.substr(1));
			int lit;
			while (ss >> lit) {
				if (lit == 0) {
					return;
				}
				bool val = lit >= 0;
				int ind = lit >= 0 ? lit - 1 : -lit - 1;
				if (Yosys::GetSize(values) <= ind) {
					values.resize(ind + 1);
				}
				values[ind] = val;
			}
		}
	};
	if (Yosys::run_command(sat_command, line_callback) != 0) {
		Yosys::log_cmd_error("Shell command failed!\n");
	}

	modelValues.clear();
	modelValues.resize(modelIdx.size());

	if (!status_sat && !status_unsat) {
		solverTimoutStatus = true;
	}
	if (!status_sat) {
		return false;
	}

	for (size_t i = 0; i < modelIdx.size(); i++) {
		int idx = modelIdx[i];
		bool refvalue = true;

		if (idx < 0)
			idx = -idx, refvalue = false;

		modelValues[i] = (values.at(idx - 1) == refvalue);
	}
	return true;
}