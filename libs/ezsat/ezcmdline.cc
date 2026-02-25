
#include "ezcmdline.h"

#include "../../kernel/yosys.h"

ezCmdlineSAT::ezCmdlineSAT(const std::string &cmd) : command(cmd) {}

ezCmdlineSAT::~ezCmdlineSAT() {}

bool ezCmdlineSAT::solver(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions)
{
#if !defined(YOSYS_DISABLE_SPAWN)
	const std::string tempdir_name = Yosys::make_temp_dir(Yosys::get_base_tmpdir() + "/yosys-sat-XXXXXX");
	const std::string cnf_filename = Yosys::stringf("%s/problem.cnf", tempdir_name.c_str());
	const std::string sat_command = Yosys::stringf("%s %s", command.c_str(), cnf_filename.c_str());
	FILE *dimacs = fopen(cnf_filename.c_str(), "w");
	if (dimacs == nullptr) {
		Yosys::log_cmd_error("Failed to create CNF file `%s`.\n", cnf_filename.c_str());
	}

	std::vector<int> modelIdx;
	for (auto id : modelExpressions)
		modelIdx.push_back(bind(id));
	std::vector<std::vector<int>> extraClauses;
	for (auto id : assumptions)
		extraClauses.push_back({bind(id)});

	printDIMACS(dimacs, false, extraClauses);
	fclose(dimacs);

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
	int return_code = Yosys::run_command(sat_command, line_callback);
	if (return_code != 0 && return_code != 10 && return_code != 20) {
		Yosys::log_cmd_error("Shell command failed!\n");
	}

	modelValues.clear();
	modelValues.resize(modelIdx.size());

	if (!status_sat && !status_unsat) {
		solverTimeoutStatus = true;
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
#else
	Yosys::log_error("SAT solver command not available in this build!\n");
#endif
}
