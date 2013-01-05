/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2012  Martin Schmölzer <martin@schmoelzer.at>
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

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/celltypes.h"
#include "fsmdata.h"
#include <string>
#include <iostream>
#include <fstream>

/**
 * Convert signal into a KISS-compatible textual representation.
 */
std::string kiss_convert_signal(const RTLIL::SigSpec &sig) {
	if (!sig.is_fully_const()) {
		throw 0;
	}

	return sig.as_const().as_string();
}

/**
 * Exports each Finite State Machine (FSM) in the design to a file in KISS2 format.
 */
struct FsmExportPass : public Pass {
	FsmExportPass() : Pass("fsm_export") {
	}

	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		FsmData       fsm_data;
		std::string   kiss_name;
		std::ofstream kiss_file;
		size_t        i;
		FsmData::transition_t tr;

		log_header("Executing FSM_EXPORT pass (exporting FSMs in KISS2 file format).\n");
		extra_args(args, 1, design);

		for (auto &mod_it : design->modules)
			for (auto &cell_it : mod_it.second->cells)
				if (cell_it.second->type == "$fsm") {
					kiss_name.assign(mod_it.first.c_str());
					kiss_name.append("-" + cell_it.second->name + ".kiss2");
					fsm_data.copy_from_cell(cell_it.second);

					log("\n");
					log("Exporting FSM `%s' from module `%s' to file `%s'.\n",
							cell_it.second->name.c_str(),
							mod_it.first.c_str(),
							kiss_name.c_str());

					kiss_file.open(kiss_name, std::ios::out | std::ios::trunc);

					if (!kiss_file.is_open()) {
						log_error("Could not open file \"%s\" with write access.\n", kiss_name.c_str());
						return;
					}

					kiss_file << ".start_kiss" << std::endl;
					kiss_file << ".i " << std::dec << fsm_data.num_inputs << std::endl;
					kiss_file << ".o " << std::dec << fsm_data.num_outputs << std::endl;
					kiss_file << ".r s" << std::dec << fsm_data.reset_state << std::endl;

					for (i = 0; i < fsm_data.transition_table.size(); i++) {
						tr = fsm_data.transition_table[i];

						try {
							kiss_file << kiss_convert_signal(tr.ctrl_in) << ' ';
							kiss_file << 's' << tr.state_in << ' ';
							kiss_file << 's' << tr.state_out << ' ';
							kiss_file << kiss_convert_signal(tr.ctrl_out) << std::endl;
						}
						catch (int) {
							log_error("exporting an FSM input or output signal failed.\n");
						}
					}

					kiss_file << ".end_kiss" << std::endl << ".end" << std::endl;
					kiss_file.close();
				}
	}
} FsmExportPass;
