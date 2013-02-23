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
 * Convert a signal into a KISS-compatible textual representation.
 */
std::string kiss_convert_signal(const RTLIL::SigSpec &sig) {
	if (!sig.is_fully_const()) {
		throw 0;
	}

	return sig.as_const().as_string();
}

/**
 * Create a KISS2 file from a cell.
 *
 * The destination file name is taken from the fsm_export attribute if present,
 * e.g. (* fsm_export="filename.kiss2" *). If this attribute is not present,
 * the file name will be assembled from the module and cell names.
 *
 * @param module pointer to module which contains the FSM cell.
 * @param cell pointer to the FSM cell which should be exported.
 */
void write_kiss2(struct RTLIL::Module *module, struct RTLIL::Cell *cell) {
	std::map<RTLIL::IdString, RTLIL::Const>::iterator attr_it;
	FsmData fsm_data;
	FsmData::transition_t tr;
	std::ofstream kiss_file;
	std::string kiss_name;
	size_t i;

	attr_it = cell->attributes.find("\\fsm_export");
	if (attr_it != cell->attributes.end() && attr_it->second.str != "") {
		kiss_name.assign(attr_it->second.str);
	}
	else {
		kiss_name.assign(module->name);
		kiss_name.append('-' + cell->name + ".kiss2");
	}

	log("\n");
	log("Exporting FSM `%s' from module `%s' to file `%s'.\n",
			cell->name.c_str(),
			module->name.c_str(),
			kiss_name.c_str());

	kiss_file.open(kiss_name, std::ios::out | std::ios::trunc);

	if (!kiss_file.is_open()) {
		log_error("Could not open file \"%s\" with write access.\n", kiss_name.c_str());
	}

	fsm_data.copy_from_cell(cell);

	kiss_file << ".i "  << std::dec << fsm_data.num_inputs << std::endl;
	kiss_file << ".o "  << std::dec << fsm_data.num_outputs << std::endl;
	kiss_file << ".p "  << std::dec << fsm_data.transition_table.size() << std::endl;
	kiss_file << ".s "  << std::dec << fsm_data.state_table.size() << std::endl;
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
			kiss_file.close();
			log_error("exporting an FSM input or output signal failed.\n");
		}
	}

	kiss_file.close();
}

/**
 * Exports Finite State Machines in the design to one file per FSM. Currently,
 * only the KISS2 file format is supported.
 */
struct FsmExportPass : public Pass {
	FsmExportPass() : Pass("fsm_export") {
	}

	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::map<RTLIL::IdString, RTLIL::Const>::iterator attr_it;
		std::string arg;
		bool flag_noauto = false;
		size_t argidx;

		log_header("Executing FSM_EXPORT pass (exporting FSMs in KISS2 file format).\n");

		for (argidx = 1; argidx < args.size(); argidx++) {
			arg = args[argidx];
			if (arg == "-noauto") {
				flag_noauto = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules)
			for (auto &cell_it : mod_it.second->cells)
				if (cell_it.second->type == "$fsm") {
				  attr_it = cell_it.second->attributes.find("\\fsm_export");
				  if (!flag_noauto || (attr_it != cell_it.second->attributes.end())) {
				    write_kiss2(mod_it.second, cell_it.second);
				  }
				}
	}
} FsmExportPass;
