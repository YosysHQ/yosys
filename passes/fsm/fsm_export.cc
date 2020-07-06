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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

/**
 * Convert a signal into a KISS-compatible textual representation.
 */
std::string kiss_convert_signal(const RTLIL::SigSpec &sig) {
	log_assert(sig.is_fully_const());
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
void write_kiss2(struct RTLIL::Module *module, struct RTLIL::Cell *cell, std::string filename, bool origenc) {
	dict<RTLIL::IdString, RTLIL::Const>::iterator attr_it;
	FsmData fsm_data;
	FsmData::transition_t tr;
	std::ofstream kiss_file;
	std::string kiss_name;
	size_t i;

	attr_it = cell->attributes.find("\\fsm_export");
	if (!filename.empty()) {
		kiss_name.assign(filename);
	} else if (attr_it != cell->attributes.end() && attr_it->second.decode_string() != "") {
		kiss_name.assign(attr_it->second.decode_string());
	}
	else {
		kiss_name.assign(log_id(module) + std::string("-") + log_id(cell) + ".kiss2");
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
	if (origenc) {
		kiss_file << ".r " << kiss_convert_signal(fsm_data.state_table[fsm_data.reset_state]) << std::endl;
	} else {
		kiss_file << ".r s" << std::dec << fsm_data.reset_state << std::endl;
	}

	for (i = 0; i < fsm_data.transition_table.size(); i++) {
		tr = fsm_data.transition_table[i];

		try {
			kiss_file << kiss_convert_signal(tr.ctrl_in) << ' ';
			if (origenc) {
				kiss_file << kiss_convert_signal(fsm_data.state_table[tr.state_in])  << ' ';
				kiss_file << kiss_convert_signal(fsm_data.state_table[tr.state_out]) << ' ';
			} else {
				kiss_file << 's' << tr.state_in << ' ';
				kiss_file << 's' << tr.state_out << ' ';
			}
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
	FsmExportPass() : Pass("fsm_export", "exporting FSMs to KISS2 files") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm_export [-noauto] [-o filename] [-origenc] [selection]\n");
		log("\n");
		log("This pass creates a KISS2 file for every selected FSM. For FSMs with the\n");
		log("'fsm_export' attribute set, the attribute value is used as filename, otherwise\n");
		log("the module and cell name is used as filename. If the parameter '-o' is given,\n");
		log("the first exported FSM is written to the specified filename. This overwrites\n");
		log("the setting as specified with the 'fsm_export' attribute. All other FSMs are\n");
		log("exported to the default name as mentioned above.\n");
		log("\n");
		log("    -noauto\n");
		log("        only export FSMs that have the 'fsm_export' attribute set\n");
		log("\n");
		log("    -o filename\n");
		log("        filename of the first exported FSM\n");
		log("\n");
		log("    -origenc\n");
		log("        use binary state encoding as state names instead of s0, s1, ...\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		dict<RTLIL::IdString, RTLIL::Const>::iterator attr_it;
		std::string arg;
		bool flag_noauto = false;
		std::string filename;
		bool flag_origenc = false;
		size_t argidx;

		log_header(design, "Executing FSM_EXPORT pass (exporting FSMs in KISS2 file format).\n");

		for (argidx = 1; argidx < args.size(); argidx++) {
			arg = args[argidx];
			if (arg == "-noauto") {
				flag_noauto = true;
				continue;
			}
			if (arg == "-o") {
				argidx++;
				filename = args[argidx];
				continue;
			}
			if (arg == "-origenc") {
				flag_origenc = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules_)
			if (design->selected(mod_it.second))
				for (auto &cell_it : mod_it.second->cells_)
					if (cell_it.second->type == "$fsm" && design->selected(mod_it.second, cell_it.second)) {
						attr_it = cell_it.second->attributes.find("\\fsm_export");
						if (!flag_noauto || (attr_it != cell_it.second->attributes.end())) {
							write_kiss2(mod_it.second, cell_it.second, filename, flag_origenc);
							filename.clear();
						}
					}
	}
} FsmExportPass;

PRIVATE_NAMESPACE_END
