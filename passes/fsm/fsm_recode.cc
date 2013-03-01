/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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
#include <string.h>

static void fm_set_fsm_print(RTLIL::Cell *cell, RTLIL::Module *module, FsmData &fsm_data, const char *prefix, FILE *f)
{
	fprintf(f, "set_fsm_state_vector {");
	for (int i = fsm_data.state_bits-1; i >= 0; i--)
		fprintf(f, " %s_reg[%d]", cell->parameters["\\NAME"].str[0] == '\\' ?
				cell->parameters["\\NAME"].str.substr(1).c_str() : cell->parameters["\\NAME"].str.c_str(), i);
	fprintf(f, " } -name {%s_%s} {%s:/WORK/%s}\n",
			prefix, RTLIL::unescape_id(cell->parameters["\\NAME"].str).c_str(),
			prefix, RTLIL::unescape_id(module->name).c_str());

	fprintf(f, "set_fsm_encoding {");
	for (size_t i = 0; i < fsm_data.state_table.size(); i++) {
		fprintf(f, " s%zd=2#", i);
		for (int j = int(fsm_data.state_table[i].bits.size())-1; j >= 0; j--)
			fprintf(f, "%c", fsm_data.state_table[i].bits[j] == RTLIL::State::S1 ? '1' : '0');
	}
	fprintf(f, " } -name {%s_%s} {%s:/WORK/%s}\n",
			prefix, RTLIL::unescape_id(cell->parameters["\\NAME"].str).c_str(),
			prefix, RTLIL::unescape_id(module->name).c_str());
}

static void fsm_recode(RTLIL::Cell *cell, RTLIL::Module *module, FILE *fm_set_fsm_file)
{
	FsmData fsm_data;
	fsm_data.copy_from_cell(cell);

	log("Recoding FSM `%s' from module `%s':\n", cell->name.c_str(), module->name.c_str());

	if (fm_set_fsm_file != NULL)
		fm_set_fsm_print(cell, module, fsm_data, "r", fm_set_fsm_file);

	fsm_data.state_bits = fsm_data.state_table.size();
	if (fsm_data.reset_state >= 0)
		fsm_data.state_bits--;

	int bit_pos = 0;
	for (size_t i = 0; i < fsm_data.state_table.size(); i++)
	{
		RTLIL::Const new_code;
		if (int(i) == fsm_data.reset_state)
			new_code = RTLIL::Const(RTLIL::State::S0, fsm_data.state_bits);
		else {
			RTLIL::Const state_code(RTLIL::State::Sa, fsm_data.state_bits);
			state_code.bits[bit_pos++] = RTLIL::State::S1;
			new_code = state_code;
		}

		log("  %s -> %s\n", fsm_data.state_table[i].as_string().c_str(), new_code.as_string().c_str());
		fsm_data.state_table[i] = new_code;
	}

	if (fm_set_fsm_file != NULL)
		fm_set_fsm_print(cell, module, fsm_data, "i", fm_set_fsm_file);

	fsm_data.copy_to_cell(cell);
}

struct FsmRecodePass : public Pass {
	FsmRecodePass() : Pass("fsm_recode", "recoding finite state machines") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm_recode [-fm_set_fsm_file file] [selection]\n");
		log("\n");
		log("This pass reassign the state encodings for FSM cells. At the moment only\n");
		log("one-hot encoding is supported.\n");
		log("\n");
		log("The option -fm_set_fsm_file can be used to generate a file containing the\n");
		log("mapping from old to new FSM encoding in form of Synopsys Formality set_fsm_*\n");
		log("commands.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		FILE *fm_set_fsm_file = NULL;

		log_header("Executing FSM_RECODE pass (re-assigning FSM state encoding).\n");
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-fm_set_fsm_file" && argidx+1 < args.size() && fm_set_fsm_file == NULL) {
				fm_set_fsm_file = fopen(args[++argidx].c_str(), "w");
				if (fm_set_fsm_file == NULL)
					log_error("Can't open fm_set_fsm_file `%s' for writing: %s\n", args[argidx].c_str(), strerror(errno));
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules)
			if (design->selected(mod_it.second))
				for (auto &cell_it : mod_it.second->cells)
					if (cell_it.second->type == "$fsm" && design->selected(mod_it.second, cell_it.second))
						fsm_recode(cell_it.second, mod_it.second, fm_set_fsm_file);

		if (fm_set_fsm_file != NULL)
			fclose(fm_set_fsm_file);
	}
} FsmRecodePass;
 
