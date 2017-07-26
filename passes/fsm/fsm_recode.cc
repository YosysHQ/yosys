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
#include <math.h>
#include <string.h>
#include <errno.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void fm_set_fsm_print(RTLIL::Cell *cell, RTLIL::Module *module, FsmData &fsm_data, const char *prefix, FILE *f)
{
	std::string name = cell->parameters["\\NAME"].decode_string();

	fprintf(f, "set_fsm_state_vector {");
	for (int i = fsm_data.state_bits-1; i >= 0; i--)
		fprintf(f, " %s_reg[%d]", name[0] == '\\' ?  name.substr(1).c_str() : name.c_str(), i);
	fprintf(f, " } -name {%s_%s} {%s:/WORK/%s}\n", prefix, RTLIL::unescape_id(name).c_str(),
			prefix, RTLIL::unescape_id(module->name).c_str());

	fprintf(f, "set_fsm_encoding {");
	for (int i = 0; i < GetSize(fsm_data.state_table); i++) {
		fprintf(f, " s%d=2#", i);
		for (int j = GetSize(fsm_data.state_table[i].bits)-1; j >= 0; j--)
			fprintf(f, "%c", fsm_data.state_table[i].bits[j] == RTLIL::State::S1 ? '1' : '0');
	}
	fprintf(f, " } -name {%s_%s} {%s:/WORK/%s}\n",
			prefix, RTLIL::unescape_id(name).c_str(),
			prefix, RTLIL::unescape_id(module->name).c_str());
}

static void fsm_recode(RTLIL::Cell *cell, RTLIL::Module *module, FILE *fm_set_fsm_file, FILE *encfile, std::string default_encoding)
{
	std::string encoding = cell->attributes.count("\\fsm_encoding") ? cell->attributes.at("\\fsm_encoding").decode_string() : "auto";

	log("Recoding FSM `%s' from module `%s' using `%s' encoding:\n", cell->name.c_str(), module->name.c_str(), encoding.c_str());

	if (encoding != "none" && encoding != "user" && encoding != "one-hot" && encoding != "binary" && encoding != "auto") {
		log("  unknown encoding `%s': using auto instead.\n", encoding.c_str());
		encoding = "auto";
	}

	if (encoding == "none" || encoding == "user") {
		log("  nothing to do for encoding `%s'.\n", encoding.c_str());
		return;
	}

	FsmData fsm_data;
	fsm_data.copy_from_cell(cell);

	if (fm_set_fsm_file != NULL)
		fm_set_fsm_print(cell, module, fsm_data, "r", fm_set_fsm_file);

	if (encoding == "auto") {
		if (!default_encoding.empty())
			encoding = default_encoding;
		else
			encoding = GetSize(fsm_data.state_table) < 32 ? "one-hot" : "binary";
		log("  mapping auto encoding to `%s` for this FSM.\n", encoding.c_str());
	}

	if (encoding == "one-hot") {
		fsm_data.state_bits = fsm_data.state_table.size();
	} else
	if (encoding == "binary") {
		int new_num_state_bits = ceil_log2(fsm_data.state_table.size());
		if (fsm_data.state_bits == new_num_state_bits) {
			log("  existing encoding is already a packed binary encoding.\n");
			return;
		}
		fsm_data.state_bits = new_num_state_bits;
	} else
		log_error("FSM encoding `%s' is not supported!\n", encoding.c_str());

	if (encfile)
		fprintf(encfile, ".fsm %s %s\n", log_id(module), RTLIL::unescape_id(cell->parameters["\\NAME"].decode_string()).c_str());

	int state_idx_counter = fsm_data.reset_state >= 0 ? 1 : 0;
	for (int i = 0; i < int(fsm_data.state_table.size()); i++)
	{
		int state_idx = fsm_data.reset_state == i ? 0 : state_idx_counter++;
		RTLIL::Const new_code;

		if (encoding == "one-hot") {
			new_code = RTLIL::Const(RTLIL::State::Sa, fsm_data.state_bits);
			new_code.bits[state_idx] = RTLIL::State::S1;
		} else
		if (encoding == "binary") {
			new_code = RTLIL::Const(state_idx, fsm_data.state_bits);
		} else
			log_abort();

		log("  %s -> %s\n", fsm_data.state_table[i].as_string().c_str(), new_code.as_string().c_str());
		if (encfile)
			fprintf(encfile, ".map %s %s\n", fsm_data.state_table[i].as_string().c_str(), new_code.as_string().c_str());
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
		log("    fsm_recode [options] [selection]\n");
		log("\n");
		log("This pass reassign the state encodings for FSM cells. At the moment only\n");
		log("one-hot encoding and binary encoding is supported.\n");

		log("    -encoding <type>\n");
		log("        specify the encoding scheme used for FSMs without the\n");
		log("        'fsm_encoding' attribute or with the attribute set to `auto'.\n");
		log("\n");
		log("    -fm_set_fsm_file <file>\n");
		log("        generate a file containing the mapping from old to new FSM encoding\n");
		log("        in form of Synopsys Formality set_fsm_* commands.\n");
		log("\n");
		log("    -encfile <file>\n");
		log("        write the mappings from old to new FSM encoding to a file in the\n");
		log("        following format:\n");
		log("\n");
		log("            .fsm <module_name> <state_signal>\n");
		log("            .map <old_bitpattern> <new_bitpattern>\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		FILE *fm_set_fsm_file = NULL;
		FILE *encfile = NULL;
		std::string default_encoding;

		log_header(design, "Executing FSM_RECODE pass (re-assigning FSM state encoding).\n");
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-fm_set_fsm_file" && argidx+1 < args.size() && fm_set_fsm_file == NULL) {
				fm_set_fsm_file = fopen(args[++argidx].c_str(), "w");
				if (fm_set_fsm_file == NULL)
					log_error("Can't open fm_set_fsm_file `%s' for writing: %s\n", args[argidx].c_str(), strerror(errno));
				continue;
			}
			if (arg == "-encfile" && argidx+1 < args.size() && encfile == NULL) {
				encfile = fopen(args[++argidx].c_str(), "w");
				if (encfile == NULL)
					log_error("Can't open encfile `%s' for writing: %s\n", args[argidx].c_str(), strerror(errno));
				continue;
			}
			if (arg == "-encoding" && argidx+1 < args.size() && default_encoding.empty()) {
				default_encoding = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules_)
			if (design->selected(mod_it.second))
				for (auto &cell_it : mod_it.second->cells_)
					if (cell_it.second->type == "$fsm" && design->selected(mod_it.second, cell_it.second))
						fsm_recode(cell_it.second, mod_it.second, fm_set_fsm_file, encfile, default_encoding);

		if (fm_set_fsm_file != NULL)
			fclose(fm_set_fsm_file);
		if (encfile != NULL)
			fclose(encfile);
	}
} FsmRecodePass;

PRIVATE_NAMESPACE_END
