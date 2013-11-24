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
 *  ---
 *
 *  A very simple and straightforward backend for the RTLIL text
 *  representation (as understood by the 'ilang' frontend).
 *
 */

#include "ilang_backend.h"
#include "kernel/register.h"
#include "kernel/log.h"
#include <string>
#include <assert.h>
#include <string.h>
#include <errno.h>

using namespace ILANG_BACKEND;

void ILANG_BACKEND::dump_const(FILE *f, const RTLIL::Const &data, int width, int offset, bool autoint)
{
	if (width < 0)
		width = data.bits.size() - offset;
	if (data.str.empty() || width != (int)data.bits.size()) {
		if (width == 32 && autoint) {
			int32_t val = 0;
			for (int i = 0; i < width; i++) {
				assert(offset+i < (int)data.bits.size());
				switch (data.bits[offset+i]) {
				case RTLIL::S0: break;
				case RTLIL::S1: val |= 1 << i; break;
				default: val = -1; break;
				}
			}
			if (val >= 0) {
				fprintf(f, "%d", val);
				return;
			}
		}
		fprintf(f, "%d'", width);
		for (int i = offset+width-1; i >= offset; i--) {
			assert(i < (int)data.bits.size());
			switch (data.bits[i]) {
			case RTLIL::S0: fprintf(f, "0"); break;
			case RTLIL::S1: fprintf(f, "1"); break;
			case RTLIL::Sx: fprintf(f, "x"); break;
			case RTLIL::Sz: fprintf(f, "z"); break;
			case RTLIL::Sa: fprintf(f, "-"); break;
			case RTLIL::Sm: fprintf(f, "m"); break;
			}
		}
	} else {
		fprintf(f, "\"");
		for (size_t i = 0; i < data.str.size(); i++) {
			if (data.str[i] == '\n')
				fprintf(f, "\\n");
			else if (data.str[i] == '\t')
				fprintf(f, "\\t");
			else if (data.str[i] < 32)
				fprintf(f, "\\%03o", data.str[i]);
			else if (data.str[i] == '"')
				fprintf(f, "\\\"");
			else
				fputc(data.str[i], f);
		}
		fprintf(f, "\"");
	}
}

void ILANG_BACKEND::dump_sigchunk(FILE *f, const RTLIL::SigChunk &chunk, bool autoint)
{
	if (chunk.wire == NULL) {
		dump_const(f, chunk.data, chunk.width, chunk.offset, autoint);
	} else {
		if (chunk.width == chunk.wire->width && chunk.offset == 0)
			fprintf(f, "%s", chunk.wire->name.c_str());
		else if (chunk.width == 1)
			fprintf(f, "%s [%d]", chunk.wire->name.c_str(), chunk.offset);
		else
			fprintf(f, "%s [%d:%d]", chunk.wire->name.c_str(), chunk.offset+chunk.width-1, chunk.offset);
	}
}

void ILANG_BACKEND::dump_sigspec(FILE *f, const RTLIL::SigSpec &sig, bool autoint)
{
	if (sig.chunks.size() == 1) {
		dump_sigchunk(f, sig.chunks[0], autoint);
	} else {
		fprintf(f, "{ ");
		for (auto it = sig.chunks.rbegin(); it != sig.chunks.rend(); it++) {
			dump_sigchunk(f, *it, false);
			fprintf(f, " ");
		}
		fprintf(f, "}");
	}
}

void ILANG_BACKEND::dump_wire(FILE *f, std::string indent, const RTLIL::Wire *wire)
{
	for (auto it = wire->attributes.begin(); it != wire->attributes.end(); it++) {
		fprintf(f, "%s" "attribute %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		fprintf(f, "\n");
	}
	fprintf(f, "%s" "wire ", indent.c_str());
	if (wire->width != 1)
		fprintf(f, "width %d ", wire->width);
	if (wire->start_offset != 0)
		fprintf(f, "offset %d ", wire->start_offset);
	if (wire->port_input && !wire->port_output)
		fprintf(f, "input %d ", wire->port_id);
	if (!wire->port_input && wire->port_output)
		fprintf(f, "output %d ", wire->port_id);
	if (wire->port_input && wire->port_output)
		fprintf(f, "inout %d ", wire->port_id);
	fprintf(f, "%s\n", wire->name.c_str());
}

void ILANG_BACKEND::dump_memory(FILE *f, std::string indent, const RTLIL::Memory *memory)
{
	for (auto it = memory->attributes.begin(); it != memory->attributes.end(); it++) {
		fprintf(f, "%s" "attribute %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		fprintf(f, "\n");
	}
	fprintf(f, "%s" "memory ", indent.c_str());
	if (memory->width != 1)
		fprintf(f, "width %d ", memory->width);
	if (memory->size != 0)
		fprintf(f, "size %d ", memory->size);
	fprintf(f, "%s\n", memory->name.c_str());
}

void ILANG_BACKEND::dump_cell(FILE *f, std::string indent, const RTLIL::Cell *cell)
{
	for (auto it = cell->attributes.begin(); it != cell->attributes.end(); it++) {
		fprintf(f, "%s" "attribute %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		fprintf(f, "\n");
	}
	fprintf(f, "%s" "cell %s %s\n", indent.c_str(), cell->type.c_str(), cell->name.c_str());
	for (auto it = cell->parameters.begin(); it != cell->parameters.end(); it++) {
		fprintf(f, "%s  parameter %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		fprintf(f, "\n");
	}
	for (auto it = cell->connections.begin(); it != cell->connections.end(); it++) {
		fprintf(f, "%s  connect %s ", indent.c_str(), it->first.c_str());
		dump_sigspec(f, it->second);
		fprintf(f, "\n");
	}
	fprintf(f, "%s" "end\n", indent.c_str());
}

void ILANG_BACKEND::dump_proc_case_body(FILE *f, std::string indent, const RTLIL::CaseRule *cs)
{
	for (auto it = cs->actions.begin(); it != cs->actions.end(); it++)
	{
		fprintf(f, "%s" "assign ", indent.c_str());
		dump_sigspec(f, it->first);
		fprintf(f, " ");
		dump_sigspec(f, it->second);
		fprintf(f, "\n");
	}

	for (auto it = cs->switches.begin(); it != cs->switches.end(); it++)
		dump_proc_switch(f, indent, *it);
}

void ILANG_BACKEND::dump_proc_switch(FILE *f, std::string indent, const RTLIL::SwitchRule *sw)
{
	for (auto it = sw->attributes.begin(); it != sw->attributes.end(); it++) {
		fprintf(f, "%s" "attribute %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		fprintf(f, "\n");
	}

	fprintf(f, "%s" "switch ", indent.c_str());
	dump_sigspec(f, sw->signal);
	fprintf(f, "\n");

	for (auto it = sw->cases.begin(); it != sw->cases.end(); it++)
	{
		fprintf(f, "%s  case ", indent.c_str());
		for (size_t i = 0; i < (*it)->compare.size(); i++) {
			if (i > 0)
				fprintf(f, ", ");
			dump_sigspec(f, (*it)->compare[i]);
		}
		fprintf(f, "\n");

		dump_proc_case_body(f, indent + "    ", *it);
	}

	fprintf(f, "%s" "end\n", indent.c_str());
}

void ILANG_BACKEND::dump_proc_sync(FILE *f, std::string indent, const RTLIL::SyncRule *sy)
{
	fprintf(f, "%s" "sync ", indent.c_str());
	switch (sy->type) {
	if (0) case RTLIL::ST0: fprintf(f, "low ");
	if (0) case RTLIL::ST1: fprintf(f, "high ");
	if (0) case RTLIL::STp: fprintf(f, "posedge ");
	if (0) case RTLIL::STn: fprintf(f, "negedge ");
	if (0) case RTLIL::STe: fprintf(f, "edge ");
		dump_sigspec(f, sy->signal);
		fprintf(f, "\n");
		break;
	case RTLIL::STa: fprintf(f, "always\n"); break;
	case RTLIL::STi: fprintf(f, "init\n"); break;
	}

	for (auto it = sy->actions.begin(); it != sy->actions.end(); it++) {
		fprintf(f, "%s  update ", indent.c_str());
		dump_sigspec(f, it->first);
		fprintf(f, " ");
		dump_sigspec(f, it->second);
		fprintf(f, "\n");
	}
}

void ILANG_BACKEND::dump_proc(FILE *f, std::string indent, const RTLIL::Process *proc)
{
	for (auto it = proc->attributes.begin(); it != proc->attributes.end(); it++) {
		fprintf(f, "%s" "attribute %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		fprintf(f, "\n");
	}
	fprintf(f, "%s" "process %s\n", indent.c_str(), proc->name.c_str());
	dump_proc_case_body(f, indent + "  ", &proc->root_case);
	for (auto it = proc->syncs.begin(); it != proc->syncs.end(); it++)
		dump_proc_sync(f, indent + "  ", *it);
	fprintf(f, "%s" "end\n", indent.c_str());
}

void ILANG_BACKEND::dump_conn(FILE *f, std::string indent, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right)
{
	fprintf(f, "%s" "connect ", indent.c_str());
	dump_sigspec(f, left);
	fprintf(f, " ");
	dump_sigspec(f, right);
	fprintf(f, "\n");
}

void ILANG_BACKEND::dump_module(FILE *f, std::string indent, const RTLIL::Module *module, const RTLIL::Design *design, bool only_selected)
{
	for (auto it = module->attributes.begin(); it != module->attributes.end(); it++) {
		fprintf(f, "%s" "attribute %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		fprintf(f, "\n");
	}

	fprintf(f, "%s" "module %s\n", indent.c_str(), module->name.c_str());

	for (auto it = module->wires.begin(); it != module->wires.end(); it++)
		if (!only_selected || design->selected(module, it->second)) {
			if (only_selected)
				fprintf(f, "\n");
			dump_wire(f, indent + "  ", it->second);
		}

	for (auto it = module->memories.begin(); it != module->memories.end(); it++)
		if (!only_selected || design->selected(module, it->second)) {
			if (only_selected)
				fprintf(f, "\n");
			dump_memory(f, indent + "  ", it->second);
		}

	for (auto it = module->cells.begin(); it != module->cells.end(); it++)
		if (!only_selected || design->selected(module, it->second)) {
			if (only_selected)
				fprintf(f, "\n");
			dump_cell(f, indent + "  ", it->second);
		}

	for (auto it = module->processes.begin(); it != module->processes.end(); it++)
		if (!only_selected || design->selected(module, it->second)) {
			if (only_selected)
				fprintf(f, "\n");
			dump_proc(f, indent + "  ", it->second);
		}

	bool first_conn_line = true;
	for (auto it = module->connections.begin(); it != module->connections.end(); it++) {
		bool show_conn = !only_selected;
		if (only_selected) {
			RTLIL::SigSpec sigs = it->first;
			sigs.append(it->second);
			for (auto &c : sigs.chunks) {
				if (c.wire == NULL || !design->selected(module, c.wire))
					continue;
				show_conn = true;
			}
		}
		if (show_conn) {
			if (only_selected && first_conn_line)
				fprintf(f, "\n");
			dump_conn(f, indent + "  ", it->first, it->second);
			first_conn_line = false;
		}
	}

	fprintf(f, "%s" "end\n", indent.c_str());
}

void ILANG_BACKEND::dump_design(FILE *f, const RTLIL::Design *design, bool only_selected)
{
	for (auto it = design->modules.begin(); it != design->modules.end(); it++) {
		if (!only_selected || design->selected(it->second)) {
			if (only_selected)
				fprintf(f, "\n");
			dump_module(f, "", it->second, design, only_selected);
		}
	}
}

struct IlangBackend : public Backend {
	IlangBackend() : Backend("ilang", "write design to ilang file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_ilang [filename]\n");
		log("\n");
		log("Write the current design to an 'ilang' file. (ilang is a text representation\n");
		log("of a design in yosys's internal format.)\n");
		log("\n");
		log("    -selected\n");
		log("        only write selected parts of the design.\n");
		log("\n");
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		bool selected = false;

		log_header("Executing ILANG backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-selected") {
				selected = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		log("Output filename: %s\n", filename.c_str());
		fprintf(f, "# Generated by %s\n", yosys_version_str);
		ILANG_BACKEND::dump_design(f, design, selected);
	}
} IlangBackend;

struct DumpPass : public Pass {
	DumpPass() : Pass("dump", "print parts of the design in ilang format") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dump [options] [selection]\n");
		log("\n");
		log("Write the selected parts of the design to the console or specified file in\n");
		log("ilang format.\n");
		log("\n");
		log("    -outfile <filename>\n");
		log("        Write to the specified file.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string filename;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-outfile" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		FILE *f = NULL;
		char *buf_ptr;
		size_t buf_size;

		if (!filename.empty()) {
			f = fopen(filename.c_str(), "w");
			if (f == NULL)
				log_error("Can't open file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
		} else {
			f = open_memstream(&buf_ptr, &buf_size);
		}

		ILANG_BACKEND::dump_design(f, design, true);

		fclose(f);

		if (filename.empty()) {
			log("%s", buf_ptr);
			free(buf_ptr);
		}
	}
} DumpPass;
 
