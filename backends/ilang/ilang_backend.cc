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
#include "kernel/yosys.h"
#include <errno.h>

USING_YOSYS_NAMESPACE
using namespace ILANG_BACKEND;
YOSYS_NAMESPACE_BEGIN

void ILANG_BACKEND::dump_const(std::ostream &f, const RTLIL::Const &data, int width, int offset, bool autoint)
{
	if (width < 0)
		width = data.bits.size() - offset;
	if ((data.flags & RTLIL::CONST_FLAG_STRING) == 0 || width != (int)data.bits.size()) {
		if (width == 32 && autoint) {
			int32_t val = 0;
			for (int i = 0; i < width; i++) {
				log_assert(offset+i < (int)data.bits.size());
				switch (data.bits[offset+i]) {
				case State::S0: break;
				case State::S1: val |= 1 << i; break;
				default: val = -1; break;
				}
			}
			if (val >= 0) {
				f << stringf("%d", val);
				return;
			}
		}
		f << stringf("%d'", width);
		for (int i = offset+width-1; i >= offset; i--) {
			log_assert(i < (int)data.bits.size());
			switch (data.bits[i]) {
			case State::S0: f << stringf("0"); break;
			case State::S1: f << stringf("1"); break;
			case RTLIL::Sx: f << stringf("x"); break;
			case RTLIL::Sz: f << stringf("z"); break;
			case RTLIL::Sa: f << stringf("-"); break;
			case RTLIL::Sm: f << stringf("m"); break;
			}
		}
	} else {
		f << stringf("\"");
		std::string str = data.decode_string();
		for (size_t i = 0; i < str.size(); i++) {
			if (str[i] == '\n')
				f << stringf("\\n");
			else if (str[i] == '\t')
				f << stringf("\\t");
			else if (str[i] < 32)
				f << stringf("\\%03o", str[i]);
			else if (str[i] == '"')
				f << stringf("\\\"");
			else if (str[i] == '\\')
				f << stringf("\\\\");
			else
				f << str[i];
		}
		f << stringf("\"");
	}
}

void ILANG_BACKEND::dump_sigchunk(std::ostream &f, const RTLIL::SigChunk &chunk, bool autoint)
{
	if (chunk.wire == NULL) {
		dump_const(f, chunk.data, chunk.width, chunk.offset, autoint);
	} else {
		if (chunk.width == chunk.wire->width && chunk.offset == 0)
			f << stringf("%s", chunk.wire->name.c_str());
		else if (chunk.width == 1)
			f << stringf("%s [%d]", chunk.wire->name.c_str(), chunk.offset);
		else
			f << stringf("%s [%d:%d]", chunk.wire->name.c_str(), chunk.offset+chunk.width-1, chunk.offset);
	}
}

void ILANG_BACKEND::dump_sigspec(std::ostream &f, const RTLIL::SigSpec &sig, bool autoint)
{
	if (sig.is_chunk()) {
		dump_sigchunk(f, sig.as_chunk(), autoint);
	} else {
		f << stringf("{ ");
		for (auto it = sig.chunks().rbegin(); it != sig.chunks().rend(); ++it) {
			dump_sigchunk(f, *it, false);
			f << stringf(" ");
		}
		f << stringf("}");
	}
}

void ILANG_BACKEND::dump_wire(std::ostream &f, std::string indent, const RTLIL::Wire *wire)
{
	for (auto &it : wire->attributes) {
		f << stringf("%s" "attribute %s ", indent.c_str(), it.first.c_str());
		dump_const(f, it.second);
		f << stringf("\n");
	}
	f << stringf("%s" "wire ", indent.c_str());
	if (wire->width != 1)
		f << stringf("width %d ", wire->width);
	if (wire->upto)
		f << stringf("upto ");
	if (wire->start_offset != 0)
		f << stringf("offset %d ", wire->start_offset);
	if (wire->port_input && !wire->port_output)
		f << stringf("input %d ", wire->port_id);
	if (!wire->port_input && wire->port_output)
		f << stringf("output %d ", wire->port_id);
	if (wire->port_input && wire->port_output)
		f << stringf("inout %d ", wire->port_id);
	f << stringf("%s\n", wire->name.c_str());
}

void ILANG_BACKEND::dump_memory(std::ostream &f, std::string indent, const RTLIL::Memory *memory)
{
	for (auto &it : memory->attributes) {
		f << stringf("%s" "attribute %s ", indent.c_str(), it.first.c_str());
		dump_const(f, it.second);
		f << stringf("\n");
	}
	f << stringf("%s" "memory ", indent.c_str());
	if (memory->width != 1)
		f << stringf("width %d ", memory->width);
	if (memory->size != 0)
		f << stringf("size %d ", memory->size);
	if (memory->start_offset != 0)
		f << stringf("offset %d ", memory->start_offset);
	f << stringf("%s\n", memory->name.c_str());
}

void ILANG_BACKEND::dump_cell(std::ostream &f, std::string indent, const RTLIL::Cell *cell)
{
	for (auto &it : cell->attributes) {
		f << stringf("%s" "attribute %s ", indent.c_str(), it.first.c_str());
		dump_const(f, it.second);
		f << stringf("\n");
	}
	f << stringf("%s" "cell %s %s\n", indent.c_str(), cell->type.c_str(), cell->name.c_str());
	for (auto &it : cell->parameters) {
		f << stringf("%s  parameter%s%s %s ", indent.c_str(),
				(it.second.flags & RTLIL::CONST_FLAG_SIGNED) != 0 ? " signed" : "",
				(it.second.flags & RTLIL::CONST_FLAG_REAL) != 0 ? " real" : "",
				it.first.c_str());
		dump_const(f, it.second);
		f << stringf("\n");
	}
	for (auto &it : cell->connections()) {
		f << stringf("%s  connect %s ", indent.c_str(), it.first.c_str());
		dump_sigspec(f, it.second);
		f << stringf("\n");
	}
	f << stringf("%s" "end\n", indent.c_str());
}

void ILANG_BACKEND::dump_proc_case_body(std::ostream &f, std::string indent, const RTLIL::CaseRule *cs)
{
	for (auto it = cs->actions.begin(); it != cs->actions.end(); ++it)
	{
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, it->first);
		f << stringf(" ");
		dump_sigspec(f, it->second);
		f << stringf("\n");
	}

	for (auto it = cs->switches.begin(); it != cs->switches.end(); ++it)
		dump_proc_switch(f, indent, *it);
}

void ILANG_BACKEND::dump_proc_switch(std::ostream &f, std::string indent, const RTLIL::SwitchRule *sw)
{
	for (auto it = sw->attributes.begin(); it != sw->attributes.end(); ++it) {
		f << stringf("%s" "attribute %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		f << stringf("\n");
	}

	f << stringf("%s" "switch ", indent.c_str());
	dump_sigspec(f, sw->signal);
	f << stringf("\n");

	for (auto it = sw->cases.begin(); it != sw->cases.end(); ++it)
	{
		for (auto ait = (*it)->attributes.begin(); ait != (*it)->attributes.end(); ++ait) {
			f << stringf("%s  attribute %s ", indent.c_str(), ait->first.c_str());
			dump_const(f, ait->second);
			f << stringf("\n");
		}
		f << stringf("%s  case ", indent.c_str());
		for (size_t i = 0; i < (*it)->compare.size(); i++) {
			if (i > 0)
				f << stringf(" , ");
			dump_sigspec(f, (*it)->compare[i]);
		}
		f << stringf("\n");

		dump_proc_case_body(f, indent + "    ", *it);
	}

	f << stringf("%s" "end\n", indent.c_str());
}

void ILANG_BACKEND::dump_proc_sync(std::ostream &f, std::string indent, const RTLIL::SyncRule *sy)
{
	f << stringf("%s" "sync ", indent.c_str());
	switch (sy->type) {
	case RTLIL::ST0: f << stringf("low ");
	if (0) case RTLIL::ST1: f << stringf("high ");
	if (0) case RTLIL::STp: f << stringf("posedge ");
	if (0) case RTLIL::STn: f << stringf("negedge ");
	if (0) case RTLIL::STe: f << stringf("edge ");
		dump_sigspec(f, sy->signal);
		f << stringf("\n");
		break;
	case RTLIL::STa: f << stringf("always\n"); break;
	case RTLIL::STg: f << stringf("global\n"); break;
	case RTLIL::STi: f << stringf("init\n"); break;
	}

	for (auto it = sy->actions.begin(); it != sy->actions.end(); ++it) {
		f << stringf("%s  update ", indent.c_str());
		dump_sigspec(f, it->first);
		f << stringf(" ");
		dump_sigspec(f, it->second);
		f << stringf("\n");
	}
}

void ILANG_BACKEND::dump_proc(std::ostream &f, std::string indent, const RTLIL::Process *proc)
{
	for (auto it = proc->attributes.begin(); it != proc->attributes.end(); ++it) {
		f << stringf("%s" "attribute %s ", indent.c_str(), it->first.c_str());
		dump_const(f, it->second);
		f << stringf("\n");
	}
	f << stringf("%s" "process %s\n", indent.c_str(), proc->name.c_str());
	dump_proc_case_body(f, indent + "  ", &proc->root_case);
	for (auto it = proc->syncs.begin(); it != proc->syncs.end(); ++it)
		dump_proc_sync(f, indent + "  ", *it);
	f << stringf("%s" "end\n", indent.c_str());
}

void ILANG_BACKEND::dump_conn(std::ostream &f, std::string indent, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right)
{
	f << stringf("%s" "connect ", indent.c_str());
	dump_sigspec(f, left);
	f << stringf(" ");
	dump_sigspec(f, right);
	f << stringf("\n");
}

void ILANG_BACKEND::dump_module(std::ostream &f, std::string indent, RTLIL::Module *module, RTLIL::Design *design, bool only_selected, bool flag_m, bool flag_n)
{
	bool print_header = flag_m || design->selected_whole_module(module->name);
	bool print_body = !flag_n || !design->selected_whole_module(module->name);

	if (print_header)
	{
		for (auto it = module->attributes.begin(); it != module->attributes.end(); ++it) {
			f << stringf("%s" "attribute %s ", indent.c_str(), it->first.c_str());
			dump_const(f, it->second);
			f << stringf("\n");
		}

		f << stringf("%s" "module %s\n", indent.c_str(), module->name.c_str());

		if (!module->avail_parameters.empty()) {
			if (only_selected)
				f << stringf("\n");
			for (auto &p : module->avail_parameters)
				f << stringf("%s" "  parameter %s\n", indent.c_str(), p.c_str());
		}
	}

	if (print_body)
	{
		for (auto it : module->wires())
			if (!only_selected || design->selected(module, it)) {
				if (only_selected)
					f << stringf("\n");
				dump_wire(f, indent + "  ", it);
			}

		for (auto it : module->memories)
			if (!only_selected || design->selected(module, it.second)) {
				if (only_selected)
					f << stringf("\n");
				dump_memory(f, indent + "  ", it.second);
			}

		for (auto it : module->cells())
			if (!only_selected || design->selected(module, it)) {
				if (only_selected)
					f << stringf("\n");
				dump_cell(f, indent + "  ", it);
			}

		for (auto it : module->processes)
			if (!only_selected || design->selected(module, it.second)) {
				if (only_selected)
					f << stringf("\n");
				dump_proc(f, indent + "  ", it.second);
			}

		bool first_conn_line = true;
		for (auto it = module->connections().begin(); it != module->connections().end(); ++it) {
			bool show_conn = !only_selected;
			if (only_selected) {
				RTLIL::SigSpec sigs = it->first;
				sigs.append(it->second);
				for (auto &c : sigs.chunks()) {
					if (c.wire == NULL || !design->selected(module, c.wire))
						continue;
					show_conn = true;
				}
			}
			if (show_conn) {
				if (only_selected && first_conn_line)
					f << stringf("\n");
				dump_conn(f, indent + "  ", it->first, it->second);
				first_conn_line = false;
			}
		}
	}

	if (print_header)
		f << stringf("%s" "end\n", indent.c_str());
}

void ILANG_BACKEND::dump_design(std::ostream &f, RTLIL::Design *design, bool only_selected, bool flag_m, bool flag_n)
{
#ifndef NDEBUG
	int init_autoidx = autoidx;
#endif

	if (!flag_m) {
		int count_selected_mods = 0;
		for (auto it = design->modules_.begin(); it != design->modules_.end(); ++it) {
			if (design->selected_whole_module(it->first))
				flag_m = true;
			if (design->selected(it->second))
				count_selected_mods++;
		}
		if (count_selected_mods > 1)
			flag_m = true;
	}

	if (!only_selected || flag_m) {
		if (only_selected)
			f << stringf("\n");
		f << stringf("autoidx %d\n", autoidx);
	}

	for (auto it = design->modules_.begin(); it != design->modules_.end(); ++it) {
		if (!only_selected || design->selected(it->second)) {
			if (only_selected)
				f << stringf("\n");
			dump_module(f, "", it->second, design, only_selected, flag_m, flag_n);
		}
	}

	log_assert(init_autoidx == autoidx);
}

YOSYS_NAMESPACE_END
PRIVATE_NAMESPACE_BEGIN

struct IlangBackend : public Backend {
	IlangBackend() : Backend("ilang", "write design to ilang file") { }
	void help() YS_OVERRIDE
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
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool selected = false;

		log_header(design, "Executing ILANG backend.\n");

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

		design->sort();

		log("Output filename: %s\n", filename.c_str());
		*f << stringf("# Generated by %s\n", yosys_version_str);
		ILANG_BACKEND::dump_design(*f, design, selected, true, false);
	}
} IlangBackend;

struct DumpPass : public Pass {
	DumpPass() : Pass("dump", "print parts of the design in ilang format") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dump [options] [selection]\n");
		log("\n");
		log("Write the selected parts of the design to the console or specified file in\n");
		log("ilang format.\n");
		log("\n");
		log("    -m\n");
		log("        also dump the module headers, even if only parts of a single\n");
		log("        module is selected\n");
		log("\n");
		log("    -n\n");
		log("        only dump the module headers if the entire module is selected\n");
		log("\n");
		log("    -o <filename>\n");
		log("        write to the specified file.\n");
		log("\n");
		log("    -a <filename>\n");
		log("        like -outfile but append instead of overwrite\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string filename;
		bool flag_m = false, flag_n = false, append = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if ((arg == "-o" || arg == "-outfile") && argidx+1 < args.size()) {
				filename = args[++argidx];
				append = false;
				continue;
			}
			if ((arg == "-a" || arg == "-append") && argidx+1 < args.size()) {
				filename = args[++argidx];
				append = true;
				continue;
			}
			if (arg == "-m") {
				flag_m = true;
				continue;
			}
			if (arg == "-n") {
				flag_n = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::ostream *f;
		std::stringstream buf;

		if (!filename.empty()) {
			rewrite_filename(filename);
			std::ofstream *ff = new std::ofstream;
			ff->open(filename.c_str(), append ? std::ofstream::app : std::ofstream::trunc);
			if (ff->fail()) {
				delete ff;
				log_error("Can't open file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
			}
			f = ff;
		} else {
			f = &buf;
		}

		ILANG_BACKEND::dump_design(*f, design, true, flag_m, flag_n);

		if (!filename.empty()) {
			delete f;
		} else {
			log("%s", buf.str().c_str());
		}
	}
} DumpPass;

PRIVATE_NAMESPACE_END
