/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
 *  representation.
 *
 */

#include "rtlil_backend.h"
#include "kernel/yosys.h"
#include "kernel/utils.h"
#include <errno.h>
#include <iterator>

USING_YOSYS_NAMESPACE
using namespace RTLIL_BACKEND;
YOSYS_NAMESPACE_BEGIN

void RTLIL_BACKEND::dump_attributes(std::ostream &f, std::string indent, const RTLIL::AttrObject *obj, const RTLIL::Design *design, DumpMode mode)
{
	if (design && design->obj_src_id(obj) != Twine::Null) {
		TwineRef id = design->obj_src_id(obj);
		f << stringf("%s" "attribute \\src ", indent);
		if (mode == DumpMode::Readable) {
			dump_const(f, RTLIL::Const(design->twines.str(id)));
		} else {
			dump_const(f, RTLIL::Const(stringf("@%zu", id)));
			if (mode == DumpMode::Replayable)
				f << stringf("  # %s", design->twines.str(id).c_str());
		}
		f << stringf("\n");
	}
	for (const auto& [name, value] : reversed(obj->attributes)) {
		f << stringf("%s" "attribute %s ", indent, name);
		dump_const(f, value);
		f << stringf("\n");
	}
}

void RTLIL_BACKEND::dump_twines(std::ostream &f, const RTLIL::Design *design)
{
	if (!design || design->twines.size() == 0)
		return;
	f << stringf("twines\n");
	std::vector<TwineRef> ids;
	for (size_t idx = 0; idx < design->twines.backing.size(); ++idx)
		ids.push_back(STATIC_TWINE_END + idx);
	std::sort(ids.begin(), ids.end());
	for (TwineRef id : ids) {
		const Twine &n = design->twines[id];
		if (n.is_leaf()) {
			f << stringf("  leaf %zu ", id);
			dump_const(f, RTLIL::Const(n.leaf()));
			f << stringf("\n");
		} else if (n.is_suffix()) {
			f << stringf("  suffix %zu %zu ", id, n.suffix().prefix);
			dump_const(f, RTLIL::Const(n.suffix().tail));
			f << stringf("\n");
		} else if (n.is_concat()) {
			f << stringf("  concat %zu", id);
			for (TwineRef c : n.children())
				f << stringf(" %zu", c);
			f << stringf("\n");
		}
	}
	f << stringf("end\n");
}

void RTLIL_BACKEND::dump_const(std::ostream &f, const RTLIL::Const &data, int width, int offset, bool autoint)
{
	if (width < 0)
		width = data.size() - offset;
	if ((data.flags & RTLIL::CONST_FLAG_STRING) == 0 || width != (int)data.size()) {
		if (width == 32 && autoint) {
			int32_t val = 0;
			for (int i = 0; i < width; i++) {
				log_assert(offset+i < (int)data.size());
				switch (data[offset+i]) {
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
		if ((data.flags & RTLIL::CONST_FLAG_UNSIZED) == 0) {
			f << stringf("%d'", width);
		}
		if (data.flags & RTLIL::CONST_FLAG_SIGNED) {
			f << stringf("s");
		}
		if (data.is_fully_undef_x_only()) {
			f << "x";
		} else {
			for (int i = offset+width-1; i >= offset; i--) {
				log_assert(i < (int)data.size());
				switch (data[i]) {
				case State::S0: f << stringf("0"); break;
				case State::S1: f << stringf("1"); break;
				case RTLIL::Sx: f << stringf("x"); break;
				case RTLIL::Sz: f << stringf("z"); break;
				case RTLIL::Sa: f << stringf("-"); break;
				case RTLIL::Sm: f << stringf("m"); break;
				}
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
				f << stringf("\\%03o", (unsigned char)str[i]);
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

static std::string twine_handle(TwineRef ref)
{
	return stringf("%s@%zu", twine_is_public(ref) ? "$pub" : "$priv", (size_t)twine_untag(ref));
}

static std::string twine_ref(const RTLIL::Design *design, TwineRef ref, DumpMode mode)
{
	if (mode == DumpMode::Readable || twine_untag(ref) < STATIC_TWINE_END)
		return design->twines.str(ref);
	return twine_handle(ref);
}

static std::string twine_cmt(const RTLIL::Design *design, TwineRef ref, DumpMode mode)
{
	if (mode != DumpMode::Replayable || twine_untag(ref) < STATIC_TWINE_END)
		return "";
	return stringf("  # %s", design->twines.str(ref).c_str());
}

void RTLIL_BACKEND::dump_sigchunk(std::ostream &f, const RTLIL::SigChunk &chunk, bool autoint, DumpMode mode)
{
	if (chunk.wire == NULL) {
		dump_const(f, chunk.data, chunk.width, chunk.offset, autoint);
	} else {
		TwineRef wref = chunk.wire->name.ref();
		std::string name = (mode == DumpMode::Readable || twine_untag(wref) < STATIC_TWINE_END)
			? chunk.wire->name.str() : twine_handle(wref);
		if (chunk.width == chunk.wire->width && chunk.offset == 0)
			f << name;
		else if (chunk.width == 1)
			f << stringf("%s [%d]", name.c_str(), chunk.offset);
		else
			f << stringf("%s [%d:%d]", name.c_str(), chunk.offset+chunk.width-1, chunk.offset);
	}
}

void RTLIL_BACKEND::dump_sigspec(std::ostream &f, const RTLIL::SigSpec &sig, bool autoint, DumpMode mode)
{
	if (sig.is_chunk()) {
		dump_sigchunk(f, sig.as_chunk(), autoint, mode);
	} else {
		f << stringf("{ ");
		auto chunks = sig.chunks();
		for (const auto& chunk : reversed(chunks)) {
			dump_sigchunk(f, chunk, false, mode);
			f << stringf(" ");
		}
		f << stringf("}");
	}
}

void RTLIL_BACKEND::dump_wire(std::ostream &f, std::string indent, const RTLIL::Wire *wire, const RTLIL::Design *design, DumpMode mode)
{
	dump_attributes(f, indent, wire, design, mode);
	if (wire->driverCell_) {
		f << stringf("%s" "# driver %s %s\n", indent,
				wire->driverCell()->name, design->twines.str(wire->driverPort()).c_str());
	}
	f << stringf("%s" "wire ", indent);
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
	if (wire->is_signed)
		f << stringf("signed ");
	f << twine_ref(design, wire->name.ref(), mode) << twine_cmt(design, wire->name.ref(), mode) << "\n";
}

void RTLIL_BACKEND::dump_memory(std::ostream &f, std::string indent, const RTLIL::Memory *memory, const RTLIL::Design *design, DumpMode mode)
{
	dump_attributes(f, indent, memory, design, mode);
	f << stringf("%s" "memory ", indent);
	if (memory->width != 1)
		f << stringf("width %d ", memory->width);
	if (memory->size != 0)
		f << stringf("size %d ", memory->size);
	if (memory->start_offset != 0)
		f << stringf("offset %d ", memory->start_offset);
	f << twine_ref(design, memory->meta_->name, mode) << twine_cmt(design, memory->meta_->name, mode) << "\n";
}

void RTLIL_BACKEND::dump_cell(std::ostream &f, std::string indent, const RTLIL::Cell *cell, const RTLIL::Design *design, DumpMode mode)
{
	dump_attributes(f, indent, cell, design, mode);
	f << stringf("%s" "cell ", indent);
	f << twine_ref(design, cell->type.ref(), mode) << " " << twine_ref(design, cell->name.ref(), mode)
		<< twine_cmt(design, cell->type.ref(), mode) << twine_cmt(design, cell->name.ref(), mode) << "\n";
	for (const auto& [name, param] : reversed(cell->parameters)) {
		f << stringf("%s  parameter%s%s%s %s ", indent,
				(param.flags & RTLIL::CONST_FLAG_SIGNED) != 0 ? " signed" : "",
				(param.flags & RTLIL::CONST_FLAG_REAL) != 0 ? " real" : "",
				(param.flags & RTLIL::CONST_FLAG_UNSIZED) != 0 ? " unsized" : "",
				name);
		dump_const(f, param);
		f << stringf("\n");
	}
	for (const auto& [port, sig] : reversed(cell->connections_)) {
		f << stringf("%s  connect ", indent);
		f << twine_ref(design, port, mode) << " ";
		dump_sigspec(f, sig, true, mode);
		f << twine_cmt(design, port, mode) << "\n";
	}
	f << stringf("%s" "end\n", indent);
}

void RTLIL_BACKEND::dump_proc_case_body(std::ostream &f, std::string indent, const RTLIL::CaseRule *cs, const RTLIL::Design *design, DumpMode mode)
{
	for (const auto& [lhs, rhs] : cs->actions) {
		f << stringf("%s" "assign ", indent);
		dump_sigspec(f, lhs, true, mode);
		f << stringf(" ");
		dump_sigspec(f, rhs, true, mode);
		f << stringf("\n");
	}

	for (const auto& sw : cs->switches)
		dump_proc_switch(f, indent, sw, design, mode);
}

void RTLIL_BACKEND::dump_proc_switch(std::ostream &f, std::string indent, const RTLIL::SwitchRule *sw, const RTLIL::Design *design, DumpMode mode)
{
	dump_attributes(f, indent, sw, design, mode);

	f << stringf("%s" "switch ", indent);
	dump_sigspec(f, sw->signal, true, mode);
	f << stringf("\n");

	for (const auto case_ : sw->cases)
	{
		dump_attributes(f, indent, case_, design, mode);
		f << stringf("%s  case ", indent);
		for (size_t i = 0; i < case_->compare.size(); i++) {
			if (i > 0)
				f << stringf(" , ");
			dump_sigspec(f, case_->compare[i], true, mode);
		}
		f << stringf("\n");

		dump_proc_case_body(f, indent + "    ", case_, design, mode);
	}

	f << stringf("%s" "end\n", indent);
}

void RTLIL_BACKEND::dump_proc_sync(std::ostream &f, std::string indent, const RTLIL::SyncRule *sy, const RTLIL::Design *design, DumpMode mode)
{
	f << stringf("%s" "sync ", indent);
	switch (sy->type) {
	case RTLIL::ST0: f << stringf("low ");
	if (0) case RTLIL::ST1: f << stringf("high ");
	if (0) case RTLIL::STp: f << stringf("posedge ");
	if (0) case RTLIL::STn: f << stringf("negedge ");
	if (0) case RTLIL::STe: f << stringf("edge ");
		dump_sigspec(f, sy->signal, true, mode);
		f << stringf("\n");
		break;
	case RTLIL::STa: f << stringf("always\n"); break;
	case RTLIL::STg: f << stringf("global\n"); break;
	case RTLIL::STi: f << stringf("init\n"); break;
	}

	for (const auto& [lhs, rhs] : sy->actions) {
		f << stringf("%s  update ", indent);
		dump_sigspec(f, lhs, true, mode);
		f << stringf(" ");
		dump_sigspec(f, rhs, true, mode);
		f << stringf("\n");
	}

	for (auto &it: sy->mem_write_actions) {
		dump_attributes(f, indent, &it, design, mode);
		f << stringf("%s  memwr %s ", indent, it.memid);
		dump_sigspec(f, it.address, true, mode);
		f << stringf(" ");
		dump_sigspec(f, it.data, true, mode);
		f << stringf(" ");
		dump_sigspec(f, it.enable, true, mode);
		f << stringf(" ");
		dump_const(f, it.priority_mask);
		f << stringf("\n");
	}
}

void RTLIL_BACKEND::dump_proc(std::ostream &f, std::string indent, const RTLIL::Process *proc, const RTLIL::Design *design, DumpMode mode)
{
	dump_attributes(f, indent, proc, design, mode);
	f << stringf("%s" "process ", indent);
	f << twine_ref(design, proc->meta_->name, mode) << twine_cmt(design, proc->meta_->name, mode) << "\n";
	dump_proc_case_body(f, indent + "  ", &proc->root_case, design, mode);
	for (auto* sync : proc->syncs)
		dump_proc_sync(f, indent + "  ", sync, design, mode);
	f << stringf("%s" "end\n", indent);
}

void RTLIL_BACKEND::dump_conn(std::ostream &f, std::string indent, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right, DumpMode mode)
{
	f << stringf("%s" "connect ", indent);
	dump_sigspec(f, left, true, mode);
	f << stringf(" ");
	dump_sigspec(f, right, true, mode);
	f << stringf("\n");
}

void RTLIL_BACKEND::dump_module(std::ostream &f, std::string indent, RTLIL::Module *module, RTLIL::Design *design, bool only_selected, bool flag_m, bool flag_n, DumpMode mode)
{
	bool print_header = flag_m || module->is_selected_whole();
	bool print_body = !flag_n || !module->is_selected_whole();

	if (print_header)
	{
		dump_attributes(f, indent, module, design, mode);

		f << stringf("%s" "module ", indent);
		f << twine_ref(design, module->meta_->name, mode) << twine_cmt(design, module->meta_->name, mode) << "\n";

		if (!module->avail_parameters.empty()) {
			if (only_selected)
				f << stringf("\n");
			for (const auto &p : module->avail_parameters) {
				const auto &it = module->parameter_default_values.find(p);
				if (it == module->parameter_default_values.end()) {
					f << stringf("%s" "  parameter %s\n", indent, p);
				} else {
					f << stringf("%s" "  parameter %s ", indent, p);
					dump_const(f, it->second);
					f << stringf("\n");
				}
			}
		}
	}

	if (print_body)
	{
		for (const auto& [_, wire] : reversed(module->wires_))
			if (!only_selected || design->selected(module, wire)) {
				if (only_selected)
					f << stringf("\n");
				dump_wire(f, indent + "  ", wire, design, mode);
			}

		for (const auto& [_, mem] : reversed(module->memories))
			if (!only_selected || design->selected(module, mem)) {
				if (only_selected)
					f << stringf("\n");
				dump_memory(f, indent + "  ", mem, design, mode);
			}

		for (const auto& [_, cell] : reversed(module->cells_))
			if (!only_selected || design->selected(module, cell)) {
				if (only_selected)
					f << stringf("\n");
				dump_cell(f, indent + "  ", cell, design, mode);
			}

		for (const auto& [_, process] : reversed(module->processes))
			if (!only_selected || design->selected(module, process)) {
				if (only_selected)
					f << stringf("\n");
				dump_proc(f, indent + "  ", process, design, mode);
			}

		bool first_conn_line = true;
		for (const auto& [lhs, rhs] : module->connections()) {
			bool show_conn = !only_selected || design->selected_whole_module(module->meta_->name);
			if (!show_conn) {
				RTLIL::SigSpec sigs = lhs;
				sigs.append(rhs);
				for (auto &c : sigs.chunks()) {
					if (c.wire == NULL || !design->selected(module, c.wire))
						continue;
					show_conn = true;
				}
			}
			if (show_conn) {
				if (only_selected && first_conn_line)
					f << stringf("\n");
				dump_conn(f, indent + "  ", lhs, rhs, mode);
				first_conn_line = false;
			}
		}
	}

	if (print_header)
		f << stringf("%s" "end\n", indent);
}

void RTLIL_BACKEND::dump_design(std::ostream &f, RTLIL::Design *design, bool only_selected, bool flag_m, bool flag_n, DumpMode mode)
{
	int init_autoidx = autoidx;

	if (!flag_m) {
		int count_selected_mods = 0;
		for (auto* module : design->modules()) {
			if (design->selected_whole_module(module->meta_->name))
				flag_m = true;
			if (design->selected_module(module->meta_->name)) {
				count_selected_mods++;
				if (module->has_processes())
					log_warning("Module %s contains processes. Case action sources attributes will be lost.\n", log_id(module));
			}
		}
		if (count_selected_mods > 1)
			flag_m = true;
	}

	if (!only_selected || flag_m) {
		if (only_selected)
			f << stringf("\n");
		f << stringf("autoidx %d\n", autoidx);
		if (mode != DumpMode::Readable)
			dump_twines(f, design);
	}

	for (const auto& [_, module] : reversed(design->modules_)) {
		if (!only_selected || design->selected_module(module->meta_->name)) {
			if (only_selected)
				f << stringf("\n");
			dump_module(f, "", module, design, only_selected, flag_m, flag_n, mode);
		}
	}

	log_assert(init_autoidx == autoidx);
}

YOSYS_NAMESPACE_END
PRIVATE_NAMESPACE_BEGIN

struct RTLILBackend : public Backend {
	RTLILBackend() : Backend("rtlil", "write design to RTLIL file") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_rtlil [filename]\n");
		log("\n");
		log("Write the current design to an RTLIL file. (RTLIL is a text representation\n");
		log("of a design in yosys's internal format.)\n");
		log("\n");
		log("    -selected\n");
		log("        only write selected parts of the design.\n");
		log("\n");
		log("    -sort\n");
		log("        sort design in-place (used to be default).\n");
		log("\n");
		log("    -readable\n");
		log("        print human-readable names. Loses twine id information,\n");
		log("        breaking perfect replayability.\n");
		log("\n");
		log("    -small\n");
		log("        like the default replayable form but omit the `# name`\n");
		log("        comments, for smaller files.\n");
		log("\n");
		log("Without -readable or -small the output is fully replayable: twine\n");
		log("handles plus a `twines` pool section and `# name` comments.\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool selected = false;
		bool do_sort = false;
		DumpMode mode = DumpMode::Replayable;

		log_header(design, "Executing RTLIL backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-selected") {
				selected = true;
				continue;
			}
			if (arg == "-sort") {
				do_sort = true;
				continue;
			}
			if (arg == "-readable" || arg == "-resolve-src") {
				mode = DumpMode::Readable;
				continue;
			}
			if (arg == "-small") {
				mode = DumpMode::Small;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		log("Output filename: %s\n", filename);

		if (do_sort)
			design->sort();

		*f << stringf("# Generated by %s\n", yosys_maybe_version());
		RTLIL_BACKEND::dump_design(*f, design, selected, true, false, mode);
	}
} RTLILBackend;

struct DumpPass : public Pass {
	DumpPass() : Pass("dump", "print parts of the design in RTLIL format") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dump [options] [selection]\n");
		log("\n");
		log("Write the selected parts of the design to the console or specified file in\n");
		log("RTLIL format.\n");
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
		log("    -readable\n");
		log("        print human-readable names. Loses twine id information,\n");
		log("        breaking perfect replayability.\n");
		log("\n");
		log("    -small\n");
		log("        like the default replayable form but omit the `# name`\n");
		log("        comments, for smaller output.\n");
		log("\n");
		log("Without -readable or -small the output is fully replayable (the same\n");
		log("form write_rtlil produces): twine handles plus a `twines` pool section\n");
		log("and `# name` comments.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string filename;
		bool flag_m = false, flag_n = false, append = false;
		DumpMode mode = DumpMode::Replayable;

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
			if (arg == "-readable" || arg == "-resolve-src") {
				mode = DumpMode::Readable;
				continue;
			}
			if (arg == "-small") {
				mode = DumpMode::Small;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::ostream *f;
		std::stringstream buf;
		bool empty = filename.empty();

		if (!empty) {
			rewrite_filename(filename);
			std::ofstream *ff = new std::ofstream;
			ff->open(filename, append ? std::ofstream::app : std::ofstream::trunc);
			if (ff->fail()) {
				delete ff;
				log_error("Can't open file `%s' for writing: %s\n", filename, strerror(errno));
			}
			f = ff;
		} else {
			f = &buf;
		}

		RTLIL_BACKEND::dump_design(*f, design, true, flag_m, flag_n, mode);

		if (!empty) {
			delete f;
		} else {
			log("%s", buf.str());
		}
	}
} DumpPass;

PRIVATE_NAMESPACE_END
