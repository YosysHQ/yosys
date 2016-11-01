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
 *  A simple and straightforward Verilog backend.
 *
 */

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/sigtools.h"
#include <string>
#include <sstream>
#include <set>
#include <map>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool verbose, norename, noattr, attr2comment, noexpr, nodec, nostr, defparam;
int auto_name_counter, auto_name_offset, auto_name_digits;
std::map<RTLIL::IdString, int> auto_name_map;
std::set<RTLIL::IdString> reg_wires, reg_ct;
std::string auto_prefix;

RTLIL::Module *active_module;

void reset_auto_counter_id(RTLIL::IdString id, bool may_rename)
{
	const char *str = id.c_str();

	if (*str == '$' && may_rename && !norename)
		auto_name_map[id] = auto_name_counter++;

	if (str[0] != '\\' || str[1] != '_' || str[2] == 0)
		return;

	for (int i = 2; str[i] != 0; i++) {
		if (str[i] == '_' && str[i+1] == 0)
			continue;
		if (str[i] < '0' || str[i] > '9')
			return;
	}

	int num = atoi(str+2);
	if (num >= auto_name_offset)
		auto_name_offset = num + 1;
}

void reset_auto_counter(RTLIL::Module *module)
{
	auto_name_map.clear();
	auto_name_counter = 0;
	auto_name_offset = 0;

	reset_auto_counter_id(module->name, false);

	for (auto it = module->wires_.begin(); it != module->wires_.end(); ++it)
		reset_auto_counter_id(it->second->name, true);

	for (auto it = module->cells_.begin(); it != module->cells_.end(); ++it) {
		reset_auto_counter_id(it->second->name, true);
		reset_auto_counter_id(it->second->type, false);
	}

	for (auto it = module->processes.begin(); it != module->processes.end(); ++it)
		reset_auto_counter_id(it->second->name, false);

	auto_name_digits = 1;
	for (size_t i = 10; i < auto_name_offset + auto_name_map.size(); i = i*10)
		auto_name_digits++;

	if (verbose)
		for (auto it = auto_name_map.begin(); it != auto_name_map.end(); ++it)
			log("  renaming `%s' to `%s_%0*d_'.\n", it->first.c_str(), auto_prefix.c_str(), auto_name_digits, auto_name_offset + it->second);
}

std::string next_auto_id()
{
	return stringf("%s_%0*d_", auto_prefix.c_str(), auto_name_digits, auto_name_offset + auto_name_counter++);
}

std::string id(RTLIL::IdString internal_id, bool may_rename = true)
{
	const char *str = internal_id.c_str();
	bool do_escape = false;

	if (may_rename && auto_name_map.count(internal_id) != 0)
		return stringf("%s_%0*d_", auto_prefix.c_str(), auto_name_digits, auto_name_offset + auto_name_map[internal_id]);

	if (*str == '\\')
		str++;

	if ('0' <= *str && *str <= '9')
		do_escape = true;

	for (int i = 0; str[i]; i++)
	{
		if ('0' <= str[i] && str[i] <= '9')
			continue;
		if ('a' <= str[i] && str[i] <= 'z')
			continue;
		if ('A' <= str[i] && str[i] <= 'Z')
			continue;
		if (str[i] == '_')
			continue;
		do_escape = true;
		break;
	}

	if (do_escape)
		return "\\" + std::string(str) + " ";
	return std::string(str);
}

bool is_reg_wire(RTLIL::SigSpec sig, std::string &reg_name)
{
	if (!sig.is_chunk() || sig.as_chunk().wire == NULL)
		return false;

	RTLIL::SigChunk chunk = sig.as_chunk();

	if (reg_wires.count(chunk.wire->name) == 0)
		return false;

	reg_name = id(chunk.wire->name);
	if (sig.size() != chunk.wire->width) {
		if (sig.size() == 1)
			reg_name += stringf("[%d]", chunk.wire->start_offset +  chunk.offset);
		else if (chunk.wire->upto)
			reg_name += stringf("[%d:%d]", (chunk.wire->width - (chunk.offset + chunk.width - 1) - 1) + chunk.wire->start_offset,
					(chunk.wire->width - chunk.offset - 1) + chunk.wire->start_offset);
		else
			reg_name += stringf("[%d:%d]", chunk.wire->start_offset +  chunk.offset + chunk.width - 1,
					chunk.wire->start_offset +  chunk.offset);
	}

	return true;
}

void dump_const(std::ostream &f, const RTLIL::Const &data, int width = -1, int offset = 0, bool no_decimal = false, bool set_signed = false, bool escape_comment = false)
{
	if (width < 0)
		width = data.bits.size() - offset;
	if (nostr)
		goto dump_bits;
	if ((data.flags & RTLIL::CONST_FLAG_STRING) == 0 || width != (int)data.bits.size()) {
		if (width == 32 && !no_decimal && !nodec) {
			int32_t val = 0;
			for (int i = offset+width-1; i >= offset; i--) {
				log_assert(i < (int)data.bits.size());
				if (data.bits[i] != RTLIL::S0 && data.bits[i] != RTLIL::S1)
					goto dump_bits;
				if (data.bits[i] == RTLIL::S1)
					val |= 1 << (i - offset);
			}
			if (set_signed && val < 0)
				f << stringf("-32'sd%u", -val);
			else
				f << stringf("32'%sd%u", set_signed ? "s" : "", val);
		} else {
	dump_bits:
			f << stringf("%d'%sb", width, set_signed ? "s" : "");
			if (width == 0)
				f << stringf("0");
			for (int i = offset+width-1; i >= offset; i--) {
				log_assert(i < (int)data.bits.size());
				switch (data.bits[i]) {
				case RTLIL::S0: f << stringf("0"); break;
				case RTLIL::S1: f << stringf("1"); break;
				case RTLIL::Sx: f << stringf("x"); break;
				case RTLIL::Sz: f << stringf("z"); break;
				case RTLIL::Sa: f << stringf("z"); break;
				case RTLIL::Sm: log_error("Found marker state in final netlist.");
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
				f << stringf("\\%03o", str[i]);
			else if (str[i] == '"')
				f << stringf("\\\"");
			else if (str[i] == '\\')
				f << stringf("\\\\");
			else if (str[i] == '/' && escape_comment && i > 0 && str[i-1] == '*')
				f << stringf("\\/");
			else
				f << str[i];
		}
		f << stringf("\"");
	}
}

void dump_sigchunk(std::ostream &f, const RTLIL::SigChunk &chunk, bool no_decimal = false)
{
	if (chunk.wire == NULL) {
		dump_const(f, chunk.data, chunk.width, chunk.offset, no_decimal);
	} else {
		if (chunk.width == chunk.wire->width && chunk.offset == 0) {
			f << stringf("%s", id(chunk.wire->name).c_str());
		} else if (chunk.width == 1) {
			if (chunk.wire->upto)
				f << stringf("%s[%d]", id(chunk.wire->name).c_str(), (chunk.wire->width - chunk.offset - 1) + chunk.wire->start_offset);
			else
				f << stringf("%s[%d]", id(chunk.wire->name).c_str(), chunk.offset + chunk.wire->start_offset);
		} else {
			if (chunk.wire->upto)
				f << stringf("%s[%d:%d]", id(chunk.wire->name).c_str(),
						(chunk.wire->width - (chunk.offset + chunk.width - 1) - 1) + chunk.wire->start_offset,
						(chunk.wire->width - chunk.offset - 1) + chunk.wire->start_offset);
			else
				f << stringf("%s[%d:%d]", id(chunk.wire->name).c_str(),
						(chunk.offset + chunk.width - 1) + chunk.wire->start_offset,
						chunk.offset + chunk.wire->start_offset);
		}
	}
}

void dump_sigspec(std::ostream &f, const RTLIL::SigSpec &sig)
{
	if (sig.is_chunk()) {
		dump_sigchunk(f, sig.as_chunk());
	} else {
		f << stringf("{ ");
		for (auto it = sig.chunks().rbegin(); it != sig.chunks().rend(); ++it) {
			if (it != sig.chunks().rbegin())
				f << stringf(", ");
			dump_sigchunk(f, *it, true);
		}
		f << stringf(" }");
	}
}

void dump_attributes(std::ostream &f, std::string indent, dict<RTLIL::IdString, RTLIL::Const> &attributes, char term = '\n', bool modattr = false)
{
	if (noattr)
		return;
	for (auto it = attributes.begin(); it != attributes.end(); ++it) {
		f << stringf("%s" "%s %s", indent.c_str(), attr2comment ? "/*" : "(*", id(it->first).c_str());
		f << stringf(" = ");
		if (modattr && (it->second == Const(0, 1) || it->second == Const(0)))
			f << stringf(" 0 ");
		else if (modattr && (it->second == Const(1, 1) || it->second == Const(1)))
			f << stringf(" 1 ");
		else
			dump_const(f, it->second, -1, 0, false, false, attr2comment);
		f << stringf(" %s%c", attr2comment ? "*/" : "*)", term);
	}
}

void dump_wire(std::ostream &f, std::string indent, RTLIL::Wire *wire)
{
	dump_attributes(f, indent, wire->attributes);
#if 0
	if (wire->port_input && !wire->port_output)
		f << stringf("%s" "input %s", indent.c_str(), reg_wires.count(wire->name) ? "reg " : "");
	else if (!wire->port_input && wire->port_output)
		f << stringf("%s" "output %s", indent.c_str(), reg_wires.count(wire->name) ? "reg " : "");
	else if (wire->port_input && wire->port_output)
		f << stringf("%s" "inout %s", indent.c_str(), reg_wires.count(wire->name) ? "reg " : "");
	else
		f << stringf("%s" "%s ", indent.c_str(), reg_wires.count(wire->name) ? "reg" : "wire");
	if (wire->width != 1)
		f << stringf("[%d:%d] ", wire->width - 1 + wire->start_offset, wire->start_offset);
	f << stringf("%s;\n", id(wire->name).c_str());
#else
	// do not use Verilog-2k "output reg" syntax in Verilog export
	std::string range = "";
	if (wire->width != 1) {
		if (wire->upto)
			range = stringf(" [%d:%d]", wire->start_offset, wire->width - 1 + wire->start_offset);
		else
			range = stringf(" [%d:%d]", wire->width - 1 + wire->start_offset, wire->start_offset);
	}
	if (wire->port_input && !wire->port_output)
		f << stringf("%s" "input%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
	if (!wire->port_input && wire->port_output)
		f << stringf("%s" "output%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
	if (wire->port_input && wire->port_output)
		f << stringf("%s" "inout%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
	if (reg_wires.count(wire->name)) {
		f << stringf("%s" "reg%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
		if (wire->attributes.count("\\init")) {
			f << stringf("%s" "initial %s = ", indent.c_str(), id(wire->name).c_str());
			dump_const(f, wire->attributes.at("\\init"));
			f << stringf(";\n");
		}
	} else if (!wire->port_input && !wire->port_output)
		f << stringf("%s" "wire%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
#endif
}

void dump_memory(std::ostream &f, std::string indent, RTLIL::Memory *memory)
{
	dump_attributes(f, indent, memory->attributes);
	f << stringf("%s" "reg [%d:0] %s [%d:0];\n", indent.c_str(), memory->width-1, id(memory->name).c_str(), memory->size-1);
}

void dump_cell_expr_port(std::ostream &f, RTLIL::Cell *cell, std::string port, bool gen_signed = true)
{
	if (gen_signed && cell->parameters.count("\\" + port + "_SIGNED") > 0 && cell->parameters["\\" + port + "_SIGNED"].as_bool()) {
		f << stringf("$signed(");
		dump_sigspec(f, cell->getPort("\\" + port));
		f << stringf(")");
	} else
		dump_sigspec(f, cell->getPort("\\" + port));
}

std::string cellname(RTLIL::Cell *cell)
{
	if (!norename && cell->name[0] == '$' && reg_ct.count(cell->type) && cell->hasPort("\\Q"))
	{
		RTLIL::SigSpec sig = cell->getPort("\\Q");
		if (GetSize(sig) != 1 || sig.is_fully_const())
			goto no_special_reg_name;

		RTLIL::Wire *wire = sig[0].wire;

		if (wire->name[0] != '\\')
			goto no_special_reg_name;

		std::string cell_name = wire->name.str();

		size_t pos = cell_name.find('[');
		if (pos != std::string::npos)
			cell_name = cell_name.substr(0, pos) + "_reg" + cell_name.substr(pos);
		else
			cell_name = cell_name + "_reg";

		if (wire->width != 1)
			cell_name += stringf("[%d]", wire->start_offset + sig[0].offset);

		if (active_module && active_module->count_id(cell_name) > 0)
				goto no_special_reg_name;

		return id(cell_name);
	}
	else
	{
no_special_reg_name:
		return id(cell->name).c_str();
	}
}

void dump_cell_expr_uniop(std::ostream &f, std::string indent, RTLIL::Cell *cell, std::string op)
{
	f << stringf("%s" "assign ", indent.c_str());
	dump_sigspec(f, cell->getPort("\\Y"));
	f << stringf(" = %s ", op.c_str());
	dump_attributes(f, "", cell->attributes, ' ');
	dump_cell_expr_port(f, cell, "A", true);
	f << stringf(";\n");
}

void dump_cell_expr_binop(std::ostream &f, std::string indent, RTLIL::Cell *cell, std::string op)
{
	f << stringf("%s" "assign ", indent.c_str());
	dump_sigspec(f, cell->getPort("\\Y"));
	f << stringf(" = ");
	dump_cell_expr_port(f, cell, "A", true);
	f << stringf(" %s ", op.c_str());
	dump_attributes(f, "", cell->attributes, ' ');
	dump_cell_expr_port(f, cell, "B", true);
	f << stringf(";\n");
}

bool dump_cell_expr(std::ostream &f, std::string indent, RTLIL::Cell *cell)
{
	if (cell->type == "$_NOT_") {
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = ");
		f << stringf("~");
		dump_attributes(f, "", cell->attributes, ' ');
		dump_cell_expr_port(f, cell, "A", false);
		f << stringf(";\n");
		return true;
	}

	if (cell->type.in("$_AND_", "$_NAND_", "$_OR_", "$_NOR_", "$_XOR_", "$_XNOR_")) {
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = ");
		if (cell->type.in("$_NAND_", "$_NOR_", "$_XNOR_"))
			f << stringf("~(");
		dump_cell_expr_port(f, cell, "A", false);
		f << stringf(" ");
		if (cell->type.in("$_AND_", "$_NAND_"))
			f << stringf("&");
		if (cell->type.in("$_OR_", "$_NOR_"))
			f << stringf("|");
		if (cell->type.in("$_XOR_", "$_XNOR_"))
			f << stringf("^");
		dump_attributes(f, "", cell->attributes, ' ');
		f << stringf(" ");
		dump_cell_expr_port(f, cell, "B", false);
		if (cell->type.in("$_NAND_", "$_NOR_", "$_XNOR_"))
			f << stringf(")");
		f << stringf(";\n");
		return true;
	}

	if (cell->type == "$_MUX_") {
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = ");
		dump_cell_expr_port(f, cell, "S", false);
		f << stringf(" ? ");
		dump_attributes(f, "", cell->attributes, ' ');
		dump_cell_expr_port(f, cell, "B", false);
		f << stringf(" : ");
		dump_cell_expr_port(f, cell, "A", false);
		f << stringf(";\n");
		return true;
	}

	if (cell->type.in("$_AOI3_", "$_OAI3_")) {
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = ~((");
		dump_cell_expr_port(f, cell, "A", false);
		f << stringf(cell->type == "$_AOI3_" ? " & " : " | ");
		dump_cell_expr_port(f, cell, "B", false);
		f << stringf(cell->type == "$_AOI3_" ? ") |" : ") &");
		dump_attributes(f, "", cell->attributes, ' ');
		f << stringf(" ");
		dump_cell_expr_port(f, cell, "C", false);
		f << stringf(");\n");
		return true;
	}

	if (cell->type.in("$_AOI4_", "$_OAI4_")) {
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = ~((");
		dump_cell_expr_port(f, cell, "A", false);
		f << stringf(cell->type == "$_AOI4_" ? " & " : " | ");
		dump_cell_expr_port(f, cell, "B", false);
		f << stringf(cell->type == "$_AOI4_" ? ") |" : ") &");
		dump_attributes(f, "", cell->attributes, ' ');
		f << stringf(" (");
		dump_cell_expr_port(f, cell, "C", false);
		f << stringf(cell->type == "$_AOI4_" ? " & " : " | ");
		dump_cell_expr_port(f, cell, "D", false);
		f << stringf("));\n");
		return true;
	}

	if (cell->type.substr(0, 6) == "$_DFF_")
	{
		std::string reg_name = cellname(cell);
		bool out_is_reg_wire = is_reg_wire(cell->getPort("\\Q"), reg_name);

		if (!out_is_reg_wire)
			f << stringf("%s" "reg %s;\n", indent.c_str(), reg_name.c_str());

		dump_attributes(f, indent, cell->attributes);
		f << stringf("%s" "always @(%sedge ", indent.c_str(), cell->type[6] == 'P' ? "pos" : "neg");
		dump_sigspec(f, cell->getPort("\\C"));
		if (cell->type[7] != '_') {
			f << stringf(" or %sedge ", cell->type[7] == 'P' ? "pos" : "neg");
			dump_sigspec(f, cell->getPort("\\R"));
		}
		f << stringf(")\n");

		if (cell->type[7] != '_') {
			f << stringf("%s" "  if (%s", indent.c_str(), cell->type[7] == 'P' ? "" : "!");
			dump_sigspec(f, cell->getPort("\\R"));
			f << stringf(")\n");
			f << stringf("%s" "    %s <= %c;\n", indent.c_str(), reg_name.c_str(), cell->type[8]);
			f << stringf("%s" "  else\n", indent.c_str());
		}

		f << stringf("%s" "    %s <= ", indent.c_str(), reg_name.c_str());
		dump_cell_expr_port(f, cell, "D", false);
		f << stringf(";\n");

		if (!out_is_reg_wire) {
			f << stringf("%s" "assign ", indent.c_str());
			dump_sigspec(f, cell->getPort("\\Q"));
			f << stringf(" = %s;\n", reg_name.c_str());
		}

		return true;
	}

	if (cell->type.substr(0, 8) == "$_DFFSR_")
	{
		char pol_c = cell->type[8], pol_s = cell->type[9], pol_r = cell->type[10];

		std::string reg_name = cellname(cell);
		bool out_is_reg_wire = is_reg_wire(cell->getPort("\\Q"), reg_name);

		if (!out_is_reg_wire)
			f << stringf("%s" "reg %s;\n", indent.c_str(), reg_name.c_str());

		dump_attributes(f, indent, cell->attributes);
		f << stringf("%s" "always @(%sedge ", indent.c_str(), pol_c == 'P' ? "pos" : "neg");
		dump_sigspec(f, cell->getPort("\\C"));
		f << stringf(" or %sedge ", pol_s == 'P' ? "pos" : "neg");
		dump_sigspec(f, cell->getPort("\\S"));
		f << stringf(" or %sedge ", pol_r == 'P' ? "pos" : "neg");
		dump_sigspec(f, cell->getPort("\\R"));
		f << stringf(")\n");

		f << stringf("%s" "  if (%s", indent.c_str(), pol_r == 'P' ? "" : "!");
		dump_sigspec(f, cell->getPort("\\R"));
		f << stringf(")\n");
		f << stringf("%s" "    %s <= 0;\n", indent.c_str(), reg_name.c_str());

		f << stringf("%s" "  else if (%s", indent.c_str(), pol_s == 'P' ? "" : "!");
		dump_sigspec(f, cell->getPort("\\S"));
		f << stringf(")\n");
		f << stringf("%s" "    %s <= 1;\n", indent.c_str(), reg_name.c_str());

		f << stringf("%s" "  else\n", indent.c_str());
		f << stringf("%s" "    %s <= ", indent.c_str(), reg_name.c_str());
		dump_cell_expr_port(f, cell, "D", false);
		f << stringf(";\n");

		if (!out_is_reg_wire) {
			f << stringf("%s" "assign ", indent.c_str());
			dump_sigspec(f, cell->getPort("\\Q"));
			f << stringf(" = %s;\n", reg_name.c_str());
		}

		return true;
	}

#define HANDLE_UNIOP(_type, _operator) \
	if (cell->type ==_type) { dump_cell_expr_uniop(f, indent, cell, _operator); return true; }
#define HANDLE_BINOP(_type, _operator) \
	if (cell->type ==_type) { dump_cell_expr_binop(f, indent, cell, _operator); return true; }

	HANDLE_UNIOP("$not", "~")
	HANDLE_UNIOP("$pos", "+")
	HANDLE_UNIOP("$neg", "-")

	HANDLE_BINOP("$and",  "&")
	HANDLE_BINOP("$or",   "|")
	HANDLE_BINOP("$xor",  "^")
	HANDLE_BINOP("$xnor", "~^")

	HANDLE_UNIOP("$reduce_and",  "&")
	HANDLE_UNIOP("$reduce_or",   "|")
	HANDLE_UNIOP("$reduce_xor",  "^")
	HANDLE_UNIOP("$reduce_xnor", "~^")
	HANDLE_UNIOP("$reduce_bool", "|")

	HANDLE_BINOP("$shl",  "<<")
	HANDLE_BINOP("$shr",  ">>")
	HANDLE_BINOP("$sshl", "<<<")
	HANDLE_BINOP("$sshr", ">>>")

	HANDLE_BINOP("$lt",  "<")
	HANDLE_BINOP("$le",  "<=")
	HANDLE_BINOP("$eq",  "==")
	HANDLE_BINOP("$ne",  "!=")
	HANDLE_BINOP("$eqx", "===")
	HANDLE_BINOP("$nex", "!==")
	HANDLE_BINOP("$ge",  ">=")
	HANDLE_BINOP("$gt",  ">")

	HANDLE_BINOP("$add", "+")
	HANDLE_BINOP("$sub", "-")
	HANDLE_BINOP("$mul", "*")
	HANDLE_BINOP("$div", "/")
	HANDLE_BINOP("$mod", "%")
	HANDLE_BINOP("$pow", "**")

	HANDLE_UNIOP("$logic_not", "!")
	HANDLE_BINOP("$logic_and", "&&")
	HANDLE_BINOP("$logic_or",  "||")

#undef HANDLE_UNIOP
#undef HANDLE_BINOP

	if (cell->type == "$mux")
	{
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = ");
		dump_sigspec(f, cell->getPort("\\S"));
		f << stringf(" ? ");
		dump_attributes(f, "", cell->attributes, ' ');
		dump_sigspec(f, cell->getPort("\\B"));
		f << stringf(" : ");
		dump_sigspec(f, cell->getPort("\\A"));
		f << stringf(";\n");
		return true;
	}

	if (cell->type == "$pmux" || cell->type == "$pmux_safe")
	{
		int width = cell->parameters["\\WIDTH"].as_int();
		int s_width = cell->getPort("\\S").size();
		std::string func_name = cellname(cell);

		f << stringf("%s" "function [%d:0] %s;\n", indent.c_str(), width-1, func_name.c_str());
		f << stringf("%s" "  input [%d:0] a;\n", indent.c_str(), width-1);
		f << stringf("%s" "  input [%d:0] b;\n", indent.c_str(), s_width*width-1);
		f << stringf("%s" "  input [%d:0] s;\n", indent.c_str(), s_width-1);

		dump_attributes(f, indent + "  ", cell->attributes);
		if (cell->type != "$pmux_safe" && !noattr)
			f << stringf("%s" "  (* parallel_case *)\n", indent.c_str());
		f << stringf("%s" "  casez (s)", indent.c_str());
		if (cell->type != "$pmux_safe")
			f << stringf(noattr ? " // synopsys parallel_case\n" : "\n");

		for (int i = 0; i < s_width; i++)
		{
			f << stringf("%s" "    %d'b", indent.c_str(), s_width);

			for (int j = s_width-1; j >= 0; j--)
				f << stringf("%c", j == i ? '1' : cell->type == "$pmux_safe" ? '0' : '?');

			f << stringf(":\n");
			f << stringf("%s" "      %s = b[%d:%d];\n", indent.c_str(), func_name.c_str(), (i+1)*width-1, i*width);
		}

		f << stringf("%s" "    default:\n", indent.c_str());
		f << stringf("%s" "      %s = a;\n", indent.c_str(), func_name.c_str());

		f << stringf("%s" "  endcase\n", indent.c_str());
		f << stringf("%s" "endfunction\n", indent.c_str());

		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = %s(", func_name.c_str());
		dump_sigspec(f, cell->getPort("\\A"));
		f << stringf(", ");
		dump_sigspec(f, cell->getPort("\\B"));
		f << stringf(", ");
		dump_sigspec(f, cell->getPort("\\S"));
		f << stringf(");\n");
		return true;
	}

	if (cell->type == "$slice")
	{
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = ");
		dump_sigspec(f, cell->getPort("\\A"));
		f << stringf(" >> %d;\n", cell->parameters.at("\\OFFSET").as_int());
		return true;
	}

	if (cell->type == "$concat")
	{
		f << stringf("%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->getPort("\\Y"));
		f << stringf(" = { ");
		dump_sigspec(f, cell->getPort("\\B"));
		f << stringf(" , ");
		dump_sigspec(f, cell->getPort("\\A"));
		f << stringf(" };\n");
		return true;
	}

	if (cell->type == "$dffsr")
	{
		SigSpec sig_clk = cell->getPort("\\CLK");
		SigSpec sig_set = cell->getPort("\\SET");
		SigSpec sig_clr = cell->getPort("\\CLR");
		SigSpec sig_d = cell->getPort("\\D");
		SigSpec sig_q = cell->getPort("\\Q");

		int width = cell->parameters["\\WIDTH"].as_int();
		bool pol_clk = cell->parameters["\\CLK_POLARITY"].as_bool();
		bool pol_set = cell->parameters["\\SET_POLARITY"].as_bool();
		bool pol_clr = cell->parameters["\\CLR_POLARITY"].as_bool();

		std::string reg_name = cellname(cell);
		bool out_is_reg_wire = is_reg_wire(sig_q, reg_name);

		if (!out_is_reg_wire)
			f << stringf("%s" "reg [%d:0] %s;\n", indent.c_str(), width-1, reg_name.c_str());

		for (int i = 0; i < width; i++) {
			f << stringf("%s" "always @(%sedge ", indent.c_str(), pol_clk ? "pos" : "neg");
			dump_sigspec(f, sig_clk);
			f << stringf(", %sedge ", pol_set ? "pos" : "neg");
			dump_sigspec(f, sig_set);
			f << stringf(", %sedge ", pol_clr ? "pos" : "neg");
			dump_sigspec(f, sig_clr);
			f << stringf(")\n");

			f << stringf("%s" "  if (%s", indent.c_str(), pol_clr ? "" : "!");
			dump_sigspec(f, sig_clr);
			f << stringf(") %s[%d] <= 1'b0;\n", reg_name.c_str(), i);

			f << stringf("%s" "  else if (%s", indent.c_str(), pol_set ? "" : "!");
			dump_sigspec(f, sig_set);
			f << stringf(") %s[%d] <= 1'b1;\n", reg_name.c_str(), i);

			f << stringf("%s" "  else  %s[%d] <= ", indent.c_str(), reg_name.c_str(), i);
			dump_sigspec(f, sig_d[i]);
			f << stringf(";\n");
		}

		if (!out_is_reg_wire) {
			f << stringf("%s" "assign ", indent.c_str());
			dump_sigspec(f, sig_q);
			f << stringf(" = %s;\n", reg_name.c_str());
		}

		return true;
	}

	if (cell->type == "$dff" || cell->type == "$adff" || cell->type == "$dffe")
	{
		RTLIL::SigSpec sig_clk, sig_arst, sig_en, val_arst;
		bool pol_clk, pol_arst = false, pol_en = false;

		sig_clk = cell->getPort("\\CLK");
		pol_clk = cell->parameters["\\CLK_POLARITY"].as_bool();

		if (cell->type == "$adff") {
			sig_arst = cell->getPort("\\ARST");
			pol_arst = cell->parameters["\\ARST_POLARITY"].as_bool();
			val_arst = RTLIL::SigSpec(cell->parameters["\\ARST_VALUE"]);
		}

		if (cell->type == "$dffe") {
			sig_en = cell->getPort("\\EN");
			pol_en = cell->parameters["\\EN_POLARITY"].as_bool();
		}

		std::string reg_name = cellname(cell);
		bool out_is_reg_wire = is_reg_wire(cell->getPort("\\Q"), reg_name);

		if (!out_is_reg_wire)
			f << stringf("%s" "reg [%d:0] %s;\n", indent.c_str(), cell->parameters["\\WIDTH"].as_int()-1, reg_name.c_str());

		f << stringf("%s" "always @(%sedge ", indent.c_str(), pol_clk ? "pos" : "neg");
		dump_sigspec(f, sig_clk);
		if (cell->type == "$adff") {
			f << stringf(" or %sedge ", pol_arst ? "pos" : "neg");
			dump_sigspec(f, sig_arst);
		}
		f << stringf(")\n");

		if (cell->type == "$adff") {
			f << stringf("%s" "  if (%s", indent.c_str(), pol_arst ? "" : "!");
			dump_sigspec(f, sig_arst);
			f << stringf(")\n");
			f << stringf("%s" "    %s <= ", indent.c_str(), reg_name.c_str());
			dump_sigspec(f, val_arst);
			f << stringf(";\n");
			f << stringf("%s" "  else\n", indent.c_str());
		}

		if (cell->type == "$dffe") {
			f << stringf("%s" "  if (%s", indent.c_str(), pol_en ? "" : "!");
			dump_sigspec(f, sig_en);
			f << stringf(")\n");
		}

		f << stringf("%s" "    %s <= ", indent.c_str(), reg_name.c_str());
		dump_cell_expr_port(f, cell, "D", false);
		f << stringf(";\n");

		if (!out_is_reg_wire) {
			f << stringf("%s" "assign ", indent.c_str());
			dump_sigspec(f, cell->getPort("\\Q"));
			f << stringf(" = %s;\n", reg_name.c_str());
		}

		return true;
	}

	if (cell->type == "$mem")
	{
		RTLIL::IdString memid = cell->parameters["\\MEMID"].decode_string();
		std::string mem_id = id(cell->parameters["\\MEMID"].decode_string());
		int abits = cell->parameters["\\ABITS"].as_int();
		int size = cell->parameters["\\SIZE"].as_int();
		int width = cell->parameters["\\WIDTH"].as_int();
		bool use_init = !(RTLIL::SigSpec(cell->parameters["\\INIT"]).is_fully_undef());

		// for memory block make something like:
		//  reg [7:0] memid [3:0];
		//  initial begin
		//    memid[0] <= ...
		//  end
		f << stringf("%s" "reg [%d:%d] %s [%d:%d];\n", indent.c_str(), width-1, 0, mem_id.c_str(), size-1, 0);
		if (use_init)
		{
			f << stringf("%s" "initial begin\n", indent.c_str());
			for (int i=0; i<size; i++)
			{
				f << stringf("%s" "  %s[%d] <= ", indent.c_str(), mem_id.c_str(), i);
				dump_const(f, cell->parameters["\\INIT"].extract(i*width, width));
				f << stringf(";\n");
			}
			f << stringf("%s" "end\n", indent.c_str());
		}

		// create a map : "edge clk" -> expressions within that clock domain
		dict<std::string, std::vector<std::string>> clk_to_lof_body;
		clk_to_lof_body[""] = std::vector<std::string>();
		std::string clk_domain_str;
		// create a list of reg declarations
		std::vector<std::string> lof_reg_declarations;

		int nread_ports = cell->parameters["\\RD_PORTS"].as_int();
		RTLIL::SigSpec sig_rd_clk, sig_rd_en, sig_rd_data, sig_rd_addr;
		bool use_rd_clk, rd_clk_posedge, rd_transparent;
		// read ports
		for (int i=0; i < nread_ports; i++)
		{
			sig_rd_clk = cell->getPort("\\RD_CLK").extract(i);
			sig_rd_en = cell->getPort("\\RD_EN").extract(i);
			sig_rd_data = cell->getPort("\\RD_DATA").extract(i*width, width);
			sig_rd_addr = cell->getPort("\\RD_ADDR").extract(i*abits, abits);
			use_rd_clk = cell->parameters["\\RD_CLK_ENABLE"].extract(i).as_bool();
			rd_clk_posedge = cell->parameters["\\RD_CLK_POLARITY"].extract(i).as_bool();
			rd_transparent = cell->parameters["\\RD_TRANSPARENT"].extract(i).as_bool();
			{
				std::ostringstream os;
				dump_sigspec(os, sig_rd_clk);
				clk_domain_str = stringf("%sedge %s", rd_clk_posedge ? "pos" : "neg", os.str().c_str());
				if( clk_to_lof_body.count(clk_domain_str) == 0 )
					clk_to_lof_body[clk_domain_str] = std::vector<std::string>();
			}
			if (use_rd_clk && !rd_transparent)
			{
				// for clocked read ports make something like:
				//   reg [..] temp_id;
				//   always @(posedge clk)
				//      if (rd_en) temp_id <= array_reg[r_addr];
				//   assign r_data = temp_id;
				std::string temp_id = next_auto_id();
				lof_reg_declarations.push_back( stringf("reg [%d:0] %s;\n", sig_rd_data.size() - 1, temp_id.c_str()) );
				{
					std::ostringstream os;
					if (sig_rd_en != RTLIL::SigBit(true))
					{
						os << stringf("if (");
						dump_sigspec(os, sig_rd_en);
						os << stringf(") ");
					}
					os << stringf("%s <= %s[", temp_id.c_str(), mem_id.c_str());
					dump_sigspec(os, sig_rd_addr);
					os << stringf("];\n");
					clk_to_lof_body[clk_domain_str].push_back(os.str());
				}
				{
					std::ostringstream os;
					dump_sigspec(os, sig_rd_data);
					std::string line = stringf("assign %s = %s;\n", os.str().c_str(), temp_id.c_str());
					clk_to_lof_body[""].push_back(line);
				}
			} else {
				if (rd_transparent) {
					// for rd-transparent read-ports make something like:
					//   reg [..] temp_id;
					//   always @(posedge clk)
					//     temp_id <= r_addr;
					//   assign r_data = array_reg[temp_id];
					std::string temp_id = next_auto_id();
					lof_reg_declarations.push_back( stringf("reg [%d:0] %s;\n", sig_rd_addr.size() - 1, temp_id.c_str()) );
					{
						std::ostringstream os;
						dump_sigspec(os, sig_rd_addr);
						std::string line = stringf("%s <= %s;\n", temp_id.c_str(), os.str().c_str());
						clk_to_lof_body[clk_domain_str].push_back(line);
					}
					{
						std::ostringstream os;
						dump_sigspec(os, sig_rd_data);
						std::string line = stringf("assign %s = %s[%s];\n", os.str().c_str(), mem_id.c_str(), temp_id.c_str());
						clk_to_lof_body[""].push_back(line);
					}
				} else {
					// for non-clocked read-ports make something like:
					//   assign r_data = array_reg[r_addr];
					std::ostringstream os, os2;
					dump_sigspec(os, sig_rd_data);
					dump_sigspec(os2, sig_rd_addr);
					std::string line = stringf("assign %s = %s[%s];\n", os.str().c_str(), mem_id.c_str(), os2.str().c_str());
					clk_to_lof_body[""].push_back(line);
				}
			}
		}

		int nwrite_ports = cell->parameters["\\WR_PORTS"].as_int();
		RTLIL::SigSpec sig_wr_clk, sig_wr_data, sig_wr_addr, sig_wr_en;
		bool wr_clk_posedge;
		SigMap sigmap(active_module);
		// write ports
		for (int i=0; i < nwrite_ports; i++)
		{
			sig_wr_clk = cell->getPort("\\WR_CLK").extract(i);
			sig_wr_data = cell->getPort("\\WR_DATA").extract(i*width, width);
			sig_wr_addr = cell->getPort("\\WR_ADDR").extract(i*abits, abits);
			sig_wr_en = cell->getPort("\\WR_EN").extract(i*width, width);
			wr_clk_posedge = cell->parameters["\\WR_CLK_POLARITY"].extract(i).as_bool();
			{
				std::ostringstream os;
				dump_sigspec(os, sig_wr_clk);
				clk_domain_str = stringf("%sedge %s", wr_clk_posedge ? "pos" : "neg", os.str().c_str());
				if( clk_to_lof_body.count(clk_domain_str) == 0 )
					clk_to_lof_body[clk_domain_str] = std::vector<std::string>();
			}
			//   make something like:
			//   always @(posedge clk)
			//      if (wr_en_bit) memid[w_addr][??] <= w_data[??];
			//   ...
			for (int i = 0; i < GetSize(sig_wr_en); i++)
			{
				int start_i = i, width = 1;
				SigBit wen_bit = sig_wr_en[i];

				while (i+1 < GetSize(sig_wr_en) && sigmap(sig_wr_en[i+1]) == sigmap(wen_bit))
					i++, width++;

				if (wen_bit == State::S0)
					continue;

				std::ostringstream os;
				if (wen_bit != State::S1)
				{
					os << stringf("if (");
					dump_sigspec(os, wen_bit);
					os << stringf(") ");
				}
				os << stringf("%s[", mem_id.c_str());
				dump_sigspec(os, sig_wr_addr);
				if (width == GetSize(sig_wr_en))
					os << stringf("] <= ");
				else
					os << stringf("][%d:%d] <= ", i, start_i);
				dump_sigspec(os, sig_wr_data.extract(start_i, width));
				os << stringf(";\n");
				clk_to_lof_body[clk_domain_str].push_back(os.str());
			}
		}
		// Output Verilog that looks something like this:
		// reg [..] _3_;
		// always @(posedge CLK2) begin
		//   _3_ <= memory[D1ADDR];
		//   if (A1EN)
		//     memory[A1ADDR] <= A1DATA;
		//   if (A2EN)
		//     memory[A2ADDR] <= A2DATA;
		//   ...
		// end
		// always @(negedge CLK1) begin
		//   if (C1EN)
		//     memory[C1ADDR] <= C1DATA;
		// end
		// ...
		// assign D1DATA = _3_;
		// assign D2DATA <= memory[D2ADDR];

		// the reg ... definitions
		for(auto &reg : lof_reg_declarations)
		{
			f << stringf("%s" "%s", indent.c_str(), reg.c_str());
		}
		// the block of expressions by clock domain
		for(auto &pair : clk_to_lof_body)
		{
			std::string clk_domain = pair.first;
			std::vector<std::string> lof_lines = pair.second;
			if( clk_domain != "")
			{
				f << stringf("%s" "always @(%s) begin\n", indent.c_str(), clk_domain.c_str());
				for(auto &line : lof_lines)
					f << stringf("%s%s" "%s", indent.c_str(), indent.c_str(), line.c_str());
				f << stringf("%s" "end\n", indent.c_str());
			}
			else
			{
				// the non-clocked assignments
				for(auto &line : lof_lines)
					f << stringf("%s" "%s", indent.c_str(), line.c_str());
			}
		}

		return true;
	}

	// FIXME: $_SR_[PN][PN]_, $_DLATCH_[PN]_, $_DLATCHSR_[PN][PN][PN]_
	// FIXME: $sr, $dlatch, $memrd, $memwr, $fsm

	return false;
}

void dump_cell(std::ostream &f, std::string indent, RTLIL::Cell *cell)
{
	if (cell->type[0] == '$' && !noexpr) {
		if (dump_cell_expr(f, indent, cell))
			return;
	}

	dump_attributes(f, indent, cell->attributes);
	f << stringf("%s" "%s", indent.c_str(), id(cell->type, false).c_str());

	if (!defparam && cell->parameters.size() > 0) {
		f << stringf(" #(");
		for (auto it = cell->parameters.begin(); it != cell->parameters.end(); ++it) {
			if (it != cell->parameters.begin())
				f << stringf(",");
			f << stringf("\n%s  .%s(", indent.c_str(), id(it->first).c_str());
			bool is_signed = (it->second.flags & RTLIL::CONST_FLAG_SIGNED) != 0;
			dump_const(f, it->second, -1, 0, false, is_signed);
			f << stringf(")");
		}
		f << stringf("\n%s" ")", indent.c_str());
	}

	std::string cell_name = cellname(cell);
	if (cell_name != id(cell->name))
		f << stringf(" %s /* %s */ (", cell_name.c_str(), id(cell->name).c_str());
	else
		f << stringf(" %s (", cell_name.c_str());

	bool first_arg = true;
	std::set<RTLIL::IdString> numbered_ports;
	for (int i = 1; true; i++) {
		char str[16];
		snprintf(str, 16, "$%d", i);
		for (auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
			if (it->first != str)
				continue;
			if (!first_arg)
				f << stringf(",");
			first_arg = false;
			f << stringf("\n%s  ", indent.c_str());
			dump_sigspec(f, it->second);
			numbered_ports.insert(it->first);
			goto found_numbered_port;
		}
		break;
	found_numbered_port:;
	}
	for (auto it = cell->connections().begin(); it != cell->connections().end(); ++it) {
		if (numbered_ports.count(it->first))
			continue;
		if (!first_arg)
			f << stringf(",");
		first_arg = false;
		f << stringf("\n%s  .%s(", indent.c_str(), id(it->first).c_str());
		if (it->second.size() > 0)
			dump_sigspec(f, it->second);
		f << stringf(")");
	}
	f << stringf("\n%s" ");\n", indent.c_str());

	if (defparam && cell->parameters.size() > 0) {
		for (auto it = cell->parameters.begin(); it != cell->parameters.end(); ++it) {
			f << stringf("%sdefparam %s.%s = ", indent.c_str(), cell_name.c_str(), id(it->first).c_str());
			bool is_signed = (it->second.flags & RTLIL::CONST_FLAG_SIGNED) != 0;
			dump_const(f, it->second, -1, 0, false, is_signed);
			f << stringf(";\n");
		}
	}

}

void dump_conn(std::ostream &f, std::string indent, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right)
{
	f << stringf("%s" "assign ", indent.c_str());
	dump_sigspec(f, left);
	f << stringf(" = ");
	dump_sigspec(f, right);
	f << stringf(";\n");
}

void dump_proc_switch(std::ostream &f, std::string indent, RTLIL::SwitchRule *sw);

void dump_case_body(std::ostream &f, std::string indent, RTLIL::CaseRule *cs, bool omit_trailing_begin = false)
{
	int number_of_stmts = cs->switches.size() + cs->actions.size();

	if (!omit_trailing_begin && number_of_stmts >= 2)
		f << stringf("%s" "begin\n", indent.c_str());

	for (auto it = cs->actions.begin(); it != cs->actions.end(); ++it) {
		if (it->first.size() == 0)
			continue;
		f << stringf("%s  ", indent.c_str());
		dump_sigspec(f, it->first);
		f << stringf(" = ");
		dump_sigspec(f, it->second);
		f << stringf(";\n");
	}

	for (auto it = cs->switches.begin(); it != cs->switches.end(); ++it)
		dump_proc_switch(f, indent + "  ", *it);

	if (!omit_trailing_begin && number_of_stmts == 0)
		f << stringf("%s  /* empty */;\n", indent.c_str());

	if (omit_trailing_begin || number_of_stmts >= 2)
		f << stringf("%s" "end\n", indent.c_str());
}

void dump_proc_switch(std::ostream &f, std::string indent, RTLIL::SwitchRule *sw)
{
	if (sw->signal.size() == 0) {
		f << stringf("%s" "begin\n", indent.c_str());
		for (auto it = sw->cases.begin(); it != sw->cases.end(); ++it) {
			if ((*it)->compare.size() == 0)
				dump_case_body(f, indent + "  ", *it);
		}
		f << stringf("%s" "end\n", indent.c_str());
		return;
	}

	f << stringf("%s" "casez (", indent.c_str());
	dump_sigspec(f, sw->signal);
	f << stringf(")\n");

	bool got_default = false;
	for (auto it = sw->cases.begin(); it != sw->cases.end(); ++it) {
		if ((*it)->compare.size() == 0) {
			if (got_default)
				continue;
			f << stringf("%s  default", indent.c_str());
			got_default = true;
		} else {
			f << stringf("%s  ", indent.c_str());
			for (size_t i = 0; i < (*it)->compare.size(); i++) {
				if (i > 0)
					f << stringf(", ");
				dump_sigspec(f, (*it)->compare[i]);
			}
		}
		f << stringf(":\n");
		dump_case_body(f, indent + "    ", *it);
	}

	f << stringf("%s" "endcase\n", indent.c_str());
}

void case_body_find_regs(RTLIL::CaseRule *cs)
{
	for (auto it = cs->switches.begin(); it != cs->switches.end(); ++it)
	for (auto it2 = (*it)->cases.begin(); it2 != (*it)->cases.end(); it2++)
		case_body_find_regs(*it2);

	for (auto it = cs->actions.begin(); it != cs->actions.end(); ++it) {
		for (auto &c : it->first.chunks())
			if (c.wire != NULL)
				reg_wires.insert(c.wire->name);
	}
}

void dump_process(std::ostream &f, std::string indent, RTLIL::Process *proc, bool find_regs = false)
{
	if (find_regs) {
		case_body_find_regs(&proc->root_case);
		for (auto it = proc->syncs.begin(); it != proc->syncs.end(); ++it)
		for (auto it2 = (*it)->actions.begin(); it2 != (*it)->actions.end(); it2++) {
			for (auto &c : it2->first.chunks())
				if (c.wire != NULL)
					reg_wires.insert(c.wire->name);
		}
		return;
	}

	f << stringf("%s" "always @* begin\n", indent.c_str());
	dump_case_body(f, indent, &proc->root_case, true);

	std::string backup_indent = indent;

	for (size_t i = 0; i < proc->syncs.size(); i++)
	{
		RTLIL::SyncRule *sync = proc->syncs[i];
		indent = backup_indent;

		if (sync->type == RTLIL::STa) {
			f << stringf("%s" "always @* begin\n", indent.c_str());
		} else {
			f << stringf("%s" "always @(", indent.c_str());
			if (sync->type == RTLIL::STp || sync->type == RTLIL::ST1)
				f << stringf("posedge ");
			if (sync->type == RTLIL::STn || sync->type == RTLIL::ST0)
				f << stringf("negedge ");
			dump_sigspec(f, sync->signal);
			f << stringf(") begin\n");
		}
		std::string ends = indent + "end\n";
		indent += "  ";

		if (sync->type == RTLIL::ST0 || sync->type == RTLIL::ST1) {
			f << stringf("%s" "if (%s", indent.c_str(), sync->type == RTLIL::ST0 ? "!" : "");
			dump_sigspec(f, sync->signal);
			f << stringf(") begin\n");
			ends = indent + "end\n" + ends;
			indent += "  ";
		}

		if (sync->type == RTLIL::STp || sync->type == RTLIL::STn) {
			for (size_t j = 0; j < proc->syncs.size(); j++) {
				RTLIL::SyncRule *sync2 = proc->syncs[j];
				if (sync2->type == RTLIL::ST0 || sync2->type == RTLIL::ST1) {
					f << stringf("%s" "if (%s", indent.c_str(), sync2->type == RTLIL::ST1 ? "!" : "");
					dump_sigspec(f, sync2->signal);
					f << stringf(") begin\n");
					ends = indent + "end\n" + ends;
					indent += "  ";
				}
			}
		}

		for (auto it = sync->actions.begin(); it != sync->actions.end(); ++it) {
			if (it->first.size() == 0)
				continue;
			f << stringf("%s  ", indent.c_str());
			dump_sigspec(f, it->first);
			f << stringf(" <= ");
			dump_sigspec(f, it->second);
			f << stringf(";\n");
		}

		f << stringf("%s", ends.c_str());
	}
}

void dump_module(std::ostream &f, std::string indent, RTLIL::Module *module)
{
	reg_wires.clear();
	reset_auto_counter(module);
	active_module = module;

	if (!module->processes.empty())
		log_warning("Module %s contains unmapped RTLIL proccesses. RTLIL processes\n"
				"can't always be mapped directly to Verilog always blocks. Unintended\n"
				"changes in simulation behavior are possible! Use \"proc\" to convert\n"
				"processes to logic networks and registers.", log_id(module));

	f << stringf("\n");
	for (auto it = module->processes.begin(); it != module->processes.end(); ++it)
		dump_process(f, indent + "  ", it->second, true);

	if (!noexpr)
	{
		std::set<std::pair<RTLIL::Wire*,int>> reg_bits;
		for (auto &it : module->cells_)
		{
			RTLIL::Cell *cell = it.second;
			if (!reg_ct.count(cell->type) || !cell->hasPort("\\Q"))
				continue;

			RTLIL::SigSpec sig = cell->getPort("\\Q");

			if (sig.is_chunk()) {
				RTLIL::SigChunk chunk = sig.as_chunk();
				if (chunk.wire != NULL)
					for (int i = 0; i < chunk.width; i++)
						reg_bits.insert(std::pair<RTLIL::Wire*,int>(chunk.wire, chunk.offset+i));
			}
		}
		for (auto &it : module->wires_)
		{
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				if (reg_bits.count(std::pair<RTLIL::Wire*,int>(wire, i)) == 0)
					goto this_wire_aint_reg;
			if (wire->width)
				reg_wires.insert(wire->name);
		this_wire_aint_reg:;
		}
	}

	dump_attributes(f, indent, module->attributes, '\n', true);
	f << stringf("%s" "module %s(", indent.c_str(), id(module->name, false).c_str());
	bool keep_running = true;
	for (int port_id = 1; keep_running; port_id++) {
		keep_running = false;
		for (auto it = module->wires_.begin(); it != module->wires_.end(); ++it) {
			RTLIL::Wire *wire = it->second;
			if (wire->port_id == port_id) {
				if (port_id != 1)
					f << stringf(", ");
				f << stringf("%s", id(wire->name).c_str());
				keep_running = true;
				continue;
			}
		}
	}
	f << stringf(");\n");

	for (auto it = module->wires_.begin(); it != module->wires_.end(); ++it)
		dump_wire(f, indent + "  ", it->second);

	for (auto it = module->memories.begin(); it != module->memories.end(); ++it)
		dump_memory(f, indent + "  ", it->second);

	for (auto it = module->cells_.begin(); it != module->cells_.end(); ++it)
		dump_cell(f, indent + "  ", it->second);

	for (auto it = module->processes.begin(); it != module->processes.end(); ++it)
		dump_process(f, indent + "  ", it->second);

	for (auto it = module->connections().begin(); it != module->connections().end(); ++it)
		dump_conn(f, indent + "  ", it->first, it->second);

	f << stringf("%s" "endmodule\n", indent.c_str());
	active_module = NULL;
}

struct VerilogBackend : public Backend {
	VerilogBackend() : Backend("verilog", "write design to Verilog file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_verilog [options] [filename]\n");
		log("\n");
		log("Write the current design to a Verilog file.\n");
		log("\n");
		log("    -norename\n");
		log("        without this option all internal object names (the ones with a dollar\n");
		log("        instead of a backslash prefix) are changed to short names in the\n");
		log("        format '_<number>_'.\n");
		log("\n");
		log("    -renameprefix <prefix>\n");
		log("        insert this prefix in front of auto-generated instance names\n");
		log("\n");
		log("    -noattr\n");
		log("        with this option no attributes are included in the output\n");
		log("\n");
		log("    -attr2comment\n");
		log("        with this option attributes are included as comments in the output\n");
		log("\n");
		log("    -noexpr\n");
		log("        without this option all internal cells are converted to Verilog\n");
		log("        expressions.\n");
		log("\n");
		log("    -nodec\n");
		log("        32-bit constant values are by default dumped as decimal numbers,\n");
		log("        not bit pattern. This option decativates this feature and instead\n");
		log("        will write out all constants in binary.\n");
		log("\n");
		log("    -nostr\n");
		log("        Parameters and attributes that are specified as strings in the\n");
		log("        original input will be output as strings by this back-end. This\n");
		log("        decativates this feature and instead will write string constants\n");
		log("        as binary numbers.\n");
		log("\n");
		log("    -defparam\n");
		log("        Use 'defparam' statements instead of the Verilog-2001 syntax for\n");
		log("        cell parameters.\n");
		log("\n");
		log("    -blackboxes\n");
		log("        usually modules with the 'blackbox' attribute are ignored. with\n");
		log("        this option set only the modules with the 'blackbox' attribute\n");
		log("        are written to the output file.\n");
		log("\n");
		log("    -selected\n");
		log("        only write selected modules. modules must be selected entirely or\n");
		log("        not at all.\n");
		log("\n");
		log("    -v\n");
		log("        verbose output (print new names of all renamed wires and cells)\n");
		log("\n");
		log("Note that RTLIL processes can't always be mapped directly to Verilog\n");
		log("always blocks. This frontend should only be used to export an RTLIL\n");
		log("netlist, i.e. after the \"proc\" pass has been used to convert all\n");
		log("processes to logic networks and registers. A warning is generated when\n");
		log("this command is called on a design with RTLIL processes.\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing Verilog backend.\n");

		verbose = false;
		norename = false;
		noattr = false;
		attr2comment = false;
		noexpr = false;
		nodec = false;
		nostr = false;
		defparam = false;
		auto_prefix = "";

		bool blackboxes = false;
		bool selected = false;

		reg_ct.clear();

		reg_ct.insert("$dff");
		reg_ct.insert("$adff");

		reg_ct.insert("$_DFF_N_");
		reg_ct.insert("$_DFF_P_");

		reg_ct.insert("$_DFF_NN0_");
		reg_ct.insert("$_DFF_NN1_");
		reg_ct.insert("$_DFF_NP0_");
		reg_ct.insert("$_DFF_NP1_");
		reg_ct.insert("$_DFF_PN0_");
		reg_ct.insert("$_DFF_PN1_");
		reg_ct.insert("$_DFF_PP0_");
		reg_ct.insert("$_DFF_PP1_");

		reg_ct.insert("$_DFFSR_NNN_");
		reg_ct.insert("$_DFFSR_NNP_");
		reg_ct.insert("$_DFFSR_NPN_");
		reg_ct.insert("$_DFFSR_NPP_");
		reg_ct.insert("$_DFFSR_PNN_");
		reg_ct.insert("$_DFFSR_PNP_");
		reg_ct.insert("$_DFFSR_PPN_");
		reg_ct.insert("$_DFFSR_PPP_");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-norename") {
				norename = true;
				continue;
			}
			if (arg == "-renameprefix" && argidx+1 < args.size()) {
				auto_prefix = args[++argidx];
				continue;
			}
			if (arg == "-noattr") {
				noattr = true;
				continue;
			}
			if (arg == "-attr2comment") {
				attr2comment = true;
				continue;
			}
			if (arg == "-noexpr") {
				noexpr = true;
				continue;
			}
			if (arg == "-nodec") {
				nodec = true;
				continue;
			}
			if (arg == "-nostr") {
				nostr = true;
				continue;
			}
			if (arg == "-defparam") {
				defparam = true;
				continue;
			}
			if (arg == "-blackboxes") {
				blackboxes = true;
				continue;
			}
			if (arg == "-selected") {
				selected = true;
				continue;
			}
			if (arg == "-v") {
				verbose = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		design->sort();

		*f << stringf("/* Generated by %s */\n", yosys_version_str);
		for (auto it = design->modules_.begin(); it != design->modules_.end(); ++it) {
			if (it->second->get_bool_attribute("\\blackbox") != blackboxes)
				continue;
			if (selected && !design->selected_whole_module(it->first)) {
				if (design->selected_module(it->first))
					log_cmd_error("Can't handle partially selected module %s!\n", RTLIL::id2cstr(it->first));
				continue;
			}
			log("Dumping module `%s'.\n", it->first.c_str());
			dump_module(*f, "", it->second);
		}

		reg_ct.clear();
	}
} VerilogBackend;

PRIVATE_NAMESPACE_END
