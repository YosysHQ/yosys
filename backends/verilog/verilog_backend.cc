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
 *  A simple and straightforward verilog backend.
 *
 *  Note that RTLIL processes can't always be mapped easily to a Verilog
 *  process. Therefore this frontend should only be used to export a
 *  Verilog netlist (i.e. after the "proc" pass has converted all processes
 *  to logic networks and registers).
 *
 */

#include "verilog_backend.h"
#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <assert.h>
#include <string>
#include <sstream>
#include <set>
#include <map>

namespace {

bool norename, noattr, attr2comment, noexpr;
int auto_name_counter, auto_name_offset, auto_name_digits;
std::map<std::string, int> auto_name_map;

std::set<std::string> reg_wires;

CellTypes reg_ct;
RTLIL::Module *active_module;

void reset_auto_counter_id(const std::string &id, bool may_rename)
{
	const char *str = id.c_str();

	if (*str == '$' && may_rename && !norename)
		auto_name_map[id] = auto_name_counter++;

	if (str[0] != '_' && str[1] != 0)
		return;
	for (int i = 0; str[i] != 0; i++) {
		if (str[i] == '_')
			continue;
		if (str[i] < '0' || str[i] > '9')
			return;
	}

	int num = atoi(str+1);
	if (num >= auto_name_offset)
		auto_name_offset = num + 1;
}

void reset_auto_counter(RTLIL::Module *module)
{
	auto_name_map.clear();
	auto_name_counter = 0;
	auto_name_offset = 0;

	reset_auto_counter_id(module->name, false);

	for (auto it = module->wires.begin(); it != module->wires.end(); it++)
		reset_auto_counter_id(it->second->name, true);

	for (auto it = module->cells.begin(); it != module->cells.end(); it++) {
		reset_auto_counter_id(it->second->name, true);
		reset_auto_counter_id(it->second->type, false);
	}

	for (auto it = module->processes.begin(); it != module->processes.end(); it++)
		reset_auto_counter_id(it->second->name, false);

	auto_name_digits = 1;
	for (size_t i = 10; i < auto_name_offset + auto_name_map.size(); i = i*10)
		auto_name_digits++;

	for (auto it = auto_name_map.begin(); it != auto_name_map.end(); it++)
		log("  renaming `%s' to `_%0*d_'.\n", it->first.c_str(), auto_name_digits, auto_name_offset + it->second);
}

std::string id(std::string internal_id, bool may_rename = true)
{
	const char *str = internal_id.c_str();
	bool do_escape = false;

	if (may_rename && auto_name_map.count(internal_id) != 0) {
		char buffer[100];
		snprintf(buffer, 100, "_%0*d_", auto_name_digits, auto_name_offset + auto_name_map[internal_id]);
		return std::string(buffer);
	}

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
		else
			reg_name += stringf("[%d:%d]", chunk.wire->start_offset +  chunk.offset + chunk.width - 1,
					chunk.wire->start_offset +  chunk.offset);
	}

	return true;
}

void dump_const(FILE *f, const RTLIL::Const &data, int width = -1, int offset = 0, bool no_decimal = false, bool set_signed = false)
{
	if (width < 0)
		width = data.bits.size() - offset;
	if ((data.flags & RTLIL::CONST_FLAG_STRING) == 0 || width != (int)data.bits.size()) {
		if (width == 32 && !no_decimal) {
			int32_t val = 0;
			for (int i = offset+width-1; i >= offset; i--) {
				assert(i < (int)data.bits.size());
				if (data.bits[i] != RTLIL::S0 && data.bits[i] != RTLIL::S1)
					goto dump_bits;
				if (data.bits[i] == RTLIL::S1)
					val |= 1 << (i - offset);
			}
			// fprintf(f, "%s32'sd%u", val < 0 ? "-" : "", abs(val));
			fprintf(f, "%d", val);
		} else {
	dump_bits:
			fprintf(f, "%d'%sb", width, set_signed ? "s" : "");
			if (width == 0)
				fprintf(f, "0");
			for (int i = offset+width-1; i >= offset; i--) {
				assert(i < (int)data.bits.size());
				switch (data.bits[i]) {
				case RTLIL::S0: fprintf(f, "0"); break;
				case RTLIL::S1: fprintf(f, "1"); break;
				case RTLIL::Sx: fprintf(f, "x"); break;
				case RTLIL::Sz: fprintf(f, "z"); break;
				case RTLIL::Sa: fprintf(f, "z"); break;
				case RTLIL::Sm: log_error("Found marker state in final netlist.");
				}
			}
		}
	} else {
		fprintf(f, "\"");
		std::string str = data.decode_string();
		for (size_t i = 0; i < str.size(); i++) {
			if (str[i] == '\n')
				fprintf(f, "\\n");
			else if (str[i] == '\t')
				fprintf(f, "\\t");
			else if (str[i] < 32)
				fprintf(f, "\\%03o", str[i]);
			else if (str[i] == '"')
				fprintf(f, "\\\"");
			else if (str[i] == '\\')
				fprintf(f, "\\\\");
			else
				fputc(str[i], f);
		}
		fprintf(f, "\"");
	}
}

void dump_sigchunk(FILE *f, const RTLIL::SigChunk &chunk, bool no_decimal = false)
{
	if (chunk.wire == NULL) {
		dump_const(f, chunk.data, chunk.width, chunk.offset, no_decimal);
	} else {
		if (chunk.width == chunk.wire->width && chunk.offset == 0)
			fprintf(f, "%s", id(chunk.wire->name).c_str());
		else if (chunk.width == 1)
			fprintf(f, "%s[%d]", id(chunk.wire->name).c_str(), chunk.offset + chunk.wire->start_offset);
		else
			fprintf(f, "%s[%d:%d]", id(chunk.wire->name).c_str(),
					chunk.offset + chunk.wire->start_offset + chunk.width - 1,
					chunk.offset + chunk.wire->start_offset);
	}
}

void dump_sigspec(FILE *f, const RTLIL::SigSpec &sig)
{
	if (sig.is_chunk()) {
		dump_sigchunk(f, sig.as_chunk());
	} else {
		fprintf(f, "{ ");
		for (auto it = sig.chunks().rbegin(); it != sig.chunks().rend(); it++) {
			if (it != sig.chunks().rbegin())
				fprintf(f, ", ");
			dump_sigchunk(f, *it, true);
		}
		fprintf(f, " }");
	}
}

void dump_attributes(FILE *f, std::string indent, std::map<RTLIL::IdString, RTLIL::Const> &attributes, char term = '\n')
{
	if (noattr)
		return;
	for (auto it = attributes.begin(); it != attributes.end(); it++) {
		fprintf(f, "%s" "%s %s", indent.c_str(), attr2comment ? "/*" : "(*", id(it->first).c_str());
		fprintf(f, " = ");
		dump_const(f, it->second);
		fprintf(f, " %s%c", attr2comment ? "*/" : "*)", term);
	}
}

void dump_wire(FILE *f, std::string indent, RTLIL::Wire *wire)
{
	dump_attributes(f, indent, wire->attributes);
#if 0
	if (wire->port_input && !wire->port_output)
		fprintf(f, "%s" "input %s", indent.c_str(), reg_wires.count(wire->name) ? "reg " : "");
	else if (!wire->port_input && wire->port_output)
		fprintf(f, "%s" "output %s", indent.c_str(), reg_wires.count(wire->name) ? "reg " : "");
	else if (wire->port_input && wire->port_output)
		fprintf(f, "%s" "inout %s", indent.c_str(), reg_wires.count(wire->name) ? "reg " : "");
	else
		fprintf(f, "%s" "%s ", indent.c_str(), reg_wires.count(wire->name) ? "reg" : "wire");
	if (wire->width != 1)
		fprintf(f, "[%d:%d] ", wire->width - 1 + wire->start_offset, wire->start_offset);
	fprintf(f, "%s;\n", id(wire->name).c_str());
#else
	// do not use Verilog-2k "outut reg" syntax in verilog export
	std::string range = "";
	if (wire->width != 1)
		range = stringf(" [%d:%d]", wire->width - 1 + wire->start_offset, wire->start_offset);
	if (wire->port_input && !wire->port_output)
		fprintf(f, "%s" "input%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
	if (!wire->port_input && wire->port_output)
		fprintf(f, "%s" "output%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
	if (wire->port_input && wire->port_output)
		fprintf(f, "%s" "inout%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
	if (reg_wires.count(wire->name))
		fprintf(f, "%s" "reg%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
	else if (!wire->port_input && !wire->port_output)
		fprintf(f, "%s" "wire%s %s;\n", indent.c_str(), range.c_str(), id(wire->name).c_str());
#endif
}

void dump_memory(FILE *f, std::string indent, RTLIL::Memory *memory)
{
	dump_attributes(f, indent, memory->attributes);
	fprintf(f, "%s" "reg [%d:0] %s [%d:0];\n", indent.c_str(), memory->width-1, id(memory->name).c_str(), memory->size-1);
}

void dump_cell_expr_port(FILE *f, RTLIL::Cell *cell, std::string port, bool gen_signed = true)
{
	if (gen_signed && cell->parameters.count("\\" + port + "_SIGNED") > 0 && cell->parameters["\\" + port + "_SIGNED"].as_bool()) {
		fprintf(f, "$signed(");
		dump_sigspec(f, cell->get("\\" + port));
		fprintf(f, ")");
	} else
		dump_sigspec(f, cell->get("\\" + port));
}

std::string cellname(RTLIL::Cell *cell)
{
	if (!norename && cell->name[0] == '$' && reg_ct.cell_known(cell->type) && cell->has("\\Q"))
	{
		RTLIL::SigSpec sig = cell->get("\\Q");
		if (SIZE(sig) != 1 || sig.is_fully_const())
			goto no_special_reg_name;

		RTLIL::Wire *wire = sig[0].wire;

		if (wire->name[0] != '\\')
			goto no_special_reg_name;

		std::string cell_name = wire->name;

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

void dump_cell_expr_uniop(FILE *f, std::string indent, RTLIL::Cell *cell, std::string op)
{
	fprintf(f, "%s" "assign ", indent.c_str());
	dump_sigspec(f, cell->get("\\Y"));
	fprintf(f, " = %s ", op.c_str());
	dump_attributes(f, "", cell->attributes, ' ');
	dump_cell_expr_port(f, cell, "A", true);
	fprintf(f, ";\n");
}

void dump_cell_expr_binop(FILE *f, std::string indent, RTLIL::Cell *cell, std::string op)
{
	fprintf(f, "%s" "assign ", indent.c_str());
	dump_sigspec(f, cell->get("\\Y"));
	fprintf(f, " = ");
	dump_cell_expr_port(f, cell, "A", true);
	fprintf(f, " %s ", op.c_str());
	dump_attributes(f, "", cell->attributes, ' ');
	dump_cell_expr_port(f, cell, "B", true);
	fprintf(f, ";\n");
}

bool dump_cell_expr(FILE *f, std::string indent, RTLIL::Cell *cell)
{
	if (cell->type == "$_INV_") {
		fprintf(f, "%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->get("\\Y"));
		fprintf(f, " = ");
		fprintf(f, "~");
		dump_attributes(f, "", cell->attributes, ' ');
		dump_cell_expr_port(f, cell, "A", false);
		fprintf(f, ";\n");
		return true;
	}

	if (cell->type == "$_AND_" || cell->type == "$_OR_" || cell->type == "$_XOR_") {
		fprintf(f, "%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->get("\\Y"));
		fprintf(f, " = ");
		dump_cell_expr_port(f, cell, "A", false);
		fprintf(f, " ");
		if (cell->type == "$_AND_")
			fprintf(f, "&");
		if (cell->type == "$_OR_")
			fprintf(f, "|");
		if (cell->type == "$_XOR_")
			fprintf(f, "^");
		dump_attributes(f, "", cell->attributes, ' ');
		fprintf(f, " ");
		dump_cell_expr_port(f, cell, "B", false);
		fprintf(f, ";\n");
		return true;
	}

	if (cell->type == "$_MUX_") {
		fprintf(f, "%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->get("\\Y"));
		fprintf(f, " = ");
		dump_cell_expr_port(f, cell, "S", false);
		fprintf(f, " ? ");
		dump_attributes(f, "", cell->attributes, ' ');
		dump_cell_expr_port(f, cell, "B", false);
		fprintf(f, " : ");
		dump_cell_expr_port(f, cell, "A", false);
		fprintf(f, ";\n");
		return true;
	}

	if (cell->type.substr(0, 6) == "$_DFF_")
	{
		std::string reg_name = cellname(cell);
		bool out_is_reg_wire = is_reg_wire(cell->get("\\Q"), reg_name);

		if (!out_is_reg_wire)
			fprintf(f, "%s" "reg %s;\n", indent.c_str(), reg_name.c_str());

		dump_attributes(f, indent, cell->attributes);
		fprintf(f, "%s" "always @(%sedge ", indent.c_str(), cell->type[6] == 'P' ? "pos" : "neg");
		dump_sigspec(f, cell->get("\\C"));
		if (cell->type[7] != '_') {
			fprintf(f, " or %sedge ", cell->type[7] == 'P' ? "pos" : "neg");
			dump_sigspec(f, cell->get("\\R"));
		}
		fprintf(f, ")\n");

		if (cell->type[7] != '_') {
			fprintf(f, "%s" "  if (%s", indent.c_str(), cell->type[7] == 'P' ? "" : "!");
			dump_sigspec(f, cell->get("\\R"));
			fprintf(f, ")\n");
			fprintf(f, "%s" "    %s <= %c;\n", indent.c_str(), reg_name.c_str(), cell->type[8]);
			fprintf(f, "%s" "  else\n", indent.c_str());
		}

		fprintf(f, "%s" "    %s <= ", indent.c_str(), reg_name.c_str());
		dump_cell_expr_port(f, cell, "D", false);
		fprintf(f, ";\n");

		if (!out_is_reg_wire) {
			fprintf(f, "%s" "assign ", indent.c_str());
			dump_sigspec(f, cell->get("\\Q"));
			fprintf(f, " = %s;\n", reg_name.c_str());
		}

		return true;
	}

	if (cell->type.substr(0, 8) == "$_DFFSR_")
	{
		char pol_c = cell->type[8], pol_s = cell->type[9], pol_r = cell->type[10];

		std::string reg_name = cellname(cell);
		bool out_is_reg_wire = is_reg_wire(cell->get("\\Q"), reg_name);

		if (!out_is_reg_wire)
			fprintf(f, "%s" "reg %s;\n", indent.c_str(), reg_name.c_str());

		dump_attributes(f, indent, cell->attributes);
		fprintf(f, "%s" "always @(%sedge ", indent.c_str(), pol_c == 'P' ? "pos" : "neg");
		dump_sigspec(f, cell->get("\\C"));
		fprintf(f, " or %sedge ", pol_s == 'P' ? "pos" : "neg");
		dump_sigspec(f, cell->get("\\S"));
		fprintf(f, " or %sedge ", pol_r == 'P' ? "pos" : "neg");
		dump_sigspec(f, cell->get("\\R"));
		fprintf(f, ")\n");

		fprintf(f, "%s" "  if (%s", indent.c_str(), pol_r == 'P' ? "" : "!");
		dump_sigspec(f, cell->get("\\R"));
		fprintf(f, ")\n");
		fprintf(f, "%s" "    %s <= 0;\n", indent.c_str(), reg_name.c_str());

		fprintf(f, "%s" "  else if (%s", indent.c_str(), pol_s == 'P' ? "" : "!");
		dump_sigspec(f, cell->get("\\S"));
		fprintf(f, ")\n");
		fprintf(f, "%s" "    %s <= 1;\n", indent.c_str(), reg_name.c_str());

		fprintf(f, "%s" "  else\n", indent.c_str());
		fprintf(f, "%s" "    %s <= ", indent.c_str(), reg_name.c_str());
		dump_cell_expr_port(f, cell, "D", false);
		fprintf(f, ";\n");

		if (!out_is_reg_wire) {
			fprintf(f, "%s" "assign ", indent.c_str());
			dump_sigspec(f, cell->get("\\Q"));
			fprintf(f, " = %s;\n", reg_name.c_str());
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

	if (cell->type == "$mux" || cell->type == "$pmux" || cell->type == "$pmux_safe")
	{
		int width = cell->parameters["\\WIDTH"].as_int();
		int s_width = cell->get("\\S").size();
		std::string func_name = cellname(cell);

		fprintf(f, "%s" "function [%d:0] %s;\n", indent.c_str(), width-1, func_name.c_str());
		fprintf(f, "%s" "  input [%d:0] a;\n", indent.c_str(), width-1);
		fprintf(f, "%s" "  input [%d:0] b;\n", indent.c_str(), s_width*width-1);
		fprintf(f, "%s" "  input [%d:0] s;\n", indent.c_str(), s_width-1);

		dump_attributes(f, indent + "  ", cell->attributes);
		if (!noattr)
			fprintf(f, "%s" "  (* parallel_case *)\n", indent.c_str());
		fprintf(f, "%s" "  casez (s)", indent.c_str());
		fprintf(f, noattr ? " // synopsys parallel_case\n" : "\n");

		for (int i = 0; i < s_width; i++)
		{
			fprintf(f, "%s" "    %d'b", indent.c_str(), s_width);

			for (int j = s_width-1; j >= 0; j--)
				fprintf(f, "%c", j == i ? '1' : cell->type == "$pmux_safe" ? '0' : '?');

			fprintf(f, ":\n");
			fprintf(f, "%s" "      %s = b[%d:%d];\n", indent.c_str(), func_name.c_str(), (i+1)*width-1, i*width);
		}

		fprintf(f, "%s" "    default:\n", indent.c_str());
		fprintf(f, "%s" "      %s = a;\n", indent.c_str(), func_name.c_str());

		fprintf(f, "%s" "  endcase\n", indent.c_str());
		fprintf(f, "%s" "endfunction\n", indent.c_str());

		fprintf(f, "%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->get("\\Y"));
		fprintf(f, " = %s(", func_name.c_str());
		dump_sigspec(f, cell->get("\\A"));
		fprintf(f, ", ");
		dump_sigspec(f, cell->get("\\B"));
		fprintf(f, ", ");
		dump_sigspec(f, cell->get("\\S"));
		fprintf(f, ");\n");
		return true;
	}

	if (cell->type == "$slice")
	{
		fprintf(f, "%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->get("\\Y"));
		fprintf(f, " = ");
		dump_sigspec(f, cell->get("\\A"));
		fprintf(f, " >> %d;\n", cell->parameters.at("\\OFFSET").as_int());
		return true;
	}

	if (cell->type == "$bu0")
	{
		fprintf(f, "%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->get("\\Y"));
		if (cell->parameters["\\A_SIGNED"].as_bool()) {
			fprintf(f, " = $signed(");
			dump_sigspec(f, cell->get("\\A"));
			fprintf(f, ");\n");
		} else {
			fprintf(f, " = { 1'b0, ");
			dump_sigspec(f, cell->get("\\A"));
			fprintf(f, " };\n");
		}
		return true;
	}

	if (cell->type == "$concat")
	{
		fprintf(f, "%s" "assign ", indent.c_str());
		dump_sigspec(f, cell->get("\\Y"));
		fprintf(f, " = { ");
		dump_sigspec(f, cell->get("\\B"));
		fprintf(f, " , ");
		dump_sigspec(f, cell->get("\\A"));
		fprintf(f, " };\n");
		return true;
	}

	if (cell->type == "$dff" || cell->type == "$adff")
	{
		RTLIL::SigSpec sig_clk, sig_arst, val_arst;
		bool pol_clk, pol_arst = false;

		sig_clk = cell->get("\\CLK");
		pol_clk = cell->parameters["\\CLK_POLARITY"].as_bool();

		if (cell->type == "$adff") {
			sig_arst = cell->get("\\ARST");
			pol_arst = cell->parameters["\\ARST_POLARITY"].as_bool();
			val_arst = RTLIL::SigSpec(cell->parameters["\\ARST_VALUE"]);
		}

		std::string reg_name = cellname(cell);
		bool out_is_reg_wire = is_reg_wire(cell->get("\\Q"), reg_name);

		if (!out_is_reg_wire)
			fprintf(f, "%s" "reg [%d:0] %s;\n", indent.c_str(), cell->parameters["\\WIDTH"].as_int()-1, reg_name.c_str());

		fprintf(f, "%s" "always @(%sedge ", indent.c_str(), pol_clk ? "pos" : "neg");
		dump_sigspec(f, sig_clk);
		if (cell->type == "$adff") {
			fprintf(f, " or %sedge ", pol_arst ? "pos" : "neg");
			dump_sigspec(f, sig_arst);
		}
		fprintf(f, ")\n");

		if (cell->type == "$adff") {
			fprintf(f, "%s" "  if (%s", indent.c_str(), pol_arst ? "" : "!");
			dump_sigspec(f, sig_arst);
			fprintf(f, ")\n");
			fprintf(f, "%s" "    %s <= ", indent.c_str(), reg_name.c_str());
			dump_sigspec(f, val_arst);
			fprintf(f, ";\n");
			fprintf(f, "%s" "  else\n", indent.c_str());
		}

		fprintf(f, "%s" "    %s <= ", indent.c_str(), reg_name.c_str());
		dump_cell_expr_port(f, cell, "D", false);
		fprintf(f, ";\n");

		if (!out_is_reg_wire) {
			fprintf(f, "%s" "assign ", indent.c_str());
			dump_sigspec(f, cell->get("\\Q"));
			fprintf(f, " = %s;\n", reg_name.c_str());
		}

		return true;
	}

	// FIXME: $_SR_[PN][PN]_, $_DLATCH_[PN]_
	// FIXME: $sr, $dffsr, $dlatch, $memrd, $memwr, $mem, $fsm

	return false;
}

void dump_cell(FILE *f, std::string indent, RTLIL::Cell *cell)
{
	if (cell->type[0] == '$' && !noexpr) {
		if (dump_cell_expr(f, indent, cell))
			return;
	}

	dump_attributes(f, indent, cell->attributes);
	fprintf(f, "%s" "%s", indent.c_str(), id(cell->type, false).c_str());

	if (cell->parameters.size() > 0) {
		fprintf(f, " #(");
		for (auto it = cell->parameters.begin(); it != cell->parameters.end(); it++) {
			if (it != cell->parameters.begin())
				fprintf(f, ",");
			fprintf(f, "\n%s  .%s(", indent.c_str(), id(it->first).c_str());
			bool is_signed = (it->second.flags & RTLIL::CONST_FLAG_SIGNED) != 0;
			dump_const(f, it->second, -1, 0, !is_signed, is_signed);
			fprintf(f, ")");
		}
		fprintf(f, "\n%s" ")", indent.c_str());
	}

	std::string cell_name = cellname(cell);
	if (cell_name != id(cell->name))
		fprintf(f, " %s /* %s */ (", cell_name.c_str(), id(cell->name).c_str());
	else
		fprintf(f, " %s (", cell_name.c_str());

	bool first_arg = true;
	std::set<std::string> numbered_ports;
	for (int i = 1; true; i++) {
		char str[16];
		snprintf(str, 16, "$%d", i);
		for (auto it = cell->connections().begin(); it != cell->connections().end(); it++) {
			if (it->first != str)
				continue;
			if (!first_arg)
				fprintf(f, ",");
			first_arg = false;
			fprintf(f, "\n%s  ", indent.c_str());
			dump_sigspec(f, it->second);
			numbered_ports.insert(it->first);
			goto found_numbered_port;
		}
		break;
	found_numbered_port:;
	}
	for (auto it = cell->connections().begin(); it != cell->connections().end(); it++) {
		if (numbered_ports.count(it->first))
			continue;
		if (!first_arg)
			fprintf(f, ",");
		first_arg = false;
		fprintf(f, "\n%s  .%s(", indent.c_str(), id(it->first).c_str());
		if (it->second.size() > 0)
			dump_sigspec(f, it->second);
		fprintf(f, ")");
	}
	fprintf(f, "\n%s" ");\n", indent.c_str());
}

void dump_conn(FILE *f, std::string indent, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right)
{
	fprintf(f, "%s" "assign ", indent.c_str());
	dump_sigspec(f, left);
	fprintf(f, " = ");
	dump_sigspec(f, right);
	fprintf(f, ";\n");
}

void dump_proc_switch(FILE *f, std::string indent, RTLIL::SwitchRule *sw);

void dump_case_body(FILE *f, std::string indent, RTLIL::CaseRule *cs, bool omit_trailing_begin = false)
{
	int number_of_stmts = cs->switches.size() + cs->actions.size();

	if (!omit_trailing_begin && number_of_stmts >= 2)
		fprintf(f, "%s" "begin\n", indent.c_str());

	for (auto it = cs->actions.begin(); it != cs->actions.end(); it++) {
		if (it->first.size() == 0)
			continue;
		fprintf(f, "%s  ", indent.c_str());
		dump_sigspec(f, it->first);
		fprintf(f, " = ");
		dump_sigspec(f, it->second);
		fprintf(f, ";\n");
	}

	for (auto it = cs->switches.begin(); it != cs->switches.end(); it++)
		dump_proc_switch(f, indent + "  ", *it);

	if (!omit_trailing_begin && number_of_stmts == 0)
		fprintf(f, "%s  /* empty */;\n", indent.c_str());

	if (omit_trailing_begin || number_of_stmts >= 2)
		fprintf(f, "%s" "end\n", indent.c_str());
}

void dump_proc_switch(FILE *f, std::string indent, RTLIL::SwitchRule *sw)
{
	if (sw->signal.size() == 0) {
		fprintf(f, "%s" "begin\n", indent.c_str());
		for (auto it = sw->cases.begin(); it != sw->cases.end(); it++) {
			if ((*it)->compare.size() == 0)
				dump_case_body(f, indent + "  ", *it);
		}
		fprintf(f, "%s" "end\n", indent.c_str());
		return;
	}

	fprintf(f, "%s" "casez (", indent.c_str());
	dump_sigspec(f, sw->signal);
	fprintf(f, ")\n");

	for (auto it = sw->cases.begin(); it != sw->cases.end(); it++) {
		fprintf(f, "%s  ", indent.c_str());
		if ((*it)->compare.size() == 0)
			fprintf(f, "default");
		else {
			for (size_t i = 0; i < (*it)->compare.size(); i++) {
				if (i > 0)
					fprintf(f, ", ");
				dump_sigspec(f, (*it)->compare[i]);
			}
		}
		fprintf(f, ":\n");
		dump_case_body(f, indent + "    ", *it);
	}

	fprintf(f, "%s" "endcase\n", indent.c_str());
}

void case_body_find_regs(RTLIL::CaseRule *cs)
{
	for (auto it = cs->switches.begin(); it != cs->switches.end(); it++)
	for (auto it2 = (*it)->cases.begin(); it2 != (*it)->cases.end(); it2++)
		case_body_find_regs(*it2);

	for (auto it = cs->actions.begin(); it != cs->actions.end(); it++) {
		for (auto &c : it->first.chunks())
			if (c.wire != NULL)
				reg_wires.insert(c.wire->name);
	}
}

void dump_process(FILE *f, std::string indent, RTLIL::Process *proc, bool find_regs = false)
{
	if (find_regs) {
		case_body_find_regs(&proc->root_case);
		for (auto it = proc->syncs.begin(); it != proc->syncs.end(); it++)
		for (auto it2 = (*it)->actions.begin(); it2 != (*it)->actions.end(); it2++) {
			for (auto &c : it2->first.chunks())
				if (c.wire != NULL)
					reg_wires.insert(c.wire->name);
		}
		return;
	}

	fprintf(f, "%s" "always @* begin\n", indent.c_str());
	dump_case_body(f, indent, &proc->root_case, true);

	std::string backup_indent = indent;

	for (size_t i = 0; i < proc->syncs.size(); i++)
	{
		RTLIL::SyncRule *sync = proc->syncs[i];
		indent = backup_indent;

		if (sync->type == RTLIL::STa) {
			fprintf(f, "%s" "always @* begin\n", indent.c_str());
		} else {
			fprintf(f, "%s" "always @(", indent.c_str());
			if (sync->type == RTLIL::STp || sync->type == RTLIL::ST1)
				fprintf(f, "posedge ");
			if (sync->type == RTLIL::STn || sync->type == RTLIL::ST0)
				fprintf(f, "negedge ");
			dump_sigspec(f, sync->signal);
			fprintf(f, ") begin\n");
		}
		std::string ends = indent + "end\n";
		indent += "  ";

		if (sync->type == RTLIL::ST0 || sync->type == RTLIL::ST1) {
			fprintf(f, "%s" "if (%s", indent.c_str(), sync->type == RTLIL::ST0 ? "!" : "");
			dump_sigspec(f, sync->signal);
			fprintf(f, ") begin\n");
			ends = indent + "end\n" + ends;
			indent += "  ";
		}

		if (sync->type == RTLIL::STp || sync->type == RTLIL::STn) {
			for (size_t j = 0; j < proc->syncs.size(); j++) {
				RTLIL::SyncRule *sync2 = proc->syncs[j];
				if (sync2->type == RTLIL::ST0 || sync2->type == RTLIL::ST1) {
					fprintf(f, "%s" "if (%s", indent.c_str(), sync2->type == RTLIL::ST1 ? "!" : "");
					dump_sigspec(f, sync2->signal);
					fprintf(f, ") begin\n");
					ends = indent + "end\n" + ends;
					indent += "  ";
				}
			}
		}

		for (auto it = sync->actions.begin(); it != sync->actions.end(); it++) {
			if (it->first.size() == 0)
				continue;
			fprintf(f, "%s  ", indent.c_str());
			dump_sigspec(f, it->first);
			fprintf(f, " <= ");
			dump_sigspec(f, it->second);
			fprintf(f, ";\n");
		}

		fprintf(f, "%s", ends.c_str());
	}
}

void dump_module(FILE *f, std::string indent, RTLIL::Module *module)
{
	reg_wires.clear();
	reset_auto_counter(module);
	active_module = module;

	fprintf(f, "\n");
	for (auto it = module->processes.begin(); it != module->processes.end(); it++)
		dump_process(f, indent + "  ", it->second, true);

	if (!noexpr)
	{
		std::set<std::pair<RTLIL::Wire*,int>> reg_bits;
		for (auto &it : module->cells)
		{
			RTLIL::Cell *cell = it.second;
			if (!reg_ct.cell_known(cell->type) || !cell->has("\\Q"))
				continue;

			RTLIL::SigSpec sig = cell->get("\\Q");

			if (sig.is_chunk()) {
				RTLIL::SigChunk chunk = sig.as_chunk();
				if (chunk.wire != NULL)
					for (int i = 0; i < chunk.width; i++)
						reg_bits.insert(std::pair<RTLIL::Wire*,int>(chunk.wire, chunk.offset+i));
			}
		}
		for (auto &it : module->wires)
		{
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				if (reg_bits.count(std::pair<RTLIL::Wire*,int>(wire, i)) == 0)
					goto this_wire_aint_reg;
			reg_wires.insert(wire->name);
		this_wire_aint_reg:;
		}
	}

	dump_attributes(f, indent, module->attributes);
	fprintf(f, "%s" "module %s(", indent.c_str(), id(module->name, false).c_str());
	bool keep_running = true;
	for (int port_id = 1; keep_running; port_id++) {
		keep_running = false;
		for (auto it = module->wires.begin(); it != module->wires.end(); it++) {
			RTLIL::Wire *wire = it->second;
			if (wire->port_id == port_id) {
				if (port_id != 1)
					fprintf(f, ", ");
				fprintf(f, "%s", id(wire->name).c_str());
				keep_running = true;
				continue;
			}
		}
	}
	fprintf(f, ");\n");

	for (auto it = module->wires.begin(); it != module->wires.end(); it++)
		dump_wire(f, indent + "  ", it->second);

	for (auto it = module->memories.begin(); it != module->memories.end(); it++)
		dump_memory(f, indent + "  ", it->second);

	for (auto it = module->cells.begin(); it != module->cells.end(); it++)
		dump_cell(f, indent + "  ", it->second);

	for (auto it = module->processes.begin(); it != module->processes.end(); it++)
		dump_process(f, indent + "  ", it->second);

	for (auto it = module->connections().begin(); it != module->connections().end(); it++)
		dump_conn(f, indent + "  ", it->first, it->second);

	fprintf(f, "%s" "endmodule\n", indent.c_str());
	active_module = NULL;
}

} /* namespace */

struct VerilogBackend : public Backend {
	VerilogBackend() : Backend("verilog", "write design to verilog file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_verilog [options] [filename]\n");
		log("\n");
		log("Write the current design to a verilog file.\n");
		log("\n");
		log("    -norename\n");
		log("        without this option all internal object names (the ones with a dollar\n");
		log("        instead of a backslash prefix) are changed to short names in the\n");
		log("        format '_<number>_'.\n");
		log("\n");
		log("    -noattr\n");
		log("        with this option no attributes are included in the output\n");
		log("\n");
		log("    -attr2comment\n");
		log("        with this option attributes are included as comments in the output\n");
		log("\n");
		log("    -noexpr\n");
		log("        without this option all internal cells are converted to verilog\n");
		log("        expressions.\n");
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
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing Verilog backend.\n");

		norename = false;
		noattr = false;
		attr2comment = false;
		noexpr = false;

		bool blackboxes = false;
		bool selected = false;

		reg_ct.clear();
		reg_ct.setup_stdcells_mem();
		reg_ct.cell_types.insert("$sr");
		reg_ct.cell_types.insert("$dff");
		reg_ct.cell_types.insert("$adff");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-norename") {
				norename = true;
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
			if (arg == "-blackboxes") {
				blackboxes = true;
				continue;
			}
			if (arg == "-selected") {
				selected = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		fprintf(f, "/* Generated by %s */\n", yosys_version_str);
		for (auto it = design->modules.begin(); it != design->modules.end(); it++) {
			if (it->second->get_bool_attribute("\\blackbox") != blackboxes)
				continue;
			if (selected && !design->selected_whole_module(it->first)) {
				if (design->selected_module(it->first))
					log_cmd_error("Can't handle partially selected module %s!\n", RTLIL::id2cstr(it->first));
				continue;
			}
			log("Dumping module `%s'.\n", it->first.c_str());
			dump_module(f, "", it->second);
		}

		reg_ct.clear();
	}
} VerilogBackend;

