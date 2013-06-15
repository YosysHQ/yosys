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

#include "vlparse.h"
#include "kernel/log.h"
#include <stdio.h>
#include <string>

static int lex_line, lex_tok;
static std::string lex_str;

static int token(int tok)
{
	lex_tok = tok;
#if 0
	if (lex_tok == 256)
		fprintf(stderr, "STR in line %d: >>%s<<\n", lex_line, lex_str.c_str());
	else if (tok >= 32 && tok < 255)
		fprintf(stderr, "CHAR in line %d: >>%c<<\n", lex_line, lex_tok);
	else
		fprintf(stderr, "CHAR in line %d: %d\n", lex_line, lex_tok);
#endif
	return tok;
}

static int lex(FILE *f)
{
	int ch = getc(f);

	while (ch == ' ' || ch == '\t' || ch == '\n') {
		if (ch == '\n')
			lex_line++;
		ch = getc(f);
	}

	if (ch <= 0 || 255 < ch)
		return token(lex_tok);
	
	if (('a' <= ch && ch <= 'z') || ('A' <= ch && ch <= 'Z') ||
			('0' <= ch && ch <= '9') || ch == '_' || ch == '\'') {
		lex_str = char(ch);
		while (1) {
			ch = getc(f);
			if (('a' <= ch && ch <= 'z') || ('A' <= ch && ch <= 'Z') ||
					('0' <= ch && ch <= '9') || ch == '_' || ch == '\'') {
				lex_str += char(ch);
				continue;
			}
			break;
		}
		ungetc(ch, f);
		return token(256);
	}

	if (ch == '/') {
		ch = getc(f);
		if (ch == '/') {
			while (ch != '\n')
				ch = getc(f);
			ungetc(ch, f);
			return lex(f);
		}
		ungetc(ch, f);
		return token('/');
	}

	return token(ch);
}

RTLIL::Design *abc_parse_verilog(FILE *f)
{
	RTLIL::Design *design = new RTLIL::Design;
	RTLIL::Module *module;
	RTLIL::Wire *wire;
	RTLIL::Cell *cell;

	int port_count = 1;
	lex_line = 1;

	// parse module header
	if (lex(f) != 256 || lex_str != "module")
		goto error;
	if (lex(f) != 256)
		goto error;

	module = new RTLIL::Module;
	module->name = "\\" + lex_str;
	design->modules[module->name] = module;

	if (lex(f) != '(')
		goto error;
	while (lex(f) != ')') {
		if (lex_tok != 256 && lex_tok != ',')
			goto error;
	}
	if (lex(f) != ';')
		goto error;

	// parse module body
	while (1)
	{
		if (lex(f) != 256)
			goto error;

		if (lex_str == "endmodule")
			return design;

		if (lex_str == "input" || lex_str == "output" || lex_str == "wire")
		{
			std::string mode = lex_str;
			while (lex(f) != ';') {
				if (lex_tok != 256 && lex_tok != ',')
					goto error;
				if (lex_tok == 256) {
					// printf("%s [%s]\n", mode.c_str(), lex_str.c_str());
					wire = new RTLIL::Wire;
					wire->name = "\\" + lex_str;
					if (mode == "input") {
						wire->port_id = port_count++;
						wire->port_input = true;
					}
					if (mode == "output") {
						wire->port_id = port_count++;
						wire->port_output = true;
					}
					module->wires[wire->name] = wire;
				}
			}
		}
		else if (lex_str == "assign")
		{
			std::string lhs, rhs;

			if (lex(f) != 256)
				goto error;
			lhs = lex_str;

			if (lex(f) != '=')
				goto error;
			if (lex(f) != 256)
				goto error;
			rhs = lex_str;

			if (lex(f) != ';')
				goto error;

			if (module->wires.count(RTLIL::escape_id(lhs)) == 0)
				goto error;

			if (rhs == "1'b0")
				module->connections.push_back(RTLIL::SigSig(module->wires.at(RTLIL::escape_id(lhs)), RTLIL::SigSpec(0, 1)));
			else if (rhs == "1'b1")
				module->connections.push_back(RTLIL::SigSig(module->wires.at(RTLIL::escape_id(lhs)), RTLIL::SigSpec(1, 1)));
			else if (module->wires.count(RTLIL::escape_id(rhs)) > 0)
				module->connections.push_back(RTLIL::SigSig(module->wires.at(RTLIL::escape_id(lhs)), module->wires.at(RTLIL::escape_id(rhs))));
			else
				goto error;
		}
		else
		{
			std::string cell_type = lex_str;

			if (lex(f) != 256)
				goto error;

			std::string cell_name = lex_str;

			if (lex(f) != '(')
				goto error;

			// printf("cell [%s] [%s]\n", cell_type.c_str(), cell_name.c_str());
			cell = new RTLIL::Cell;
			cell->type = "\\" + cell_type;
			cell->name = "\\" + cell_name;
			module->cells[cell->name] = cell;

			lex(f);
			while (lex_tok != ')')
			{
				if (lex_tok != '.' || lex(f) != 256)
					goto error;

				std::string cell_port = lex_str;

				if (lex(f) != '(' || lex(f) != 256)
					goto error;

				std::string wire_name = lex_str;

				// printf("  [%s] <- [%s]\n", cell_port.c_str(), wire_name.c_str());
				if (module->wires.count("\\" + wire_name) == 0)
					goto error;
				cell->connections["\\" + cell_port] = RTLIL::SigSpec(module->wires["\\" + wire_name]);

				if (lex(f) != ')' || (lex(f) != ',' && lex_tok != ')'))
					goto error;
				while (lex_tok == ',')
					lex(f);
			}

			if (lex(f) != ';')
				goto error;
		}
	}

error:
	log_error("Syntax error in line %d!\n", lex_line);
	// delete design;
	// return NULL;
}

