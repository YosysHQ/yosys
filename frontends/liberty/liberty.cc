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

#include "passes/techmap/libparse.h"
#include "kernel/register.h"
#include "kernel/log.h"

using namespace PASS_DFFLIBMAP;

struct token_t {
	char type;
	RTLIL::SigSpec sig;
	token_t (char t) : type(t) { }
	token_t (char t, RTLIL::SigSpec s) : type(t), sig(s) { }
};

static RTLIL::SigSpec parse_func_identifier(RTLIL::Module *module, const char *&expr)
{
	log_assert(*expr != 0);

	int id_len = 0;
	while (('a' <= expr[id_len] && expr[id_len] <= 'z') || ('A' <= expr[id_len] && expr[id_len] <= 'Z') ||
			('0' <= expr[id_len] && expr[id_len] <= '9') || expr[id_len] == '.' || expr[id_len] == '_') id_len++;

	if (id_len == 0)
		log_error("Expected identifier at `%s'.\n", expr);
	
	if (id_len == 1 && (*expr == '0' || *expr == '1'))
		return *(expr++) == '0' ? RTLIL::State::S0 : RTLIL::State::S1;

	std::string id = RTLIL::escape_id(std::string(expr, id_len));
	if (!module->wires.count(id))
		log_error("Can't resolve wire name %s.\n", RTLIL::id2cstr(id));

	expr += id_len;
	return module->wires.at(id);
}

static RTLIL::SigSpec create_inv_cell(RTLIL::Module *module, RTLIL::SigSpec A)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = NEW_ID;
	cell->type = "$_INV_";
	cell->connections["\\A"] = A;
	cell->connections["\\Y"] = NEW_WIRE(module, 1);
	module->add(cell);
	return cell->connections["\\Y"];
}

static RTLIL::SigSpec create_xor_cell(RTLIL::Module *module, RTLIL::SigSpec A, RTLIL::SigSpec B)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = NEW_ID;
	cell->type = "$_XOR_";
	cell->connections["\\A"] = A;
	cell->connections["\\B"] = B;
	cell->connections["\\Y"] = NEW_WIRE(module, 1);
	module->add(cell);
	return cell->connections["\\Y"];
}

static RTLIL::SigSpec create_and_cell(RTLIL::Module *module, RTLIL::SigSpec A, RTLIL::SigSpec B)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = NEW_ID;
	cell->type = "$_AND_";
	cell->connections["\\A"] = A;
	cell->connections["\\B"] = B;
	cell->connections["\\Y"] = NEW_WIRE(module, 1);
	module->add(cell);
	return cell->connections["\\Y"];
}

static RTLIL::SigSpec create_or_cell(RTLIL::Module *module, RTLIL::SigSpec A, RTLIL::SigSpec B)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = NEW_ID;
	cell->type = "$_OR_";
	cell->connections["\\A"] = A;
	cell->connections["\\B"] = B;
	cell->connections["\\Y"] = NEW_WIRE(module, 1);
	module->add(cell);
	return cell->connections["\\Y"];
}

static bool parse_func_reduce(RTLIL::Module *module, std::vector<token_t> &stack, token_t next_token)
{
	int top = int(stack.size())-1;

	if (0 <= top-1 && stack[top].type == 0 && stack[top-1].type == '!') {
		token_t t = token_t(0, create_inv_cell(module, stack[top].sig));
		stack.pop_back();
		stack.pop_back();
		stack.push_back(t);
		return true;
	}

	if (0 <= top-1 && stack[top].type == '\'' && stack[top-1].type == 0) {
		token_t t = token_t(0, create_inv_cell(module, stack[top-1].sig));
		stack.pop_back();
		stack.pop_back();
		stack.push_back(t);
		return true;
	}

	if (0 <= top && stack[top].type == 0) {
		if (next_token.type == '\'')
			return false;
		stack[top].type = 1;
		return true;
	}

	if (0 <= top-2 && stack[top-2].type == 1 && stack[top-1].type == '^' && stack[top].type == 1) {
		token_t t = token_t(1, create_xor_cell(module, stack[top-2].sig, stack[top].sig));
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(t);
		return true;
	}

	if (0 <= top && stack[top].type == 1) {
		if (next_token.type == '^')
			return false;
		stack[top].type = 2;
		return true;
	}

	if (0 <= top-1 && stack[top-1].type == 2 && stack[top].type == 2) {
		token_t t = token_t(2, create_and_cell(module, stack[top-2].sig, stack[top].sig));
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(t);
		return true;
	}

	if (0 <= top-2 && stack[top-2].type == 2 && (stack[top-1].type == '*' || stack[top-1].type == '&') && stack[top].type == 2) {
		token_t t = token_t(2, create_and_cell(module, stack[top-2].sig, stack[top].sig));
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(t);
		return true;
	}

	if (0 <= top && stack[top].type == 2) {
		if (next_token.type == '*' || next_token.type == '&' || next_token.type == 0)
			return false;
		stack[top].type = 3;
		return true;
	}

	if (0 <= top-2 && stack[top-2].type == 3 && (stack[top-1].type == '+' || stack[top-1].type == '|') && stack[top].type == 3) {
		token_t t = token_t(3, create_or_cell(module, stack[top-2].sig, stack[top].sig));
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(t);
		return true;
	}

	if (0 <= top-2 && stack[top-2].type == '(' && stack[top-1].type == 3 && stack[top].type == ')') {
		token_t t = token_t(0, stack[top-1].sig);
		stack.pop_back();
		stack.pop_back();
		stack.pop_back();
		stack.push_back(t);
		return true;
	}

	return false;
}

static RTLIL::SigSpec parse_func_expr(RTLIL::Module *module, const char *expr)
{
	const char *orig_expr = expr;
	std::vector<token_t> stack;

	while (*expr)
	{
		if (*expr == ' ' || *expr == '\t' || *expr == '\r' || *expr == '\n' || *expr == '"') {
			expr++;
			continue;
		}

		token_t next_token(0);
		if (*expr == '(' || *expr == ')' || *expr == '\'' || *expr == '!' || *expr == '^' || *expr == '*' || *expr == '+' || *expr == '|')
			next_token = token_t(*(expr++));
		else
			next_token = token_t(0, parse_func_identifier(module, expr));

		while (parse_func_reduce(module, stack, next_token)) {}
		stack.push_back(next_token);
	}

	while (parse_func_reduce(module, stack, token_t('.'))) {}

#if 0
	for (size_t i = 0; i < stack.size(); i++)
		if (stack[i].type < 16)
			log("%3d: %d %s\n", int(i), stack[i].type, log_signal(stack[i].sig));
		else
			log("%3d: %c\n", int(i), stack[i].type);
#endif

	if (stack.size() != 1 || stack.back().type != 3)
		log_error("Parser error in function expr `%s'.\n", orig_expr);

	return stack.back().sig;
}

struct LibertyFrontend : public Frontend {
	LibertyFrontend() : Frontend("liberty", "read cells from liberty file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read_liberty [filename]\n");
		log("\n");
		log("Read cells from liberty file as modules into current design.\n");
		log("\n");
		log("    -lib\n");
		log("        only create empty blackbox modules\n");
		log("\n");
		log("    -ignore_redef\n");
		log("        ignore re-definitions of modules. (the default behavior is to\n");
		log("        create an error message.)\n");
		log("\n");
		log("    -setattr <attribute_name>\n");
		log("        set the specified attribute (to the value 1) on all loaded modules\n");
		log("\n");
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_lib = false;
		bool flag_ignore_redef = false;
		std::vector<std::string> attributes;

		log_header("Executing Liberty frontend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-lib") {
				flag_lib = true;
				continue;
			}
			if (arg == "-ignore_redef") {
				flag_ignore_redef = true;
				continue;
			}
			if (arg == "-setattr" && argidx+1 < args.size()) {
				attributes.push_back(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		LibertyParser parser(f);
		int cell_count = 0;

		for (auto cell : parser.ast->children)
		{
			if (cell->id != "cell" || cell->args.size() != 1)
				continue;

			std::string cell_name = RTLIL::escape_id(cell->args.at(0));

			if (design->modules.count(cell_name)) {
				if (flag_ignore_redef)
					continue;
				log_error("Duplicate definition of cell/module %s.\n", RTLIL::id2cstr(cell_name));
			}

			if (!flag_lib)
			{
				LibertyAst *ff = cell->find("ff");
				if (ff != NULL) {
					log("Warning: skipping flip-flop cell %s.\n", RTLIL::id2cstr(cell_name));
					continue;
				}

				LibertyAst *latch = cell->find("latch");
				if (latch != NULL) {
					log("Warning: skipping latch cell %s.\n", RTLIL::id2cstr(cell_name));
					continue;
				}
			}

			// log("Processing cell type %s.\n", RTLIL::id2cstr(cell_name));
			cell_count++;

			RTLIL::Module *module = new RTLIL::Module;
			module->name = cell_name;
			design->modules[module->name] = module;

			for (auto &attr : attributes)
				module->attributes[attr] = 1;

			for (auto pin : cell->children)
			{
				if (pin->id != "pin" || pin->args.size() != 1)
					continue;

				LibertyAst *dir = pin->find("direction");
				if (dir == NULL || dir->value == "internal")
					continue;

				log_assert(dir->value == "input" || dir->value == "output");

				RTLIL::Wire *wire = new RTLIL::Wire;
				wire->name = RTLIL::escape_id(pin->args.at(0));
				module->add(wire);

				if (dir->value == "input") {
					wire->port_input = true;
					continue;
				}

				wire->port_output = true;

				if (flag_lib)
					continue;

				LibertyAst *func = pin->find("function");
				if (func == NULL)
					log_error("Missing function on output %s of cell %s.\n", RTLIL::id2cstr(wire->name), RTLIL::id2cstr(module->name));

				RTLIL::SigSpec out_sig = parse_func_expr(module, func->value.c_str());
				module->connections.push_back(RTLIL::SigSig(wire, out_sig));

				continue;
			}

			module->fixup_ports();
		}

		log("Imported %d cell types from liberty file.\n", cell_count);
	}
} LibertyFrontend;

