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
		token_t t = token_t(2, create_and_cell(module, stack[top-1].sig, stack[top].sig));
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
		if (next_token.type == '*' || next_token.type == '&' || next_token.type == 0 || next_token.type == '(')
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

static void create_ff(RTLIL::Module *module, LibertyAst *node)
{
	RTLIL::SigSpec iq_sig(module->new_wire(1, RTLIL::escape_id(node->args.at(0))));
	RTLIL::SigSpec iqn_sig(module->new_wire(1, RTLIL::escape_id(node->args.at(1))));

	RTLIL::SigSpec clk_sig, data_sig, clear_sig, preset_sig;
	bool clk_polarity = true, clear_polarity = true, preset_polarity = true;

	for (auto child : node->children) {
		if (child->id == "clocked_on")
			clk_sig = parse_func_expr(module, child->value.c_str());
		if (child->id == "next_state")
			data_sig = parse_func_expr(module, child->value.c_str());
		if (child->id == "clear")
			clear_sig = parse_func_expr(module, child->value.c_str());
		if (child->id == "preset")
			preset_sig = parse_func_expr(module, child->value.c_str());
	}

	if (clk_sig.width == 0 || data_sig.width == 0)
		log_error("FF cell %s has no next_state and/or clocked_on attribute.\n", RTLIL::id2cstr(module->name));

	for (bool rerun_invert_rollback = true; rerun_invert_rollback;)
	{
		rerun_invert_rollback = false;

		for (auto &it : module->cells) {
			if (it.second->type == "$_INV_" && it.second->connections.at("\\Y") == clk_sig) {
				clk_sig = it.second->connections.at("\\A");
				clk_polarity = !clk_polarity;
				rerun_invert_rollback = true;
			}
			if (it.second->type == "$_INV_" && it.second->connections.at("\\Y") == clear_sig) {
				clear_sig = it.second->connections.at("\\A");
				clear_polarity = !clear_polarity;
				rerun_invert_rollback = true;
			}
			if (it.second->type == "$_INV_" && it.second->connections.at("\\Y") == preset_sig) {
				preset_sig = it.second->connections.at("\\A");
				preset_polarity = !preset_polarity;
				rerun_invert_rollback = true;
			}
		}
	}

	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = NEW_ID;
	cell->type = "$_INV_";
	cell->connections["\\A"] = iq_sig;
	cell->connections["\\Y"] = iqn_sig;
	module->add(cell);

	cell = new RTLIL::Cell;
	cell->name = NEW_ID;
	cell->connections["\\D"] = data_sig;
	cell->connections["\\Q"] = iq_sig;
	cell->connections["\\C"] = clk_sig;
	module->add(cell);

	if (clear_sig.width == 0 && preset_sig.width == 0) {
		cell->type = stringf("$_DFF_%c_", clk_polarity ? 'P' : 'N');
	}

	if (clear_sig.width == 1 && preset_sig.width == 0) {
		cell->type = stringf("$_DFF_%c%c0_", clk_polarity ? 'P' : 'N', clear_polarity ? 'P' : 'N');
		cell->connections["\\R"] = clear_sig;
	}

	if (clear_sig.width == 0 && preset_sig.width == 1) {
		cell->type = stringf("$_DFF_%c%c1_", clk_polarity ? 'P' : 'N', preset_polarity ? 'P' : 'N');
		cell->connections["\\R"] = preset_sig;
	}

	if (clear_sig.width == 1 && preset_sig.width == 1) {
		cell->type = stringf("$_DFFSR_%c%c%c_", clk_polarity ? 'P' : 'N', preset_polarity ? 'P' : 'N', clear_polarity ? 'P' : 'N');
		cell->connections["\\S"] = preset_sig;
		cell->connections["\\R"] = clear_sig;
	}

	log_assert(!cell->type.empty());
}

static void create_latch(RTLIL::Module *module, LibertyAst *node)
{
	RTLIL::SigSpec iq_sig(module->new_wire(1, RTLIL::escape_id(node->args.at(0))));
	RTLIL::SigSpec iqn_sig(module->new_wire(1, RTLIL::escape_id(node->args.at(1))));

	RTLIL::SigSpec enable_sig, data_sig, clear_sig, preset_sig;
	bool enable_polarity = true, clear_polarity = true, preset_polarity = true;

	for (auto child : node->children) {
		if (child->id == "enable")
			enable_sig = parse_func_expr(module, child->value.c_str());
		if (child->id == "data_in")
			data_sig = parse_func_expr(module, child->value.c_str());
		if (child->id == "clear")
			clear_sig = parse_func_expr(module, child->value.c_str());
		if (child->id == "preset")
			preset_sig = parse_func_expr(module, child->value.c_str());
	}

	if (enable_sig.width == 0 || data_sig.width == 0)
		log_error("Latch cell %s has no data_in and/or enable attribute.\n", RTLIL::id2cstr(module->name));

	for (bool rerun_invert_rollback = true; rerun_invert_rollback;)
	{
		rerun_invert_rollback = false;

		for (auto &it : module->cells) {
			if (it.second->type == "$_INV_" && it.second->connections.at("\\Y") == enable_sig) {
				enable_sig = it.second->connections.at("\\A");
				enable_polarity = !enable_polarity;
				rerun_invert_rollback = true;
			}
			if (it.second->type == "$_INV_" && it.second->connections.at("\\Y") == clear_sig) {
				clear_sig = it.second->connections.at("\\A");
				clear_polarity = !clear_polarity;
				rerun_invert_rollback = true;
			}
			if (it.second->type == "$_INV_" && it.second->connections.at("\\Y") == preset_sig) {
				preset_sig = it.second->connections.at("\\A");
				preset_polarity = !preset_polarity;
				rerun_invert_rollback = true;
			}
		}
	}

	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = NEW_ID;
	cell->type = "$_INV_";
	cell->connections["\\A"] = iq_sig;
	cell->connections["\\Y"] = iqn_sig;
	module->add(cell);

	if (clear_sig.width == 1)
	{
		RTLIL::SigSpec clear_negative = clear_sig;
		RTLIL::SigSpec clear_enable = clear_sig;

		if (clear_polarity == true || clear_polarity != enable_polarity)
		{
			RTLIL::Cell *inv = new RTLIL::Cell;
			inv->name = NEW_ID;
			inv->type = "$_INV_";
			inv->connections["\\A"] = clear_sig;
			inv->connections["\\Y"] = NEW_WIRE(module, 1);;
			module->add(inv);

			if (clear_polarity == true)
				clear_negative = inv->connections["\\Y"];
			if (clear_polarity != enable_polarity)
				clear_enable = inv->connections["\\Y"];
		}

		RTLIL::Cell *data_gate = new RTLIL::Cell;
		data_gate->name = NEW_ID;
		data_gate->type = "$_AND_";
		data_gate->connections["\\A"] = data_sig;
		data_gate->connections["\\B"] = clear_negative;
		data_gate->connections["\\Y"] = data_sig = NEW_WIRE(module, 1);;
		module->add(data_gate);

		RTLIL::Cell *enable_gate = new RTLIL::Cell;
		enable_gate->name = NEW_ID;
		enable_gate->type = enable_polarity ? "$_OR_" : "$_AND_";
		enable_gate->connections["\\A"] = enable_sig;
		enable_gate->connections["\\B"] = clear_enable;
		enable_gate->connections["\\Y"] = data_sig = NEW_WIRE(module, 1);;
		module->add(enable_gate);
	}

	if (preset_sig.width == 1)
	{
		RTLIL::SigSpec preset_positive = preset_sig;
		RTLIL::SigSpec preset_enable = preset_sig;

		if (preset_polarity == false || preset_polarity != enable_polarity)
		{
			RTLIL::Cell *inv = new RTLIL::Cell;
			inv->name = NEW_ID;
			inv->type = "$_INV_";
			inv->connections["\\A"] = preset_sig;
			inv->connections["\\Y"] = NEW_WIRE(module, 1);;
			module->add(inv);

			if (preset_polarity == false)
				preset_positive = inv->connections["\\Y"];
			if (preset_polarity != enable_polarity)
				preset_enable = inv->connections["\\Y"];
		}

		RTLIL::Cell *data_gate = new RTLIL::Cell;
		data_gate->name = NEW_ID;
		data_gate->type = "$_OR_";
		data_gate->connections["\\A"] = data_sig;
		data_gate->connections["\\B"] = preset_positive;
		data_gate->connections["\\Y"] = data_sig = NEW_WIRE(module, 1);;
		module->add(data_gate);

		RTLIL::Cell *enable_gate = new RTLIL::Cell;
		enable_gate->name = NEW_ID;
		enable_gate->type = enable_polarity ? "$_OR_" : "$_AND_";
		enable_gate->connections["\\A"] = enable_sig;
		enable_gate->connections["\\B"] = preset_enable;
		enable_gate->connections["\\Y"] = data_sig = NEW_WIRE(module, 1);;
		module->add(enable_gate);
	}

	cell = new RTLIL::Cell;
	cell->name = NEW_ID;
	cell->type = stringf("$_DLATCH_%c_", enable_polarity ? 'P' : 'N');
	cell->connections["\\D"] = data_sig;
	cell->connections["\\Q"] = iq_sig;
	cell->connections["\\E"] = enable_sig;
	module->add(cell);
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
		log("    -ignore_miss_func\n");
		log("        ignore cells with missing function specification of outputs\n");
		log("\n");
		log("    -ignore_miss_dir\n");
		log("        ignore cells with a missing or invalid direction\n");
		log("        specification on a pin\n");
		log("\n");
		log("    -setattr <attribute_name>\n");
		log("        set the specified attribute (to the value 1) on all loaded modules\n");
		log("\n");
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_lib = false;
		bool flag_ignore_redef = false;
		bool flag_ignore_miss_func = false;
		bool flag_ignore_miss_dir  = false;
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
			if (arg == "-ignore_miss_func") {
				flag_ignore_miss_func = true;
				continue;
			}
			if (arg == "-ignore_miss_dir") {
				flag_ignore_miss_dir = true;
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

			// log("Processing cell type %s.\n", RTLIL::id2cstr(cell_name));

			RTLIL::Module *module = new RTLIL::Module;
			module->name = cell_name;

			for (auto &attr : attributes)
				module->attributes[attr] = 1;

			for (auto node : cell->children)
				if (node->id == "pin" && node->args.size() == 1) {
					LibertyAst *dir = node->find("direction");
					if (!dir || (dir->value != "input" && dir->value != "output" && dir->value != "internal"))
					{
						if (!flag_ignore_miss_dir)
						{
							log_error("Missing or invalid dircetion for pin %s of cell %s.\n", node->args.at(0).c_str(), RTLIL::id2cstr(module->name));
						} else {
							log("Ignoring cell %s with missing or invalid dircetion for pin %s.\n", RTLIL::id2cstr(module->name), node->args.at(0).c_str());
							delete module;
							goto skip_cell;
						}
					}
					if (!flag_lib || dir->value != "internal")
						module->new_wire(1, RTLIL::escape_id(node->args.at(0)));
				}

			for (auto node : cell->children)
			{
				if (!flag_lib) {
					if (node->id == "ff" && node->args.size() == 2)
						create_ff(module, node);
					if (node->id == "latch" && node->args.size() == 2)
						create_latch(module, node);
				}

				if (node->id == "pin" && node->args.size() == 1)
				{
					LibertyAst *dir = node->find("direction");

					if (flag_lib && dir->value == "internal")
						continue;

					RTLIL::Wire *wire = module->wires.at(RTLIL::escape_id(node->args.at(0)));

					if (dir && dir->value == "input") {
						wire->port_input = true;
						continue;
					}

					if (dir && dir->value == "output")
						wire->port_output = true;

					if (flag_lib)
						continue;

					LibertyAst *func = node->find("function");
					if (func == NULL)
					{
						if (!flag_ignore_miss_func)
						{
							log_error("Missing function on output %s of cell %s.\n", RTLIL::id2cstr(wire->name), RTLIL::id2cstr(module->name));
						} else {
							log("Ignoring cell %s with missing function on output %s.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
							delete module;
							goto skip_cell;
						}
					}

					RTLIL::SigSpec out_sig = parse_func_expr(module, func->value.c_str());
					module->connections.push_back(RTLIL::SigSig(wire, out_sig));
				}
			}

			module->fixup_ports();
			design->modules[module->name] = module;
			cell_count++;
skip_cell:;
		}

		log("Imported %d cell types from liberty file.\n", cell_count);
	}
} LibertyFrontend;

