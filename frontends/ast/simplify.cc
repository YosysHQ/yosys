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
 *  This is the AST frontend library.
 *
 *  The AST frontend library is not a frontend on it's own but provides a
 *  generic abstract syntax tree (AST) abstraction for HDL code and can be
 *  used by HDL frontends. See "ast.h" for an overview of the API and the
 *  Verilog frontend for an usage example.
 *
 */

#include "kernel/log.h"
#include "libs/sha1/sha1.h"
#include "ast.h"

#include <sstream>
#include <stdarg.h>
#include <assert.h>

using namespace AST;
using namespace AST_INTERNAL;

// convert the AST into a simpler AST that has all parameters subsitited by their
// values, unrolled for-loops, expanded generate blocks, etc. when this function
// is done with an AST it can be converted into RTLIL using genRTLIL().
//
// this function also does all name resolving and sets the id2ast member of all
// nodes that link to a different node using names and lexical scoping.
bool AstNode::simplify(bool const_fold, bool at_zero, bool in_lvalue, int stage, int width_hint, bool sign_hint)
{
	AstNode *newNode = NULL;
	bool did_something = false;

	if (stage == 0)
	{
		assert(type == AST_MODULE);

		while (simplify(const_fold, at_zero, in_lvalue, 1, width_hint, sign_hint)) { }

		if (!flag_nomem2reg && !get_bool_attribute("\\nomem2reg"))
		{
			std::set<AstNode*> mem2reg_set, mem2reg_candidates;
			mem2reg_as_needed_pass1(mem2reg_set, mem2reg_candidates, false, false, flag_mem2reg);

			for (auto node : mem2reg_set)
			{
				int mem_width, mem_size, addr_bits;
				node->meminfo(mem_width, mem_size, addr_bits);

				for (int i = 0; i < mem_size; i++) {
					AstNode *reg = new AstNode(AST_WIRE, new AstNode(AST_RANGE,
							mkconst_int(mem_width-1, true), mkconst_int(0, true)));
					reg->str = stringf("%s[%d]", node->str.c_str(), i);
					reg->is_reg = true;
					reg->is_signed = node->is_signed;
					children.push_back(reg);
					while (reg->simplify(true, false, false, 1, -1, false)) { }
				}
			}

			mem2reg_as_needed_pass2(mem2reg_set, this, NULL);

			for (size_t i = 0; i < children.size(); i++) {
				if (mem2reg_set.count(children[i]) > 0) {
					delete children[i];
					children.erase(children.begin() + (i--));
				}
			}
		}

		while (simplify(const_fold, at_zero, in_lvalue, 2, width_hint, sign_hint)) { }
		return false;
	}

	current_filename = filename;
	set_line_num(linenum);

	// we do not look inside a task or function
	// (but as soon as a task of function is instanciated we process the generated AST as usual)
	if (type == AST_FUNCTION || type == AST_TASK)
		return false;

	// deactivate all calls non-synthesis system taks
	if ((type == AST_FCALL || type == AST_TCALL) && (str == "$display" || str == "$stop" || str == "$finish")) {
		delete_children();
		str = std::string();
	}

	// activate const folding if this is anything that must be evaluated statically (ranges, parameters, attributes, etc.)
	if (type == AST_WIRE || type == AST_PARAMETER || type == AST_LOCALPARAM || type == AST_DEFPARAM || type == AST_PARASET || type == AST_RANGE || type == AST_PREFIX)
		const_fold = true;
	if (type == AST_IDENTIFIER && current_scope.count(str) > 0 && (current_scope[str]->type == AST_PARAMETER || current_scope[str]->type == AST_LOCALPARAM))
		const_fold = true;

	std::map<std::string, AstNode*> backup_scope;

	// create name resolution entries for all objects with names
	// also merge multiple declarations for the same wire (e.g. "output foobar; reg foobar;")
	if (type == AST_MODULE) {
		current_scope.clear();
		std::map<std::string, AstNode*> this_wire_scope;
		for (size_t i = 0; i < children.size(); i++) {
			AstNode *node = children[i];
			if (node->type == AST_WIRE) {
				if (this_wire_scope.count(node->str) > 0) {
					AstNode *first_node = this_wire_scope[node->str];
					if (!node->is_input && !node->is_output && node->is_reg && node->children.size() == 0)
						goto wires_are_compatible;
					if (first_node->children.size() != node->children.size())
						goto wires_are_incompatible;
					for (size_t j = 0; j < node->children.size(); j++) {
						AstNode *n1 = first_node->children[j], *n2 = node->children[j];
						if (n1->type == AST_RANGE && n2->type == AST_RANGE && n1->range_valid && n2->range_valid) {
							if (n1->range_left != n2->range_left)
								goto wires_are_incompatible;
							if (n1->range_right != n2->range_right)
								goto wires_are_incompatible;
						} else if (*n1 != *n2)
							goto wires_are_incompatible;
					}
					if (first_node->range_left != node->range_left)
						goto wires_are_incompatible;
					if (first_node->range_right != node->range_right)
						goto wires_are_incompatible;
					if (first_node->port_id == 0 && (node->is_input || node->is_output))
						goto wires_are_incompatible;
				wires_are_compatible:
					if (node->is_input)
						first_node->is_input = true;
					if (node->is_output)
						first_node->is_output = true;
					if (node->is_reg)
						first_node->is_reg = true;
					if (node->is_signed)
						first_node->is_signed = true;
					for (auto &it : node->attributes) {
						if (first_node->attributes.count(it.first) > 0)
							delete first_node->attributes[it.first];
						first_node->attributes[it.first] = it.second->clone();
					}
					children.erase(children.begin()+(i--));
					did_something = true;
					delete node;
					continue;
				}
				this_wire_scope[node->str] = node;
			}
		wires_are_incompatible:
			if (node->type == AST_PARAMETER || node->type == AST_LOCALPARAM || node->type == AST_WIRE || node->type == AST_AUTOWIRE || node->type == AST_GENVAR ||
					node->type == AST_MEMORY || node->type == AST_FUNCTION || node->type == AST_TASK || node->type == AST_CELL) {
				backup_scope[node->str] = current_scope[node->str];
				current_scope[node->str] = node;
			}
		}
	}

	auto backup_current_block = current_block;
	auto backup_current_block_child = current_block_child;
	auto backup_current_top_block = current_top_block;

	int backup_width_hint = width_hint;
	bool backup_sign_hint = sign_hint;

	bool detect_width_simple = false;
	bool child_0_is_self_determined = false;
	bool child_1_is_self_determined = false;
	bool children_are_self_determined = false;
	bool reset_width_after_children = false;

	switch (type)
	{
	case AST_ASSIGN_EQ:
	case AST_ASSIGN_LE:
	case AST_ASSIGN:
		while (children[0]->simplify(false, false, true, stage, -1, false) == true) { }
		while (children[1]->simplify(false, false, false, stage, -1, false) == true) { }
		children[0]->detectSignWidth(backup_width_hint, backup_sign_hint);
		children[1]->detectSignWidth(width_hint, sign_hint);
		width_hint = std::max(width_hint, backup_width_hint);
		child_0_is_self_determined = true;
		break;

	case AST_PARAMETER:
	case AST_LOCALPARAM:
		while (children[0]->simplify(false, false, false, stage, -1, false) == true) { }
		children[0]->detectSignWidth(width_hint, sign_hint);
		if (children.size() > 1) {
			assert(children[1]->type == AST_RANGE);
			while (children[1]->simplify(false, false, false, stage, -1, false) == true) { }
			if (!children[1]->range_valid)
				log_error("Non-constant width range on parameter decl at %s:%d.\n", filename.c_str(), linenum);
			width_hint = std::max(width_hint, children[1]->range_left - children[1]->range_right + 1);
		}
		break;

	case AST_TO_SIGNED:
	case AST_TO_UNSIGNED:
	case AST_CONCAT:
	case AST_REPLICATE:
	case AST_REDUCE_AND:
	case AST_REDUCE_OR:
	case AST_REDUCE_XOR:
	case AST_REDUCE_XNOR:
	case AST_REDUCE_BOOL:
		detect_width_simple = true;
		children_are_self_determined = true;
		break;

	case AST_NEG:
	case AST_BIT_NOT:
	case AST_POS:
	case AST_BIT_AND:
	case AST_BIT_OR:
	case AST_BIT_XOR:
	case AST_BIT_XNOR:
	case AST_ADD:
	case AST_SUB:
	case AST_MUL:
	case AST_DIV:
	case AST_MOD:
		detect_width_simple = true;
		break;

	case AST_SHIFT_LEFT:
	case AST_SHIFT_RIGHT:
	case AST_SHIFT_SLEFT:
	case AST_SHIFT_SRIGHT:
	case AST_POW:
		detect_width_simple = true;
		child_1_is_self_determined = true;
		break;

	case AST_LT:
	case AST_LE:
	case AST_EQ:
	case AST_NE:
	case AST_GE:
	case AST_GT:
		width_hint = -1;
		sign_hint = true;
		for (auto child : children) {
			while (child->simplify(false, false, in_lvalue, stage, -1, false) == true) { }
			child->detectSignWidthWorker(width_hint, sign_hint);
		}
		reset_width_after_children = true;
		break;

	case AST_LOGIC_AND:
	case AST_LOGIC_OR:
	case AST_LOGIC_NOT:
		detect_width_simple = true;
		children_are_self_determined = true;
		break;

	case AST_TERNARY:
		detect_width_simple = true;
		child_0_is_self_determined = true;
		break;
	
	case AST_MEMRD:
		detect_width_simple = true;
		children_are_self_determined = true;
		break;

	default:
		width_hint = -1;
		sign_hint = false;
	}

	if (detect_width_simple && width_hint < 0) {
		for (auto child : children)
			while (child->simplify(false, false, in_lvalue, stage, -1, false) == true) { }
		if (type == AST_REPLICATE)
			while (children[0]->simplify(true, false, in_lvalue, stage, -1, false) == true) { }
		detectSignWidth(width_hint, sign_hint);
	}

	// simplify all children first
	// (iterate by index as e.g. auto wires can add new children in the process)
	for (size_t i = 0; i < children.size(); i++) {
		bool did_something_here = true;
		if ((type == AST_GENFOR || type == AST_FOR) && i >= 3)
			break;
		if (type == AST_GENIF && i >= 1)
			break;
		if (type == AST_GENBLOCK)
			break;
		if (type == AST_PREFIX && i >= 1)
			break;
		while (did_something_here && i < children.size()) {
			bool const_fold_here = const_fold, in_lvalue_here = in_lvalue;
			int width_hint_here = width_hint;
			bool sign_hint_here = sign_hint;
			if (i == 0 && type == AST_REPLICATE)
				const_fold_here = true;
			if (type == AST_PARAMETER || type == AST_LOCALPARAM)
				const_fold_here = true;
			if (i == 0 && (type == AST_ASSIGN || type == AST_ASSIGN_EQ || type == AST_ASSIGN_LE))
				in_lvalue_here = true;
			if (type == AST_BLOCK) {
				current_block = this;
				current_block_child = children[i];
			}
			if ((type == AST_ALWAYS || type == AST_INITIAL) && children[i]->type == AST_BLOCK)
				current_top_block = children[i];
			if (i == 0 && child_0_is_self_determined)
				width_hint_here = -1, sign_hint_here = false;
			if (i == 1 && child_1_is_self_determined)
				width_hint_here = -1, sign_hint_here = false;
			if (children_are_self_determined)
				width_hint_here = -1, sign_hint_here = false;
			did_something_here = children[i]->simplify(const_fold_here, at_zero, in_lvalue_here, stage, width_hint_here, sign_hint_here);
			if (did_something_here)
				did_something = true;
		}
	}
	for (auto &attr : attributes) {
		while (attr.second->simplify(true, false, false, stage, -1, false)) { }
	}

	if (reset_width_after_children) {
		width_hint = backup_width_hint;
		sign_hint = backup_sign_hint;
		if (width_hint < 0)
			detectSignWidth(width_hint, sign_hint);
	}

	current_block = backup_current_block;
	current_block_child = backup_current_block_child;
	current_top_block = backup_current_top_block;

	for (auto it = backup_scope.begin(); it != backup_scope.end(); it++) {
		if (it->second == NULL)
			current_scope.erase(it->first);
		else
			current_scope[it->first] = it->second;
	}

	current_filename = filename;
	set_line_num(linenum);

	if (type == AST_MODULE)
		current_scope.clear();

	// convert defparam nodes to cell parameters
	if (type == AST_DEFPARAM && !str.empty()) {
		size_t pos = str.rfind('.');
		if (pos == std::string::npos)
			log_error("Defparam `%s' does not contain a dot (module/parameter seperator) at %s:%d!\n",
					RTLIL::id2cstr(str.c_str()), filename.c_str(), linenum);
		std::string modname = str.substr(0, pos), paraname = "\\" + str.substr(pos+1);
		if (current_scope.count(modname) == 0 || current_scope.at(modname)->type != AST_CELL)
			log_error("Can't find cell for defparam `%s . %s` at %s:%d!\n", RTLIL::id2cstr(modname), RTLIL::id2cstr(paraname), filename.c_str(), linenum);
		AstNode *cell = current_scope.at(modname), *paraset = clone();
		cell->children.insert(cell->children.begin() + 1, paraset);
		paraset->type = AST_PARASET;
		paraset->str = paraname;
		str.clear();
	}

	// resolve constant prefixes
	if (type == AST_PREFIX) {
		if (children[0]->type != AST_CONSTANT) {
			// dumpAst(NULL, ">   ");
			log_error("Index in generate block prefix syntax at %s:%d is not constant!\n", filename.c_str(), linenum);
		}
		assert(children[1]->type == AST_IDENTIFIER);
		newNode = children[1]->clone();
		newNode->str = stringf("%s[%d].%s", str.c_str(), children[0]->integer, children[1]->str.c_str());
		goto apply_newNode;
	}

	// annotate constant ranges
	if (type == AST_RANGE) {
		bool old_range_valid = range_valid;
		range_valid = false;
		range_left = -1;
		range_right = 0;
		assert(children.size() >= 1);
		if (children[0]->type == AST_CONSTANT) {
			range_valid = true;
			range_left = children[0]->integer;
			if (children.size() == 1)
				range_right = range_left;
		}
		if (children.size() >= 2) {
			if (children[1]->type == AST_CONSTANT)
				range_right = children[1]->integer;
			else
				range_valid = false;
		}
		if (old_range_valid != range_valid)
			did_something = true;
		if (range_valid && range_left >= 0 && range_right > range_left) {
			int tmp = range_right;
			range_right = range_left;
			range_left = tmp;
		}
	}

	// annotate wires with their ranges
	if (type == AST_WIRE) {
		if (children.size() > 0) {
			if (children[0]->range_valid) {
				if (!range_valid)
					did_something = true;
				range_valid = true;
				range_left = children[0]->range_left;
				range_right = children[0]->range_right;
			}
		} else {
			if (!range_valid)
				did_something = true;
			range_valid = true;
			range_left = 0;
			range_right = 0;
		}
	}

	// trim/extend parameters
	if ((type == AST_PARAMETER || type == AST_LOCALPARAM) && children[0]->type == AST_CONSTANT && children.size() > 1) {
		if (!children[1]->range_valid)
			log_error("Non-constant width range on parameter decl at %s:%d.\n", filename.c_str(), linenum);
		int width = children[1]->range_left - children[1]->range_right + 1;
		if (width != int(children[0]->bits.size())) {
			RTLIL::SigSpec sig(children[0]->bits);
			sig.extend(width, children[0]->is_signed);
			delete children[0];
			children[0] = mkconst_bits(sig.as_const().bits, children[0]->is_signed);
		}
		children[0]->is_signed = is_signed;
	}

	// annotate identifiers using scope resolution and create auto-wires as needed
	if (type == AST_IDENTIFIER) {
		if (current_scope.count(str) == 0) {
			for (auto node : current_ast_mod->children) {
				if ((node->type == AST_PARAMETER || node->type == AST_LOCALPARAM || node->type == AST_WIRE || node->type == AST_AUTOWIRE || node->type == AST_GENVAR ||
						node->type == AST_MEMORY || node->type == AST_FUNCTION || node->type == AST_TASK) && str == node->str) {
					current_scope[node->str] = node;
					break;
				}
			}
		}
		if (current_scope.count(str) == 0) {
			log("Warning: Creating auto-wire `%s' in module `%s'.\n", str.c_str(), current_ast_mod->str.c_str());
			AstNode *auto_wire = new AstNode(AST_AUTOWIRE);
			auto_wire->str = str;
			current_ast_mod->children.push_back(auto_wire);
			current_scope[str] = auto_wire;
			did_something = true;
		}
		id2ast = current_scope[str];
	}

	// unroll for loops and generate-for blocks
	if ((type == AST_GENFOR || type == AST_FOR) && children.size() != 0)
	{
		AstNode *init_ast = children[0];
		AstNode *while_ast = children[1];
		AstNode *next_ast = children[2];
		AstNode *body_ast = children[3];

		if (init_ast->type != AST_ASSIGN_EQ)
			log_error("Unsupported 1st expression of generate for-loop at %s:%d!\n", filename.c_str(), linenum);
		if (next_ast->type != AST_ASSIGN_EQ)
			log_error("Unsupported 3rd expression of generate for-loop at %s:%d!\n", filename.c_str(), linenum);

		if (type == AST_GENFOR) {
			if (init_ast->children[0]->id2ast == NULL || init_ast->children[0]->id2ast->type != AST_GENVAR)
				log_error("Left hand side of 1st expression of generate for-loop at %s:%d is not a gen var!\n", filename.c_str(), linenum);
			if (next_ast->children[0]->id2ast == NULL || next_ast->children[0]->id2ast->type != AST_GENVAR)
				log_error("Left hand side of 3rd expression of generate for-loop at %s:%d is not a gen var!\n", filename.c_str(), linenum);
		} else {
			if (init_ast->children[0]->id2ast == NULL || init_ast->children[0]->id2ast->type != AST_WIRE)
				log_error("Left hand side of 1st expression of generate for-loop at %s:%d is not a register!\n", filename.c_str(), linenum);
			if (next_ast->children[0]->id2ast == NULL || next_ast->children[0]->id2ast->type != AST_WIRE)
				log_error("Left hand side of 3rd expression of generate for-loop at %s:%d is not a register!\n", filename.c_str(), linenum);
		}

		if (init_ast->children[0]->id2ast != next_ast->children[0]->id2ast)
			log_error("Incompatible left-hand sides in 1st and 3rd expression of generate for-loop at %s:%d!\n", filename.c_str(), linenum);

		// eval 1st expression
		AstNode *varbuf = init_ast->children[1]->clone();
		while (varbuf->simplify(true, false, false, stage, width_hint, sign_hint)) { }

		if (varbuf->type != AST_CONSTANT)
			log_error("Right hand side of 1st expression of generate for-loop at %s:%d is not constant!\n", filename.c_str(), linenum);

		varbuf = new AstNode(AST_LOCALPARAM, varbuf);
		varbuf->str = init_ast->children[0]->str;

		AstNode *backup_scope_varbuf = current_scope[varbuf->str];
		current_scope[varbuf->str] = varbuf;

		size_t current_block_idx = 0;
		if (type == AST_FOR) {
			while (current_block_idx < current_block->children.size() &&
					current_block->children[current_block_idx] != current_block_child)
				current_block_idx++;
		}

		while (1)
		{
			// eval 2nd expression
			AstNode *buf = while_ast->clone();
			while (buf->simplify(true, false, false, stage, width_hint, sign_hint)) { }

			if (buf->type != AST_CONSTANT)
				log_error("2nd expression of generate for-loop at %s:%d is not constant!\n", filename.c_str(), linenum);

			if (buf->integer == 0) {
				delete buf;
				break;
			}
			delete buf;

			// expand body
			int index = varbuf->children[0]->integer;
			if (body_ast->type == AST_GENBLOCK)
				buf = body_ast->clone();
			else
				buf = new AstNode(AST_GENBLOCK, body_ast->clone());
			if (buf->str.empty()) {
				std::stringstream sstr;
				sstr << "$genblock$" << filename << ":" << linenum << "$" << (RTLIL::autoidx++);
				buf->str = sstr.str();
			}
			std::map<std::string, std::string> name_map;
			std::stringstream sstr;
			sstr << buf->str << "[" << index << "].";
			buf->expand_genblock(varbuf->str, sstr.str(), name_map);

			if (type == AST_GENFOR) {
				for (size_t i = 0; i < buf->children.size(); i++)
					current_ast_mod->children.push_back(buf->children[i]);
			} else {
				for (size_t i = 0; i < buf->children.size(); i++)
					current_block->children.insert(current_block->children.begin() + current_block_idx++, buf->children[i]);
			}
			buf->children.clear();
			delete buf;

			// eval 3rd expression
			buf = next_ast->children[1]->clone();
			while (buf->simplify(true, false, false, stage, width_hint, sign_hint)) { }

			if (buf->type != AST_CONSTANT)
				log_error("Right hand side of 3rd expression of generate for-loop at %s:%d is not constant!\n", filename.c_str(), linenum);

			delete varbuf->children[0];
			varbuf->children[0] = buf;
		}

		current_scope[varbuf->str] = backup_scope_varbuf;
		delete varbuf;
		delete_children();
		did_something = true;
	}

	// simplify unconditional generate block
	if (type == AST_GENBLOCK && children.size() != 0)
	{
		if (!str.empty()) {
			std::map<std::string, std::string> name_map;
			expand_genblock(std::string(), str + ".", name_map);
		}

		for (size_t i = 0; i < children.size(); i++)
			current_ast_mod->children.push_back(children[i]);

		children.clear();
		did_something = true;
	}

	// simplify generate-if blocks
	if (type == AST_GENIF && children.size() != 0)
	{
		AstNode *buf = children[0]->clone();
		while (buf->simplify(true, false, false, stage, width_hint, sign_hint)) { }
		if (buf->type != AST_CONSTANT) {
			// for (auto f : log_files)
			// 	dumpAst(f, "verilog-ast> ");
			log_error("Condition for generate if at %s:%d is not constant!\n", filename.c_str(), linenum);
		}
		if (buf->integer != 0) {
			delete buf;
			buf = children[1]->clone();
		} else {
			delete buf;
			buf = children.size() > 2 ? children[2]->clone() : NULL;
		}

		if (buf)
		{
			if (buf->type != AST_GENBLOCK)
				buf = new AstNode(AST_GENBLOCK, buf);

			if (!buf->str.empty()) {
				std::map<std::string, std::string> name_map;
				buf->expand_genblock(std::string(), buf->str + ".", name_map);
			}

			for (size_t i = 0; i < buf->children.size(); i++)
				current_ast_mod->children.push_back(buf->children[i]);

			buf->children.clear();
			delete buf;
		}

		delete_children();
		did_something = true;
	}

	// replace primitives with assignmens
	if (type == AST_PRIMITIVE)
	{
		if (children.size() < 2)
			log_error("Insufficient number of arguments for primitive `%s' at %s:%d!\n",
					str.c_str(), filename.c_str(), linenum);

		std::vector<AstNode*> children_list;
		for (auto child : children) {
			assert(child->type == AST_ARGUMENT);
			assert(child->children.size() == 1);
			children_list.push_back(child->children[0]);
			child->children.clear();
			delete child;
		}
		children.clear();

		if (str == "bufif0" || str == "bufif1" || str == "notif0" || str == "notif1")
		{
			if (children_list.size() != 3)
				log_error("Invalid number of arguments for primitive `%s' at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);

			std::vector<RTLIL::State> z_const(1, RTLIL::State::Sz);

			AstNode *mux_input = children_list.at(1);
			if (str == "notif0" || str == "notif1") {
				mux_input = new AstNode(AST_BIT_NOT, mux_input);
			}
			AstNode *node = new AstNode(AST_TERNARY, children_list.at(2));
			if (str == "bufif0") {
				node->children.push_back(AstNode::mkconst_bits(z_const, false));
				node->children.push_back(mux_input);
			} else {
				node->children.push_back(mux_input);
				node->children.push_back(AstNode::mkconst_bits(z_const, false));
			}

			str.clear();
			type = AST_ASSIGN;
			children.push_back(children_list.at(0));
			children.push_back(node);
			did_something = true;
		}
		else
		{
			AstNodeType op_type = AST_NONE;
			bool invert_results = false;

			if (str == "and")
				op_type = AST_BIT_AND;
			if (str == "nand")
				op_type = AST_BIT_AND, invert_results = true;
			if (str == "or")
				op_type = AST_BIT_OR;
			if (str == "nor")
				op_type = AST_BIT_OR, invert_results = true;
			if (str == "xor")
				op_type = AST_BIT_XOR;
			if (str == "xnor")
				op_type = AST_BIT_XOR, invert_results = true;
			if (str == "buf")
				op_type = AST_POS;
			if (str == "not")
				op_type = AST_POS, invert_results = true;
			assert(op_type != AST_NONE);

			AstNode *node = children_list[1];
			if (op_type != AST_POS)
				for (size_t i = 2; i < children_list.size(); i++)
					node = new AstNode(op_type, node, children_list[i]);
			if (invert_results)
				node = new AstNode(AST_BIT_NOT, node);

			str.clear();
			type = AST_ASSIGN;
			children.push_back(children_list[0]);
			children.push_back(node);
			did_something = true;
		}
	}

	// replace dynamic ranges in left-hand side expressions (e.g. "foo[bar] <= 1'b1;") with
	// a big case block that selects the correct single-bit assignment.
	if (type == AST_ASSIGN_EQ || type == AST_ASSIGN_LE) {
		if (children[0]->type != AST_IDENTIFIER || children[0]->children.size() == 0)
			goto skip_dynamic_range_lvalue_expansion;
		if (children[0]->children[0]->range_valid || did_something)
			goto skip_dynamic_range_lvalue_expansion;
		if (children[0]->id2ast == NULL || children[0]->id2ast->type != AST_WIRE)
			goto skip_dynamic_range_lvalue_expansion;
		if (!children[0]->id2ast->range_valid)
			goto skip_dynamic_range_lvalue_expansion;
		int source_width = children[0]->id2ast->range_left - children[0]->id2ast->range_right + 1;
		int result_width = 1;
		AstNode *shift_expr = NULL;
		AstNode *range = children[0]->children[0];
		if (range->children.size() == 1) {
			shift_expr = range->children[0]->clone();
		} else {
			shift_expr = range->children[1]->clone();
			AstNode *left_at_zero_ast = range->children[0]->clone();
			AstNode *right_at_zero_ast = range->children[1]->clone();
			while (left_at_zero_ast->simplify(true, true, false, stage, -1, false)) { }
			while (right_at_zero_ast->simplify(true, true, false, stage, -1, false)) { }
			if (left_at_zero_ast->type != AST_CONSTANT || right_at_zero_ast->type != AST_CONSTANT)
				log_error("Unsupported expression on dynamic range select on signal `%s' at %s:%d!\n",
						str.c_str(), filename.c_str(), linenum);
			result_width = left_at_zero_ast->integer - right_at_zero_ast->integer + 1;
		}
		did_something = true;
		newNode = new AstNode(AST_CASE, shift_expr);
		for (int i = 0; i <= source_width-result_width; i++) {
			int start_bit = children[0]->id2ast->range_right + i;
			AstNode *cond = new AstNode(AST_COND, mkconst_int(start_bit, true));
			AstNode *lvalue = children[0]->clone();
			lvalue->delete_children();
			lvalue->children.push_back(new AstNode(AST_RANGE,
					mkconst_int(start_bit+result_width-1, true), mkconst_int(start_bit, true)));
			cond->children.push_back(new AstNode(AST_BLOCK, new AstNode(type, lvalue, children[1]->clone())));
			newNode->children.push_back(cond);
		}
		goto apply_newNode;
	}
skip_dynamic_range_lvalue_expansion:;

	// found right-hand side identifier for memory -> replace with memory read port
	if (stage > 1 && type == AST_IDENTIFIER && id2ast != NULL && id2ast->type == AST_MEMORY && !in_lvalue &&
			children[0]->type == AST_RANGE && children[0]->children.size() == 1) {
		newNode = new AstNode(AST_MEMRD, children[0]->children[0]->clone());
		newNode->str = str;
		newNode->id2ast = id2ast;
		goto apply_newNode;
	}

	// assignment with memory in left-hand side expression -> replace with memory write port
	if (stage > 1 && (type == AST_ASSIGN_EQ || type == AST_ASSIGN_LE) && children[0]->type == AST_IDENTIFIER &&
			children[0]->children.size() == 1 && children[0]->id2ast && children[0]->id2ast->type == AST_MEMORY &&
			children[0]->id2ast->children.size() >= 2 && children[0]->id2ast->children[0]->range_valid &&
			children[0]->id2ast->children[1]->range_valid)
	{
		std::stringstream sstr;
		sstr << "$memwr$" << children[0]->str << "$" << filename << ":" << linenum << "$" << (RTLIL::autoidx++);
		std::string id_addr = sstr.str() + "_ADDR", id_data = sstr.str() + "_DATA", id_en = sstr.str() + "_EN";

		if (type == AST_ASSIGN_EQ)
			log("Warining: Blocking assignment to memory in line %s:%d is handled like a non-blocking assignment.\n",
					filename.c_str(), linenum);

		int mem_width, mem_size, addr_bits;
		children[0]->id2ast->meminfo(mem_width, mem_size, addr_bits);

		AstNode *wire_addr = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(addr_bits-1, true), mkconst_int(0, true)));
		wire_addr->str = id_addr;
		current_ast_mod->children.push_back(wire_addr);
		current_scope[wire_addr->str] = wire_addr;
		while (wire_addr->simplify(true, false, false, 1, -1, false)) { }

		AstNode *wire_data = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(mem_width-1, true), mkconst_int(0, true)));
		wire_data->str = id_data;
		current_ast_mod->children.push_back(wire_data);
		current_scope[wire_data->str] = wire_data;
		while (wire_data->simplify(true, false, false, 1, -1, false)) { }

		AstNode *wire_en = new AstNode(AST_WIRE);
		wire_en->str = id_en;
		current_ast_mod->children.push_back(wire_en);
		current_scope[wire_en->str] = wire_en;
		while (wire_en->simplify(true, false, false, 1, -1, false)) { }

		std::vector<RTLIL::State> x_bits;
		x_bits.push_back(RTLIL::State::Sx);

		AstNode *assign_addr = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), mkconst_bits(x_bits, false));
		assign_addr->children[0]->str = id_addr;

		AstNode *assign_data = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), mkconst_bits(x_bits, false));
		assign_data->children[0]->str = id_data;

		AstNode *assign_en = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), mkconst_int(0, false, 1));
		assign_en->children[0]->str = id_en;

		AstNode *default_signals = new AstNode(AST_BLOCK);
		default_signals->children.push_back(assign_addr);
		default_signals->children.push_back(assign_data);
		default_signals->children.push_back(assign_en);
		current_top_block->children.insert(current_top_block->children.begin(), default_signals);

		assign_addr = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), children[0]->children[0]->children[0]->clone());
		assign_addr->children[0]->str = id_addr;

		assign_data = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), children[1]->clone());
		assign_data->children[0]->str = id_data;

		assign_en = new AstNode(AST_ASSIGN_LE, new AstNode(AST_IDENTIFIER), mkconst_int(1, false, 1));
		assign_en->children[0]->str = id_en;

		newNode = new AstNode(AST_BLOCK);
		newNode->children.push_back(assign_addr);
		newNode->children.push_back(assign_data);
		newNode->children.push_back(assign_en);

		AstNode *wrnode = new AstNode(AST_MEMWR);
		wrnode->children.push_back(new AstNode(AST_IDENTIFIER));
		wrnode->children.push_back(new AstNode(AST_IDENTIFIER));
		wrnode->children.push_back(new AstNode(AST_IDENTIFIER));
		wrnode->str = children[0]->str;
		wrnode->children[0]->str = id_addr;
		wrnode->children[1]->str = id_data;
		wrnode->children[2]->str = id_en;
		current_ast_mod->children.push_back(wrnode);

		goto apply_newNode;
	}

	// replace function and task calls with the code from the function or task
	if ((type == AST_FCALL || type == AST_TCALL) && !str.empty())
	{
		if (type == AST_FCALL) {
			if (current_scope.count(str) == 0 || current_scope[str]->type != AST_FUNCTION)
				log_error("Can't resolve function name `%s' at %s:%d.\n", str.c_str(), filename.c_str(), linenum);
		}
		if (type == AST_TCALL) {
			if (current_scope.count(str) == 0 || current_scope[str]->type != AST_TASK)
				log_error("Can't resolve task name `%s' at %s:%d.\n", str.c_str(), filename.c_str(), linenum);
		}

		AstNode *decl = current_scope[str];
		std::stringstream sstr;
		sstr << "$func$" << str << "$" << filename << ":" << linenum << "$" << (RTLIL::autoidx++) << "$";
		std::string prefix = sstr.str();

		size_t arg_count = 0;
		std::map<std::string, std::string> replace_rules;

		if (current_block == NULL)
		{
			assert(type == AST_FCALL);

			AstNode *wire = NULL;
			for (auto child : decl->children)
				if (child->type == AST_WIRE && child->str == str)
					wire = child->clone();
			assert(wire != NULL);

			wire->str = prefix + str;
			wire->port_id = 0;
			wire->is_input = false;
			wire->is_output = false;

			current_ast_mod->children.push_back(wire);
			while (wire->simplify(true, false, false, 1, -1, false)) { }

			AstNode *lvalue = new AstNode(AST_IDENTIFIER);
			lvalue->str = wire->str;

			AstNode *always = new AstNode(AST_ALWAYS, new AstNode(AST_BLOCK,
					new AstNode(AST_ASSIGN_EQ, lvalue, clone())));
			current_ast_mod->children.push_back(always);

			goto replace_fcall_with_id;
		}

		for (auto child : decl->children)
		{
			if (child->type == AST_WIRE)
			{
				AstNode *wire = child->clone();
				wire->str = prefix + wire->str;
				wire->port_id = 0;
				wire->is_input = false;
				wire->is_output = false;
				current_ast_mod->children.push_back(wire);
				while (wire->simplify(true, false, false, 1, -1, false)) { }

				replace_rules[child->str] = wire->str;

				if (child->is_input && arg_count < children.size())
				{
					AstNode *arg = children[arg_count++]->clone();
					AstNode *wire_id = new AstNode(AST_IDENTIFIER);
					wire_id->str = wire->str;
					AstNode *assign = new AstNode(AST_ASSIGN_EQ, wire_id, arg);

					for (auto it = current_block->children.begin(); it != current_block->children.end(); it++) {
						if (*it != current_block_child)
							continue;
						current_block->children.insert(it, assign);
						break;
					}
				}
			}
			else
			{
				AstNode *stmt = child->clone();
				stmt->replace_ids(replace_rules);

				for (auto it = current_block->children.begin(); it != current_block->children.end(); it++) {
					if (*it != current_block_child)
						continue;
					current_block->children.insert(it, stmt);
					break;
				}
			}
		}

	replace_fcall_with_id:
		if (type == AST_FCALL) {
			delete_children();
			type = AST_IDENTIFIER;
			str = prefix + str;
		}
		if (type == AST_TCALL)
			str = "";
		did_something = true;
	}

	// perform const folding when activated
	if (const_fold && newNode == NULL)
	{
		std::vector<RTLIL::State> tmp_bits;
		RTLIL::Const (*const_func)(const RTLIL::Const&, const RTLIL::Const&, bool, bool, int);
		RTLIL::Const dummy_arg;

		switch (type)
		{
		case AST_IDENTIFIER:
			if (current_scope.count(str) > 0 && (current_scope[str]->type == AST_PARAMETER || current_scope[str]->type == AST_LOCALPARAM)) {
				if (current_scope[str]->children[0]->type == AST_CONSTANT) {
					if (children.size() != 0 && children[0]->type == AST_RANGE && children[0]->range_valid) {
						std::vector<RTLIL::State> data;
						for (int i = children[0]->range_right; i <= children[0]->range_left; i++)
							data.push_back(current_scope[str]->children[0]->bits[i]);
						newNode = mkconst_bits(data, false);
					} else
					if (children.size() == 0)
						newNode = current_scope[str]->children[0]->clone();
				}
			}
			else if (at_zero && current_scope.count(str) > 0 && (current_scope[str]->type == AST_WIRE || current_scope[str]->type == AST_AUTOWIRE)) {
				newNode = mkconst_int(0, sign_hint, width_hint);
			}
			break;
		case AST_BIT_NOT:
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = RTLIL::const_not(children[0]->bitsAsConst(width_hint, sign_hint), dummy_arg, sign_hint, false, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			}
			break;
		if (0) { case AST_BIT_AND:  const_func = RTLIL::const_and;  }
		if (0) { case AST_BIT_OR:   const_func = RTLIL::const_or;   }
		if (0) { case AST_BIT_XOR:  const_func = RTLIL::const_xor;  }
		if (0) { case AST_BIT_XNOR: const_func = RTLIL::const_xnor; }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(children[0]->bitsAsConst(width_hint, sign_hint),
						children[1]->bitsAsConst(width_hint, sign_hint), sign_hint, sign_hint, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			}
			break;
		if (0) { case AST_REDUCE_AND:  const_func = RTLIL::const_reduce_and;  }
		if (0) { case AST_REDUCE_OR:   const_func = RTLIL::const_reduce_or;   }
		if (0) { case AST_REDUCE_XOR:  const_func = RTLIL::const_reduce_xor;  }
		if (0) { case AST_REDUCE_XNOR: const_func = RTLIL::const_reduce_xnor; }
		if (0) { case AST_REDUCE_BOOL: const_func = RTLIL::const_reduce_bool; }
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(RTLIL::Const(children[0]->bits), dummy_arg, false, false, -1);
				newNode = mkconst_bits(y.bits, false);
			}
			break;
		case AST_LOGIC_NOT:
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = RTLIL::const_logic_not(RTLIL::Const(children[0]->bits), dummy_arg, children[0]->is_signed, false, -1);
				newNode = mkconst_bits(y.bits, false);
			}
			break;
		if (0) { case AST_LOGIC_AND: const_func = RTLIL::const_logic_and; }
		if (0) { case AST_LOGIC_OR:  const_func = RTLIL::const_logic_or;  }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(RTLIL::Const(children[0]->bits), RTLIL::Const(children[1]->bits),
						children[0]->is_signed, children[1]->is_signed, -1);
				newNode = mkconst_bits(y.bits, false);
			}
			break;
		if (0) { case AST_SHIFT_LEFT:   const_func = RTLIL::const_shl;  }
		if (0) { case AST_SHIFT_RIGHT:  const_func = RTLIL::const_shr;  }
		if (0) { case AST_SHIFT_SLEFT:  const_func = RTLIL::const_sshl; }
		if (0) { case AST_SHIFT_SRIGHT: const_func = RTLIL::const_sshr; }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(children[0]->bitsAsConst(width_hint, sign_hint),
						RTLIL::Const(children[1]->bits), sign_hint, false, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			}
			break;
		if (0) { case AST_LT: const_func = RTLIL::const_lt; }
		if (0) { case AST_LE: const_func = RTLIL::const_le; }
		if (0) { case AST_EQ: const_func = RTLIL::const_eq; }
		if (0) { case AST_NE: const_func = RTLIL::const_ne; }
		if (0) { case AST_GE: const_func = RTLIL::const_ge; }
		if (0) { case AST_GT: const_func = RTLIL::const_gt; }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				int cmp_width = std::max(children[0]->bits.size(), children[1]->bits.size());
				bool cmp_signed = children[0]->is_signed && children[1]->is_signed;
				RTLIL::Const y = const_func(children[0]->bitsAsConst(cmp_width, cmp_signed),
						children[1]->bitsAsConst(cmp_width, cmp_signed), cmp_signed, cmp_signed, 1);
				newNode = mkconst_bits(y.bits, false);
			}
			break;
		if (0) { case AST_ADD: const_func = RTLIL::const_add; }
		if (0) { case AST_SUB: const_func = RTLIL::const_sub; }
		if (0) { case AST_MUL: const_func = RTLIL::const_mul; }
		if (0) { case AST_DIV: const_func = RTLIL::const_div; }
		if (0) { case AST_MOD: const_func = RTLIL::const_mod; }
		if (0) { case AST_POW: const_func = RTLIL::const_pow; }
			if (children[0]->type == AST_CONSTANT && children[1]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(children[0]->bitsAsConst(width_hint, sign_hint),
						children[1]->bitsAsConst(width_hint, sign_hint), sign_hint, sign_hint, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			}
			break;
		if (0) { case AST_POS: const_func = RTLIL::const_pos; }
		if (0) { case AST_NEG: const_func = RTLIL::const_neg; }
			if (children[0]->type == AST_CONSTANT) {
				RTLIL::Const y = const_func(children[0]->bitsAsConst(width_hint, sign_hint), dummy_arg, sign_hint, false, width_hint);
				newNode = mkconst_bits(y.bits, sign_hint);
			}
			break;
		case AST_TERNARY:
			if (children[0]->type == AST_CONSTANT) {
				AstNode *choice = children[children[0]->integer ? 1 : 2];
				if (choice->type == AST_CONSTANT) {
					RTLIL::Const y = choice->bitsAsConst(width_hint, sign_hint);
					newNode = mkconst_bits(y.bits, sign_hint);
				}
			}
			break;
		case AST_CONCAT:
			for (auto it = children.begin(); it != children.end(); it++) {
				if ((*it)->type != AST_CONSTANT)
					goto not_const;
				tmp_bits.insert(tmp_bits.end(), (*it)->bits.begin(), (*it)->bits.end());
			}
			newNode = mkconst_bits(tmp_bits, false);
			break;
		case AST_REPLICATE:
			if (children.at(0)->type != AST_CONSTANT || children.at(1)->type != AST_CONSTANT)
				goto not_const;
			for (int i = 0; i < children[0]->bitsAsConst().as_int(); i++)
				tmp_bits.insert(tmp_bits.end(), children.at(1)->bits.begin(), children.at(1)->bits.end());
			newNode = mkconst_bits(tmp_bits, false);
			break;
		default:
		not_const:
			break;
		}
	}

	// if any of the above set 'newNode' -> use 'newNode' as template to update 'this'
	if (newNode) {
apply_newNode:
		// fprintf(stderr, "----\n");
		// dumpAst(stderr, "- ");
		// newNode->dumpAst(stderr, "+ ");
		assert(newNode != NULL);
		newNode->filename = filename;
		newNode->linenum = linenum;
		newNode->cloneInto(this);
		delete newNode;
		did_something = true;
	}

	return did_something;
}

// annotate the names of all wires and other named objects in a generate block
void AstNode::expand_genblock(std::string index_var, std::string prefix, std::map<std::string, std::string> &name_map)
{
	if (!index_var.empty() && type == AST_IDENTIFIER && str == index_var) {
		current_scope[index_var]->children[0]->cloneInto(this);
		return;
	}

	if ((type == AST_IDENTIFIER || type == AST_FCALL || type == AST_TCALL) && name_map.count(str) > 0)
		str = name_map[str];

	std::map<std::string, std::string> backup_name_map;

	for (size_t i = 0; i < children.size(); i++) {
		AstNode *child = children[i];
		if (child->type == AST_WIRE || child->type == AST_MEMORY || child->type == AST_PARAMETER || child->type == AST_LOCALPARAM ||
				child->type == AST_FUNCTION || child->type == AST_TASK || child->type == AST_CELL) {
			if (backup_name_map.size() == 0)
				backup_name_map = name_map;
			std::string new_name = prefix[0] == '\\' ? prefix.substr(1) : prefix;
			size_t pos = child->str.rfind('.');
			if (pos == std::string::npos)
				pos = child->str[0] == '\\' ? 1 : 0;
			else
				pos = pos + 1;
			new_name = child->str.substr(0, pos) + new_name + child->str.substr(pos);
			if (new_name[0] != '$' && new_name[0] != '\\')
				new_name = prefix[0] + new_name;
			name_map[child->str] = new_name;
			child->str = new_name;
		}
	}

	for (size_t i = 0; i < children.size(); i++) {
		AstNode *child = children[i];
		if (child->type != AST_FUNCTION && child->type != AST_TASK)
			child->expand_genblock(index_var, prefix, name_map);
	}

	if (backup_name_map.size() > 0)
		name_map.swap(backup_name_map);
}

// rename stuff (used when tasks of functions are instanciated)
void AstNode::replace_ids(std::map<std::string, std::string> &rules)
{
	if (type == AST_IDENTIFIER && rules.count(str) > 0)
		str = rules[str];
	for (auto child : children)
		child->replace_ids(rules);
}

// find memories that should be replaced by registers
void AstNode::mem2reg_as_needed_pass1(std::set<AstNode*> &mem2reg_set, std::set<AstNode*> &mem2reg_candidates, bool sync_proc, bool async_proc, bool force_mem2reg)
{
	if ((type == AST_ASSIGN_LE && async_proc) || (type == AST_ASSIGN_EQ && (sync_proc || async_proc)))
		if (children[0]->type == AST_IDENTIFIER && children[0]->id2ast && children[0]->id2ast->type == AST_MEMORY &&
				!children[0]->id2ast->get_bool_attribute("\\nomem2reg")) {
			if (async_proc || mem2reg_candidates.count(children[0]->id2ast) > 0) {
				if (mem2reg_set.count(children[0]->id2ast) == 0)
					log("Warning: Replacing memory %s with list of registers because of assignment in line %s:%d.\n",
						children[0]->str.c_str(), filename.c_str(), linenum);
				mem2reg_set.insert(children[0]->id2ast);
			}
			mem2reg_candidates.insert(children[0]->id2ast);
		}
	
	if (type == AST_MEMORY && (get_bool_attribute("\\mem2reg") || force_mem2reg))
		mem2reg_set.insert(this);

	if (type == AST_MODULE && get_bool_attribute("\\mem2reg"))
		force_mem2reg = true;

	if (type == AST_ALWAYS) {
		for (auto child : children) {
			if (child->type == AST_POSEDGE || child->type == AST_NEGEDGE)
				sync_proc = true;
		}
		async_proc = !sync_proc;
	}

	for (auto child : children)
		child->mem2reg_as_needed_pass1(mem2reg_set, mem2reg_candidates, sync_proc, async_proc, force_mem2reg);
}

// actually replace memories with registers
void AstNode::mem2reg_as_needed_pass2(std::set<AstNode*> &mem2reg_set, AstNode *mod, AstNode *block)
{
	if (type == AST_BLOCK)
		block = this;

	if ((type == AST_ASSIGN_LE || type == AST_ASSIGN_EQ) && block != NULL &&
			children[0]->id2ast && mem2reg_set.count(children[0]->id2ast) > 0)
	{
		std::stringstream sstr;
		sstr << "$mem2reg_wr$" << children[0]->str << "$" << filename << ":" << linenum << "$" << (RTLIL::autoidx++);
		std::string id_addr = sstr.str() + "_ADDR", id_data = sstr.str() + "_DATA";

		int mem_width, mem_size, addr_bits;
		children[0]->id2ast->meminfo(mem_width, mem_size, addr_bits);

		AstNode *wire_addr = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(addr_bits-1, true), mkconst_int(0, true)));
		wire_addr->str = id_addr;
		wire_addr->is_reg = true;
		wire_addr->attributes["\\nosync"] = AstNode::mkconst_int(1, false);
		mod->children.push_back(wire_addr);
		while (wire_addr->simplify(true, false, false, 1, -1, false)) { }

		AstNode *wire_data = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(mem_width-1, true), mkconst_int(0, true)));
		wire_data->str = id_data;
		wire_data->is_reg = true;
		wire_data->attributes["\\nosync"] = AstNode::mkconst_int(1, false);
		mod->children.push_back(wire_data);
		while (wire_data->simplify(true, false, false, 1, -1, false)) { }

		assert(block != NULL);
		size_t assign_idx = 0;
		while (assign_idx < block->children.size() && block->children[assign_idx] != this)
			assign_idx++;
		assert(assign_idx < block->children.size());

		AstNode *assign_addr = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), children[0]->children[0]->children[0]->clone());
		assign_addr->children[0]->str = id_addr;
		block->children.insert(block->children.begin()+assign_idx+1, assign_addr);

		AstNode *case_node = new AstNode(AST_CASE, new AstNode(AST_IDENTIFIER));
		case_node->children[0]->str = id_addr;
		for (int i = 0; i < mem_size; i++) {
			if (children[0]->children[0]->children[0]->type == AST_CONSTANT && int(children[0]->children[0]->children[0]->integer) != i)
				continue;
			AstNode *cond_node = new AstNode(AST_COND, AstNode::mkconst_int(i, false, addr_bits), new AstNode(AST_BLOCK));
			AstNode *assign_reg = new AstNode(type, new AstNode(AST_IDENTIFIER), new AstNode(AST_IDENTIFIER));
			assign_reg->children[0]->str = stringf("%s[%d]", children[0]->str.c_str(), i);
			assign_reg->children[1]->str = id_data;
			cond_node->children[1]->children.push_back(assign_reg);
			case_node->children.push_back(cond_node);
		}
		block->children.insert(block->children.begin()+assign_idx+2, case_node);

		children[0]->delete_children();
		children[0]->range_valid = false;
		children[0]->id2ast = NULL;
		children[0]->str = id_data;
		type = AST_ASSIGN_EQ;
	}

	if (type == AST_IDENTIFIER && id2ast && mem2reg_set.count(id2ast) > 0)
	{
		std::stringstream sstr;
		sstr << "$mem2reg_rd$" << children[0]->str << "$" << filename << ":" << linenum << "$" << (RTLIL::autoidx++);
		std::string id_addr = sstr.str() + "_ADDR", id_data = sstr.str() + "_DATA";

		int mem_width, mem_size, addr_bits;
		id2ast->meminfo(mem_width, mem_size, addr_bits);

		AstNode *wire_addr = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(addr_bits-1, true), mkconst_int(0, true)));
		wire_addr->str = id_addr;
		wire_addr->attributes["\\nosync"] = AstNode::mkconst_int(1, false);
		mod->children.push_back(wire_addr);
		while (wire_addr->simplify(true, false, false, 1, -1, false)) { }

		AstNode *wire_data = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(mem_width-1, true), mkconst_int(0, true)));
		wire_data->str = id_data;
		wire_data->attributes["\\nosync"] = AstNode::mkconst_int(1, false);
		mod->children.push_back(wire_data);
		while (wire_data->simplify(true, false, false, 1, -1, false)) { }

		AstNode *assign_addr = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), children[0]->children[0]->clone());
		assign_addr->children[0]->str = id_addr;

		AstNode *case_node = new AstNode(AST_CASE, new AstNode(AST_IDENTIFIER));
		case_node->children[0]->str = id_addr;

		for (int i = 0; i < mem_size; i++) {
			if (children[0]->children[0]->type == AST_CONSTANT && int(children[0]->children[0]->integer) != i)
				continue;
			AstNode *cond_node = new AstNode(AST_COND, AstNode::mkconst_int(i, false, addr_bits), new AstNode(AST_BLOCK));
			AstNode *assign_reg = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), new AstNode(AST_IDENTIFIER));
			assign_reg->children[0]->str = id_data;
			assign_reg->children[1]->str = stringf("%s[%d]", str.c_str(), i);
			cond_node->children[1]->children.push_back(assign_reg);
			case_node->children.push_back(cond_node);
		}

		std::vector<RTLIL::State> x_bits;
		x_bits.push_back(RTLIL::State::Sx);

		AstNode *cond_node = new AstNode(AST_COND, new AstNode(AST_DEFAULT), new AstNode(AST_BLOCK));
		AstNode *assign_reg = new AstNode(AST_ASSIGN_EQ, new AstNode(AST_IDENTIFIER), AstNode::mkconst_bits(x_bits, false));
		assign_reg->children[0]->str = id_data;
		cond_node->children[1]->children.push_back(assign_reg);
		case_node->children.push_back(cond_node);

		if (block)
		{
			size_t assign_idx = 0;
			while (assign_idx < block->children.size() && !block->children[assign_idx]->contains(this))
				assign_idx++;
			assert(assign_idx < block->children.size());
			block->children.insert(block->children.begin()+assign_idx, case_node);
			block->children.insert(block->children.begin()+assign_idx, assign_addr);
			wire_addr->is_reg = true;
			wire_data->is_reg = true;
		}
		else
		{
			AstNode *proc = new AstNode(AST_ALWAYS, new AstNode(AST_BLOCK));
			proc->children[0]->children.push_back(case_node);
			mod->children.push_back(proc);
			mod->children.push_back(assign_addr);
		}

		delete_children();
		range_valid = false;
		id2ast = NULL;
		str = id_data;
	}

	assert(id2ast == NULL || mem2reg_set.count(id2ast) == 0);

	auto children_list = children;
	for (size_t i = 0; i < children_list.size(); i++)
		children_list[i]->mem2reg_as_needed_pass2(mem2reg_set, mod, block);
}

// calulate memory dimensions
void AstNode::meminfo(int &mem_width, int &mem_size, int &addr_bits)
{
	assert(type == AST_MEMORY);

	mem_width = children[0]->range_left - children[0]->range_right + 1;
	mem_size = children[1]->range_left - children[1]->range_right;

	if (mem_size < 0)
		mem_size *= -1;
	mem_size += std::min(children[1]->range_left, children[1]->range_right) + 1;

	addr_bits = 1;
	while ((1 << addr_bits) < mem_size)
		addr_bits++;
}

