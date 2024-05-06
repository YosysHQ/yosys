/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018  Ruben Undheim <ruben.undheim@gmail.com>
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

#include "kernel/yosys.h"
#include "libs/sha1/sha1.h"
#include "ast.h"

YOSYS_NAMESPACE_BEGIN

using namespace AST;
using namespace AST_INTERNAL;

// instantiate global variables (public API)
namespace AST {
	std::string current_filename;
	void (*set_line_num)(int) = NULL;
	int (*get_line_num)() = NULL;
}

// instantiate global variables (private API)
namespace AST_INTERNAL {
	bool flag_nodisplay, flag_dump_ast1, flag_dump_ast2, flag_no_dump_ptr, flag_dump_vlog1, flag_dump_vlog2, flag_dump_rtlil, flag_nolatches, flag_nomeminit;
	bool flag_nomem2reg, flag_mem2reg, flag_noblackbox, flag_lib, flag_nowb, flag_noopt, flag_icells, flag_pwires, flag_autowire;
	AstNode *current_ast, *current_ast_mod;
	std::map<std::string, AstNode*> current_scope;
	const dict<RTLIL::SigBit, RTLIL::SigBit> *genRTLIL_subst_ptr = NULL;
	RTLIL::SigSpec ignoreThisSignalsInInitial;
	AstNode *current_always, *current_top_block, *current_block, *current_block_child;
	Module *current_module;
	bool current_always_clocked;
	dict<std::string, int> current_memwr_count;
	dict<std::string, pool<int>> current_memwr_visible;
}

// convert node types to string
std::string AST::type2str(AstNodeType type)
{
	switch (type)
	{
#define X(_item) case _item: return #_item;
	X(AST_NONE)
	X(AST_DESIGN)
	X(AST_MODULE)
	X(AST_TASK)
	X(AST_FUNCTION)
	X(AST_DPI_FUNCTION)
	X(AST_WIRE)
	X(AST_MEMORY)
	X(AST_AUTOWIRE)
	X(AST_PARAMETER)
	X(AST_LOCALPARAM)
	X(AST_DEFPARAM)
	X(AST_PARASET)
	X(AST_ARGUMENT)
	X(AST_RANGE)
	X(AST_MULTIRANGE)
	X(AST_CONSTANT)
	X(AST_REALVALUE)
	X(AST_CELLTYPE)
	X(AST_IDENTIFIER)
	X(AST_PREFIX)
	X(AST_ASSERT)
	X(AST_ASSUME)
	X(AST_LIVE)
	X(AST_FAIR)
	X(AST_COVER)
	X(AST_ENUM)
	X(AST_ENUM_ITEM)
	X(AST_FCALL)
	X(AST_TO_BITS)
	X(AST_TO_SIGNED)
	X(AST_TO_UNSIGNED)
	X(AST_SELFSZ)
	X(AST_CAST_SIZE)
	X(AST_CONCAT)
	X(AST_REPLICATE)
	X(AST_BIT_NOT)
	X(AST_BIT_AND)
	X(AST_BIT_OR)
	X(AST_BIT_XOR)
	X(AST_BIT_XNOR)
	X(AST_REDUCE_AND)
	X(AST_REDUCE_OR)
	X(AST_REDUCE_XOR)
	X(AST_REDUCE_XNOR)
	X(AST_REDUCE_BOOL)
	X(AST_SHIFT_LEFT)
	X(AST_SHIFT_RIGHT)
	X(AST_SHIFT_SLEFT)
	X(AST_SHIFT_SRIGHT)
	X(AST_SHIFTX)
	X(AST_SHIFT)
	X(AST_LT)
	X(AST_LE)
	X(AST_EQ)
	X(AST_NE)
	X(AST_EQX)
	X(AST_NEX)
	X(AST_GE)
	X(AST_GT)
	X(AST_ADD)
	X(AST_SUB)
	X(AST_MUL)
	X(AST_DIV)
	X(AST_MOD)
	X(AST_POW)
	X(AST_POS)
	X(AST_NEG)
	X(AST_LOGIC_AND)
	X(AST_LOGIC_OR)
	X(AST_LOGIC_NOT)
	X(AST_TERNARY)
	X(AST_MEMRD)
	X(AST_MEMWR)
	X(AST_MEMINIT)
	X(AST_TCALL)
	X(AST_ASSIGN)
	X(AST_CELL)
	X(AST_PRIMITIVE)
	X(AST_CELLARRAY)
	X(AST_ALWAYS)
	X(AST_INITIAL)
	X(AST_BLOCK)
	X(AST_ASSIGN_EQ)
	X(AST_ASSIGN_LE)
	X(AST_CASE)
	X(AST_COND)
	X(AST_CONDX)
	X(AST_CONDZ)
	X(AST_DEFAULT)
	X(AST_FOR)
	X(AST_WHILE)
	X(AST_REPEAT)
	X(AST_GENVAR)
	X(AST_GENFOR)
	X(AST_GENIF)
	X(AST_GENCASE)
	X(AST_GENBLOCK)
	X(AST_TECALL)
	X(AST_POSEDGE)
	X(AST_NEGEDGE)
	X(AST_EDGE)
	X(AST_INTERFACE)
	X(AST_INTERFACEPORT)
	X(AST_INTERFACEPORTTYPE)
	X(AST_MODPORT)
	X(AST_MODPORTMEMBER)
	X(AST_PACKAGE)
	X(AST_WIRETYPE)
	X(AST_TYPEDEF)
	X(AST_STRUCT)
	X(AST_UNION)
	X(AST_STRUCT_ITEM)
	X(AST_BIND)
#undef X
	default:
		log_abort();
	}
}

// check if attribute exists and has non-zero value
bool AstNode::get_bool_attribute(RTLIL::IdString id)
{
	if (attributes.count(id) == 0)
		return false;

	AstNode *attr = attributes.at(id);
	if (attr->type != AST_CONSTANT)
		attr->input_error("Attribute `%s' with non-constant value!\n", id.c_str());

	return attr->integer != 0;
}

// create new node (AstNode constructor)
// (the optional child arguments make it easier to create AST trees)
AstNode::AstNode(AstNodeType type, AstNode *child1, AstNode *child2, AstNode *child3, AstNode *child4)
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	this->type = type;
	filename = current_filename;
	is_input = false;
	is_output = false;
	is_reg = false;
	is_logic = false;
	is_signed = false;
	is_string = false;
	is_enum = false;
	is_wand = false;
	is_wor = false;
	is_unsized = false;
	was_checked = false;
	range_valid = false;
	range_swapped = false;
	is_custom_type = false;
	port_id = 0;
	range_left = -1;
	range_right = 0;
	unpacked_dimensions = 0;
	integer = 0;
	realvalue = 0;
	id2ast = NULL;
	basic_prep = false;
	lookahead = false;
	in_lvalue_from_above = false;
	in_param_from_above = false;
	in_lvalue = false;
	in_param = false;

	if (child1)
		children.push_back(child1);
	if (child2)
		children.push_back(child2);
	if (child3)
		children.push_back(child3);
	if (child4)
		children.push_back(child4);

	fixup_hierarchy_flags();
}

// create a (deep recursive) copy of a node
AstNode *AstNode::clone() const
{
	AstNode *that = new AstNode;
	*that = *this;
	for (auto &it : that->children)
		it = it->clone();
	for (auto &it : that->attributes)
		it.second = it.second->clone();

	that->set_in_lvalue_flag(false);
	that->set_in_param_flag(false);
	that->fixup_hierarchy_flags(); // fixup to set flags on cloned children
	return that;
}

// create a (deep recursive) copy of a node use 'other' as target root node
void AstNode::cloneInto(AstNode *other) const
{
	AstNode *tmp = clone();
	tmp->in_lvalue_from_above = other->in_lvalue_from_above;
	tmp->in_param_from_above = other->in_param_from_above;
	other->delete_children();
	*other = *tmp;
	tmp->children.clear();
	tmp->attributes.clear();
	other->fixup_hierarchy_flags();
	delete tmp;
}

// delete all children in this node
void AstNode::delete_children()
{
	for (auto &it : children)
		delete it;
	children.clear();

	for (auto &it : attributes)
		delete it.second;
	attributes.clear();
}

// AstNode destructor
AstNode::~AstNode()
{
	delete_children();
}

// create a nice text representation of the node
// (traverse tree by recursion, use 'other' pointer for diffing two AST trees)
void AstNode::dumpAst(FILE *f, std::string indent) const
{
	if (f == NULL) {
		for (auto f : log_files)
			dumpAst(f, indent);
		return;
	}

	std::string type_name = type2str(type);
	fprintf(f, "%s%s <%s>", indent.c_str(), type_name.c_str(), loc_string().c_str());

	if (!flag_no_dump_ptr) {
		if (id2ast)
			fprintf(f, " [%p -> %p]", this, id2ast);
		else
			fprintf(f, " [%p]", this);
	}

	if (!str.empty())
		fprintf(f, " str='%s'", str.c_str());
	if (!bits.empty()) {
		fprintf(f, " bits='");
		for (size_t i = bits.size(); i > 0; i--)
			fprintf(f, "%c", bits[i-1] == State::S0 ? '0' :
					bits[i-1] == State::S1 ? '1' :
					bits[i-1] == RTLIL::Sx ? 'x' :
					bits[i-1] == RTLIL::Sz ? 'z' : '?');
		fprintf(f, "'(%d)", GetSize(bits));
	}
	if (is_input)
		fprintf(f, " input");
	if (is_output)
		fprintf(f, " output");
	if (is_logic)
		fprintf(f, " logic");
	if (is_reg) // this is an AST dump, not Verilog - if we see "logic reg" that's fine.
		fprintf(f, " reg");
	if (is_signed)
		fprintf(f, " signed");
	if (is_unsized)
		fprintf(f, " unsized");
	if (basic_prep)
		fprintf(f, " basic_prep");
	if (lookahead)
		fprintf(f, " lookahead");
	if (port_id > 0)
		fprintf(f, " port=%d", port_id);
	if (range_valid || range_left != -1 || range_right != 0)
		fprintf(f, " %srange=[%d:%d]%s", range_swapped ? "swapped_" : "", range_left, range_right, range_valid ? "" : "!");
	if (integer != 0)
		fprintf(f, " int=%u", (int)integer);
	if (realvalue != 0)
		fprintf(f, " real=%e", realvalue);
	if (!dimensions.empty()) {
		fprintf(f, " dimensions=");
		for (auto &dim : dimensions) {
			int left = dim.range_right + dim.range_width - 1;
			int right = dim.range_right;
			if (dim.range_swapped)
				std::swap(left, right);
			fprintf(f, "[%d:%d]", left, right);
		}
	}
	if (is_enum) {
		fprintf(f, " type=enum");
	}
	if (in_lvalue)
		fprintf(f, " in_lvalue");
	if (in_param)
		fprintf(f, " in_param");
	fprintf(f, "\n");

	for (auto &it : attributes) {
		fprintf(f, "%s  ATTR %s:\n", indent.c_str(), it.first.c_str());
		it.second->dumpAst(f, indent + "    ");
	}

	for (size_t i = 0; i < children.size(); i++)
		children[i]->dumpAst(f, indent + "  ");

	fflush(f);
}

// helper function for AstNode::dumpVlog()
static std::string id2vl(std::string txt)
{
	if (txt.size() > 1 && txt[0] == '\\')
		txt = txt.substr(1);
	for (size_t i = 0; i < txt.size(); i++) {
		if ('A' <= txt[i] && txt[i] <= 'Z') continue;
		if ('a' <= txt[i] && txt[i] <= 'z') continue;
		if ('0' <= txt[i] && txt[i] <= '9') continue;
		if (txt[i] == '_') continue;
		txt = "\\" + txt + " ";
		break;
	}
	return txt;
}

// dump AST node as Verilog pseudo-code
void AstNode::dumpVlog(FILE *f, std::string indent) const
{
	bool first = true;
	std::string txt;
	std::vector<AstNode*> rem_children1, rem_children2;

	if (f == NULL) {
		for (auto f : log_files)
			dumpVlog(f, indent);
		return;
	}

	for (auto &it : attributes) {
		fprintf(f, "%s" "(* %s = ", indent.c_str(), id2vl(it.first.str()).c_str());
		it.second->dumpVlog(f, "");
		fprintf(f, " *)%s", indent.empty() ? "" : "\n");
	}

	switch (type)
	{
	case AST_MODULE:
		fprintf(f, "%s" "module %s(", indent.c_str(), id2vl(str).c_str());
		for (auto child : children)
			if (child->type == AST_WIRE && (child->is_input || child->is_output)) {
				fprintf(f, "%s%s", first ? "" : ", ", id2vl(child->str).c_str());
				first = false;
			}
		fprintf(f, ");\n");

		for (auto child : children)
			if (child->type == AST_PARAMETER || child->type == AST_LOCALPARAM || child->type == AST_DEFPARAM)
				child->dumpVlog(f, indent + "  ");
			else
				rem_children1.push_back(child);

		for (auto child : rem_children1)
			if (child->type == AST_WIRE || child->type == AST_AUTOWIRE || child->type == AST_MEMORY)
				child->dumpVlog(f, indent + "  ");
			else
				rem_children2.push_back(child);
		rem_children1.clear();

		for (auto child : rem_children2)
			if (child->type == AST_TASK || child->type == AST_FUNCTION)
				child->dumpVlog(f, indent + "  ");
			else
				rem_children1.push_back(child);
		rem_children2.clear();

		for (auto child : rem_children1)
			child->dumpVlog(f, indent + "  ");
		rem_children1.clear();

		fprintf(f, "%s" "endmodule\n", indent.c_str());
		break;

	case AST_WIRE:
		if (is_input && is_output)
			fprintf(f, "%s" "inout", indent.c_str());
		else if (is_input)
			fprintf(f, "%s" "input", indent.c_str());
		else if (is_output)
			fprintf(f, "%s" "output", indent.c_str());
		else if (!is_reg)
			fprintf(f, "%s" "wire", indent.c_str());
		if (is_reg)
			fprintf(f, "%s" "reg", (is_input || is_output) ? " " : indent.c_str());
		if (is_signed)
			fprintf(f, " signed");
		for (auto child : children) {
			fprintf(f, " ");
			child->dumpVlog(f, "");
		}
		fprintf(f, " %s", id2vl(str).c_str());
		fprintf(f, ";\n");
		break;

	case AST_MEMORY:
		fprintf(f, "%s" "memory", indent.c_str());
		if (is_signed)
			fprintf(f, " signed");
		for (auto child : children) {
			fprintf(f, " ");
			child->dumpVlog(f, "");
			if (first)
				fprintf(f, " %s", id2vl(str).c_str());
			first = false;
		}
		fprintf(f, ";\n");
		break;

	if (0) { case AST_MEMRD:   txt = "@memrd@";  }
	if (0) { case AST_MEMINIT: txt = "@meminit@";  }
	if (0) { case AST_MEMWR:   txt = "@memwr@";  }
		fprintf(f, "%s%s", indent.c_str(), txt.c_str());
		for (auto child : children) {
			fprintf(f, first ? "(" : ", ");
			child->dumpVlog(f, "");
			first = false;
		}
		fprintf(f, ")");
		if (type != AST_MEMRD)
			fprintf(f, ";\n");
		break;

	case AST_RANGE:
		if (range_valid) {
			if (range_swapped)
				fprintf(f, "[%d:%d]", range_right, range_left);
			else
				fprintf(f, "[%d:%d]", range_left, range_right);
		} else {
			for (auto child : children) {
				fprintf(f, "%c", first ? '[' : ':');
				child->dumpVlog(f, "");
				first = false;
			}
			fprintf(f, "]");
		}
		break;

	case AST_MULTIRANGE:
		for (auto child : children)
			child->dumpVlog(f, "");
		break;

	case AST_ALWAYS:
		fprintf(f, "%s" "always @", indent.c_str());
		for (auto child : children) {
			if (child->type != AST_POSEDGE && child->type != AST_NEGEDGE && child->type != AST_EDGE)
				continue;
			fprintf(f, first ? "(" : ", ");
			child->dumpVlog(f, "");
			first = false;
		}
		fprintf(f, first ? "*\n" : ")\n");
		for (auto child : children) {
			if (child->type != AST_POSEDGE && child->type != AST_NEGEDGE && child->type != AST_EDGE)
				child->dumpVlog(f, indent + "  ");
		}
		break;

	case AST_INITIAL:
		fprintf(f, "%s" "initial\n", indent.c_str());
		for (auto child : children) {
			if (child->type != AST_POSEDGE && child->type != AST_NEGEDGE && child->type != AST_EDGE)
				child->dumpVlog(f, indent + "  ");
		}
		break;

	case AST_POSEDGE:
	case AST_NEGEDGE:
	case AST_EDGE:
		if (type == AST_POSEDGE)
			fprintf(f, "posedge ");
		if (type == AST_NEGEDGE)
			fprintf(f, "negedge ");
		for (auto child : children)
			child->dumpVlog(f, "");
		break;

	case AST_IDENTIFIER:
		{
			AstNode *member_node = get_struct_member();
			if (member_node)
				fprintf(f, "%s[%d:%d]", id2vl(str).c_str(), member_node->range_left, member_node->range_right);
			else
				fprintf(f, "%s", id2vl(str).c_str());
		}
		for (auto child : children)
			child->dumpVlog(f, "");
		break;

	case AST_STRUCT:
	case AST_UNION:
	case AST_STRUCT_ITEM:
		fprintf(f, "%s", id2vl(str).c_str());
		break;

	case AST_CONSTANT:
		if (!str.empty())
			fprintf(f, "\"%s\"", str.c_str());
		else if (bits.size() == 32)
			fprintf(f, "%d", RTLIL::Const(bits).as_int());
		else
			fprintf(f, "%d'b %s", GetSize(bits), RTLIL::Const(bits).as_string().c_str());
		break;

	case AST_REALVALUE:
		fprintf(f, "%e", realvalue);
		break;

	case AST_BLOCK:
		if (children.size() == 1) {
			children[0]->dumpVlog(f, indent);
		} else {
			fprintf(f, "%s" "begin\n", indent.c_str());
			for (auto child : children)
				child->dumpVlog(f, indent + "  ");
			fprintf(f, "%s" "end\n", indent.c_str());
		}
		break;

	case AST_CASE:
		if (children.size() > 1 && children[1]->type == AST_CONDX)
			fprintf(f, "%s" "casex (", indent.c_str());
		else if (children.size() > 1 && children[1]->type == AST_CONDZ)
			fprintf(f, "%s" "casez (", indent.c_str());
		else
			fprintf(f, "%s" "case (", indent.c_str());
		children[0]->dumpVlog(f, "");
		fprintf(f, ")\n");
		for (size_t i = 1; i < children.size(); i++) {
			AstNode *child = children[i];
			child->dumpVlog(f, indent + "  ");
		}
		fprintf(f, "%s" "endcase\n", indent.c_str());
		break;

	case AST_COND:
	case AST_CONDX:
	case AST_CONDZ:
		for (auto child : children) {
			if (child->type == AST_BLOCK) {
				fprintf(f, ":\n");
				child->dumpVlog(f, indent + "  ");
				first = true;
			} else {
				fprintf(f, "%s", first ? indent.c_str() : ", ");
				if (child->type == AST_DEFAULT)
					fprintf(f, "default");
				else
					child->dumpVlog(f, "");
				first = false;
			}
		}
		break;

	case AST_ASSIGN:
		fprintf(f, "%sassign ", indent.c_str());
		children[0]->dumpVlog(f, "");
		fprintf(f, " = ");
		children[1]->dumpVlog(f, "");
		fprintf(f, ";\n");
		break;

	case AST_ASSIGN_EQ:
	case AST_ASSIGN_LE:
		fprintf(f, "%s", indent.c_str());
		children[0]->dumpVlog(f, "");
		fprintf(f, " %s ", type == AST_ASSIGN_EQ ? "=" : "<=");
		children[1]->dumpVlog(f, "");
		fprintf(f, ";\n");
		break;

	case AST_CONCAT:
		fprintf(f, "{");
		for (int i = GetSize(children)-1; i >= 0; i--) {
			auto child = children[i];
			if (!first)
				fprintf(f, ", ");
			child->dumpVlog(f, "");
			first = false;
		}
		fprintf(f, "}");
		break;

	case AST_REPLICATE:
		fprintf(f, "{");
		children[0]->dumpVlog(f, "");
		fprintf(f, "{");
		children[1]->dumpVlog(f, "");
		fprintf(f, "}}");
		break;

	if (0) { case AST_BIT_NOT:     txt = "~";  }
	if (0) { case AST_REDUCE_AND:  txt = "&";  }
	if (0) { case AST_REDUCE_OR:   txt = "|";  }
	if (0) { case AST_REDUCE_XOR:  txt = "^";  }
	if (0) { case AST_REDUCE_XNOR: txt = "~^"; }
	if (0) { case AST_REDUCE_BOOL: txt = "|";  }
	if (0) { case AST_POS:         txt = "+";  }
	if (0) { case AST_NEG:         txt = "-";  }
	if (0) { case AST_LOGIC_NOT:   txt = "!";  }
	if (0) { case AST_SELFSZ:      txt = "@selfsz@";  }
	if (0) { case AST_TO_SIGNED:   txt = "signed'";  }
	if (0) { case AST_TO_UNSIGNED: txt = "unsigned'";  }
		fprintf(f, "%s(", txt.c_str());
		children[0]->dumpVlog(f, "");
		fprintf(f, ")");
		break;

	case AST_CAST_SIZE:
		children[0]->dumpVlog(f, "");
		fprintf(f, "'(");
		children[1]->dumpVlog(f, "");
		fprintf(f, ")");
		break;

	if (0) { case AST_BIT_AND:      txt = "&";   }
	if (0) { case AST_BIT_OR:       txt = "|";   }
	if (0) { case AST_BIT_XOR:      txt = "^";   }
	if (0) { case AST_BIT_XNOR:     txt = "~^";  }
	if (0) { case AST_SHIFT_LEFT:   txt = "<<";  }
	if (0) { case AST_SHIFT_RIGHT:  txt = ">>";  }
	if (0) { case AST_SHIFT_SLEFT:  txt = "<<<"; }
	if (0) { case AST_SHIFT_SRIGHT: txt = ">>>"; }
	if (0) { case AST_SHIFTX:       txt = "@shiftx@"; }
	if (0) { case AST_SHIFT:        txt = "@shift@"; }
	if (0) { case AST_LT:           txt = "<";   }
	if (0) { case AST_LE:           txt = "<=";  }
	if (0) { case AST_EQ:           txt = "==";  }
	if (0) { case AST_NE:           txt = "!=";  }
	if (0) { case AST_EQX:          txt = "===";  }
	if (0) { case AST_NEX:          txt = "!==";  }
	if (0) { case AST_GE:           txt = ">=";  }
	if (0) { case AST_GT:           txt = ">";   }
	if (0) { case AST_ADD:          txt = "+";   }
	if (0) { case AST_SUB:          txt = "-";   }
	if (0) { case AST_MUL:          txt = "*";   }
	if (0) { case AST_DIV:          txt = "/";   }
	if (0) { case AST_MOD:          txt = "%";   }
	if (0) { case AST_POW:          txt = "**";  }
	if (0) { case AST_LOGIC_AND:    txt = "&&";  }
	if (0) { case AST_LOGIC_OR:     txt = "||";  }
		fprintf(f, "(");
		children[0]->dumpVlog(f, "");
		fprintf(f, ")%s(", txt.c_str());
		children[1]->dumpVlog(f, "");
		fprintf(f, ")");
		break;

	case AST_TERNARY:
		fprintf(f, "(");
		children[0]->dumpVlog(f, "");
		fprintf(f, ") ? (");
		children[1]->dumpVlog(f, "");
		fprintf(f, ") : (");
		children[2]->dumpVlog(f, "");
		fprintf(f, ")");
		break;

	default:
		std::string type_name = type2str(type);
		fprintf(f, "%s" "/** %s **/%s", indent.c_str(), type_name.c_str(), indent.empty() ? "" : "\n");
		// dumpAst(f, indent, NULL);
	}

	fflush(f);
}

// check if two AST nodes are identical
bool AstNode::operator==(const AstNode &other) const
{
	if (type != other.type)
		return false;
	if (children.size() != other.children.size())
		return false;
	if (str != other.str)
		return false;
	if (bits != other.bits)
		return false;
	if (is_input != other.is_input)
		return false;
	if (is_output != other.is_output)
		return false;
	if (is_logic != other.is_logic)
		return false;
	if (is_reg != other.is_reg)
		return false;
	if (is_signed != other.is_signed)
		return false;
	if (is_string != other.is_string)
		return false;
	if (range_valid != other.range_valid)
		return false;
	if (range_swapped != other.range_swapped)
		return false;
	if (port_id != other.port_id)
		return false;
	if (range_left != other.range_left)
		return false;
	if (range_right != other.range_right)
		return false;
	if (integer != other.integer)
		return false;
	for (size_t i = 0; i < children.size(); i++)
		if (*children[i] != *other.children[i])
			return false;
	return true;
}

// check if two AST nodes are not identical
bool AstNode::operator!=(const AstNode &other) const
{
	return !(*this == other);
}

// check if this AST contains the given node
bool AstNode::contains(const AstNode *other) const
{
	if (this == other)
		return true;
	for (auto child : children)
		if (child->contains(other))
			return true;
	return false;
}

// create an AST node for a constant (using a 32 bit int as value)
AstNode *AstNode::mkconst_int(uint32_t v, bool is_signed, int width)
{
	AstNode *node = new AstNode(AST_CONSTANT);
	node->integer = v;
	node->is_signed = is_signed;
	for (int i = 0; i < width; i++) {
		node->bits.push_back((v & 1) ? State::S1 : State::S0);
		v = v >> 1;
	}
	node->range_valid = true;
	node->range_left = width-1;
	node->range_right = 0;
	return node;
}

// create an AST node for a constant (using a bit vector as value)
AstNode *AstNode::mkconst_bits(const std::vector<RTLIL::State> &v, bool is_signed, bool is_unsized)
{
	AstNode *node = new AstNode(AST_CONSTANT);
	node->is_signed = is_signed;
	node->bits = v;
	for (size_t i = 0; i < 32; i++) {
		if (i < node->bits.size())
			node->integer |= (node->bits[i] == State::S1) << i;
		else if (is_signed && !node->bits.empty())
			node->integer |= (node->bits.back() == State::S1) << i;
	}
	node->range_valid = true;
	node->range_left = node->bits.size()-1;
	node->range_right = 0;
	node->is_unsized = is_unsized;
	return node;
}

AstNode *AstNode::mkconst_bits(const std::vector<RTLIL::State> &v, bool is_signed)
{
	return mkconst_bits(v, is_signed, false);
}

// create an AST node for a constant (using a string in bit vector form as value)
AstNode *AstNode::mkconst_str(const std::vector<RTLIL::State> &v)
{
	AstNode *node = mkconst_str(RTLIL::Const(v).decode_string());
	while (GetSize(node->bits) < GetSize(v))
		node->bits.push_back(RTLIL::State::S0);
	log_assert(node->bits == v);
	return node;
}

// create an AST node for a constant (using a string as value)
AstNode *AstNode::mkconst_str(const std::string &str)
{
	std::vector<RTLIL::State> data;
	data.reserve(str.size() * 8);
	for (size_t i = 0; i < str.size(); i++) {
		unsigned char ch = str[str.size() - i - 1];
		for (int j = 0; j < 8; j++) {
			data.push_back((ch & 1) ? State::S1 : State::S0);
			ch = ch >> 1;
		}
	}
	AstNode *node = AstNode::mkconst_bits(data, false);
	node->is_string = true;
	node->str = str;
	return node;
}

// create a temporary register
AstNode *AstNode::mktemp_logic(const std::string &name, AstNode *mod, bool nosync, int range_left, int range_right, bool is_signed)
{
	AstNode *wire = new AstNode(AST_WIRE, new AstNode(AST_RANGE, mkconst_int(range_left, true), mkconst_int(range_right, true)));
	wire->str = stringf("%s%s:%d$%d", name.c_str(), RTLIL::encode_filename(filename).c_str(), location.first_line, autoidx++);
	if (nosync)
		wire->set_attribute(ID::nosync, AstNode::mkconst_int(1, false));
	wire->is_signed = is_signed;
	wire->is_logic = true;
	mod->children.push_back(wire);
	while (wire->simplify(true, 1, -1, false)) { }

	AstNode *ident = new AstNode(AST_IDENTIFIER);
	ident->str = wire->str;
	ident->id2ast = wire;

	return ident;
}

bool AstNode::bits_only_01() const
{
	for (auto bit : bits)
		if (bit != State::S0 && bit != State::S1)
			return false;
	return true;
}

RTLIL::Const AstNode::bitsAsUnsizedConst(int width)
{
	RTLIL::State extbit = bits.back();
	while (width > int(bits.size()))
		bits.push_back(extbit);
	return RTLIL::Const(bits);
}

RTLIL::Const AstNode::bitsAsConst(int width, bool is_signed)
{
	std::vector<RTLIL::State> bits = this->bits;
	if (width >= 0 && width < int(bits.size()))
		bits.resize(width);
	if (width >= 0 && width > int(bits.size())) {
		RTLIL::State extbit = RTLIL::State::S0;
		if ((is_signed || is_unsized) && !bits.empty())
			extbit = bits.back();
		while (width > int(bits.size()))
			bits.push_back(extbit);
	}
	return RTLIL::Const(bits);
}

RTLIL::Const AstNode::bitsAsConst(int width)
{
	return bitsAsConst(width, is_signed);
}

RTLIL::Const AstNode::asAttrConst() const
{
	log_assert(type == AST_CONSTANT);

	RTLIL::Const val;
	val.bits = bits;

	if (is_string) {
		val.flags |= RTLIL::CONST_FLAG_STRING;
		log_assert(val.decode_string() == str);
	}

	return val;
}

RTLIL::Const AstNode::asParaConst() const
{
	if (type == AST_REALVALUE)
	{
		AstNode *strnode = AstNode::mkconst_str(stringf("%f", realvalue));
		RTLIL::Const val = strnode->asAttrConst();
		val.flags |= RTLIL::CONST_FLAG_REAL;
		delete strnode;
		return val;
	}

	RTLIL::Const val = asAttrConst();
	if (is_signed)
		val.flags |= RTLIL::CONST_FLAG_SIGNED;
	return val;
}

bool AstNode::asBool() const
{
	log_assert(type == AST_CONSTANT);
	for (auto &bit : bits)
		if (bit == RTLIL::State::S1)
			return true;
	return false;
}

int AstNode::isConst() const
{
	if (type == AST_CONSTANT)
		return 1;
	if (type == AST_REALVALUE)
		return 2;
	return 0;
}

uint64_t AstNode::asInt(bool is_signed)
{
	if (type == AST_CONSTANT)
	{
		RTLIL::Const v = bitsAsConst(64, is_signed);
		uint64_t ret = 0;

		for (int i = 0; i < 64; i++)
			if (v.bits.at(i) == RTLIL::State::S1)
				ret |= uint64_t(1) << i;

		return ret;
	}

	if (type == AST_REALVALUE)
		return uint64_t(realvalue);

	log_abort();
}

double AstNode::asReal(bool is_signed)
{
	if (type == AST_CONSTANT)
	{
		RTLIL::Const val(bits);

		bool is_negative = is_signed && !val.bits.empty() && val.bits.back() == RTLIL::State::S1;
		if (is_negative)
			val = const_neg(val, val, false, false, val.bits.size());

		double v = 0;
		for (size_t i = 0; i < val.bits.size(); i++)
			// IEEE Std 1800-2012 Par 6.12.2: Individual bits that are x or z in
			// the net or the variable shall be treated as zero upon conversion.
			if (val.bits.at(i) == RTLIL::State::S1)
				v += exp2(i);
		if (is_negative)
			v *= -1;

		return v;
	}

	if (type == AST_REALVALUE)
		return realvalue;

	log_abort();
}

RTLIL::Const AstNode::realAsConst(int width)
{
	double v = round(realvalue);
	RTLIL::Const result;
#ifdef EMSCRIPTEN
	if (!isfinite(v)) {
#else
	if (!std::isfinite(v)) {
#endif
		result.bits = std::vector<RTLIL::State>(width, RTLIL::State::Sx);
	} else {
		bool is_negative = v < 0;
		if (is_negative)
			v *= -1;
		for (int i = 0; i < width; i++, v /= 2)
			result.bits.push_back((fmod(floor(v), 2) != 0) ? RTLIL::State::S1 : RTLIL::State::S0);
		if (is_negative)
			result = const_neg(result, result, false, false, result.bits.size());
	}
	return result;
}

std::string AstNode::loc_string() const
{
	return stringf("%s:%d.%d-%d.%d", filename.c_str(), location.first_line, location.first_column, location.last_line, location.last_column);
}

void AST::set_src_attr(RTLIL::AttrObject *obj, const AstNode *ast)
{
	obj->attributes[ID::src] = ast->loc_string();
}

static bool param_has_no_default(const AstNode *param) {
	const auto &children = param->children;
	log_assert(param->type == AST_PARAMETER);
	log_assert(children.size() <= 2);
	return children.empty() ||
		(children.size() == 1 && children[0]->type == AST_RANGE);
}

static RTLIL::Module *process_module(RTLIL::Design *design, AstNode *ast, bool defer, AstNode *original_ast = NULL, bool quiet = false)
{
	log_assert(current_scope.empty());
	log_assert(ast->type == AST_MODULE || ast->type == AST_INTERFACE);

	if (defer)
		log("Storing AST representation for module `%s'.\n", ast->str.c_str());
	else if (!quiet) {
		log("Generating RTLIL representation for module `%s'.\n", ast->str.c_str());
	}

	AstModule *module = new AstModule;
	current_module = module;

	module->ast = NULL;
	module->name = ast->str;
	set_src_attr(module, ast);
	module->set_bool_attribute(ID::cells_not_processed);

	current_ast_mod = ast;
	AstNode *ast_before_simplify;
	if (original_ast != NULL)
		ast_before_simplify = original_ast;
	else
		ast_before_simplify = ast->clone();

	if (flag_dump_ast1) {
		log("Dumping AST before simplification:\n");
		ast->dumpAst(NULL, "    ");
		log("--- END OF AST DUMP ---\n");
	}
	if (flag_dump_vlog1) {
		log("Dumping Verilog AST before simplification:\n");
		ast->dumpVlog(NULL, "    ");
		log("--- END OF AST DUMP ---\n");
	}

	if (!defer)
	{
		for (const AstNode *node : ast->children)
			if (node->type == AST_PARAMETER && param_has_no_default(node))
				node->input_error("Parameter `%s' has no default value and has not been overridden!\n", node->str.c_str());

		bool blackbox_module = flag_lib;

		if (!blackbox_module && !flag_noblackbox) {
			blackbox_module = true;
			for (auto child : ast->children) {
				if (child->type == AST_WIRE && (child->is_input || child->is_output))
					continue;
				if (child->type == AST_PARAMETER || child->type == AST_LOCALPARAM)
					continue;
				if (child->type == AST_CELL && child->children.size() > 0 && child->children[0]->type == AST_CELLTYPE &&
						(child->children[0]->str == "$specify2" || child->children[0]->str == "$specify3" || child->children[0]->str == "$specrule"))
					continue;
				blackbox_module = false;
				break;
			}
		}

		// simplify this module or interface using the current design as context
		// for lookup up ports and wires within cells
		set_simplify_design_context(design);
		while (ast->simplify(!flag_noopt, 0, -1, false)) { }
		set_simplify_design_context(nullptr);

		if (flag_dump_ast2) {
			log("Dumping AST after simplification:\n");
			ast->dumpAst(NULL, "    ");
			log("--- END OF AST DUMP ---\n");
		}

		if (flag_dump_vlog2) {
			log("Dumping Verilog AST after simplification:\n");
			ast->dumpVlog(NULL, "    ");
			log("--- END OF AST DUMP ---\n");
		}

		if (flag_nowb && ast->attributes.count(ID::whitebox)) {
			delete ast->attributes.at(ID::whitebox);
			ast->attributes.erase(ID::whitebox);
		}

		if (ast->attributes.count(ID::lib_whitebox)) {
			if (!flag_lib || flag_nowb) {
				delete ast->attributes.at(ID::lib_whitebox);
				ast->attributes.erase(ID::lib_whitebox);
			} else {
				if (ast->attributes.count(ID::whitebox)) {
					delete ast->attributes.at(ID::whitebox);
					ast->attributes.erase(ID::whitebox);
				}
				AstNode *n = ast->attributes.at(ID::lib_whitebox);
				ast->set_attribute(ID::whitebox, n);
				ast->attributes.erase(ID::lib_whitebox);
			}
		}

		if (!blackbox_module && ast->attributes.count(ID::blackbox)) {
			AstNode *n = ast->attributes.at(ID::blackbox);
			if (n->type != AST_CONSTANT)
				ast->input_error("Got blackbox attribute with non-constant value!\n");
			blackbox_module = n->asBool();
		}

		if (blackbox_module && ast->attributes.count(ID::whitebox)) {
			AstNode *n = ast->attributes.at(ID::whitebox);
			if (n->type != AST_CONSTANT)
				ast->input_error("Got whitebox attribute with non-constant value!\n");
			blackbox_module = !n->asBool();
		}

		if (ast->attributes.count(ID::noblackbox)) {
			if (blackbox_module) {
				AstNode *n = ast->attributes.at(ID::noblackbox);
				if (n->type != AST_CONSTANT)
					ast->input_error("Got noblackbox attribute with non-constant value!\n");
				blackbox_module = !n->asBool();
			}
			delete ast->attributes.at(ID::noblackbox);
			ast->attributes.erase(ID::noblackbox);
		}

		if (blackbox_module)
		{
			if (ast->attributes.count(ID::whitebox)) {
				delete ast->attributes.at(ID::whitebox);
				ast->attributes.erase(ID::whitebox);
			}

			if (ast->attributes.count(ID::lib_whitebox)) {
				delete ast->attributes.at(ID::lib_whitebox);
				ast->attributes.erase(ID::lib_whitebox);
			}

			std::vector<AstNode*> new_children;
			for (auto child : ast->children) {
				if (child->type == AST_WIRE && (child->is_input || child->is_output)) {
					new_children.push_back(child);
				} else if (child->type == AST_PARAMETER) {
					new_children.push_back(child);
				} else if (child->type == AST_CELL && child->children.size() > 0 && child->children[0]->type == AST_CELLTYPE &&
						(child->children[0]->str == "$specify2" || child->children[0]->str == "$specify3" || child->children[0]->str == "$specrule")) {
					new_children.push_back(child);
				} else {
					delete child;
				}
			}

			ast->children.swap(new_children);

			if (ast->attributes.count(ID::blackbox) == 0) {
				ast->set_attribute(ID::blackbox, AstNode::mkconst_int(1, false));
			}
		}

		ignoreThisSignalsInInitial = RTLIL::SigSpec();

		for (auto &attr : ast->attributes) {
			if (attr.second->type != AST_CONSTANT)
				ast->input_error("Attribute `%s' with non-constant value!\n", attr.first.c_str());
			module->attributes[attr.first] = attr.second->asAttrConst();
		}
		for (size_t i = 0; i < ast->children.size(); i++) {
			AstNode *node = ast->children[i];
			if (node->type == AST_WIRE || node->type == AST_MEMORY)
				node->genRTLIL();
		}
		for (size_t i = 0; i < ast->children.size(); i++) {
			AstNode *node = ast->children[i];
			if (node->type != AST_WIRE && node->type != AST_MEMORY && node->type != AST_INITIAL)
				node->genRTLIL();
		}

		ignoreThisSignalsInInitial.sort_and_unify();

		for (size_t i = 0; i < ast->children.size(); i++) {
			AstNode *node = ast->children[i];
			if (node->type == AST_INITIAL)
				node->genRTLIL();
		}

		ignoreThisSignalsInInitial = RTLIL::SigSpec();
		current_scope.clear();
	}
	else {
		for (auto &attr : ast->attributes) {
			if (attr.second->type != AST_CONSTANT)
				continue;
			module->attributes[attr.first] = attr.second->asAttrConst();
		}
		for (const AstNode *node : ast->children)
			if (node->type == AST_PARAMETER)
				current_module->avail_parameters(node->str);
	}

	if (ast->type == AST_INTERFACE)
		module->set_bool_attribute(ID::is_interface);
	module->ast = ast_before_simplify;
	module->nolatches = flag_nolatches;
	module->nomeminit = flag_nomeminit;
	module->nomem2reg = flag_nomem2reg;
	module->mem2reg = flag_mem2reg;
	module->noblackbox = flag_noblackbox;
	module->lib = flag_lib;
	module->nowb = flag_nowb;
	module->noopt = flag_noopt;
	module->icells = flag_icells;
	module->pwires = flag_pwires;
	module->autowire = flag_autowire;
	module->fixup_ports();

	if (flag_dump_rtlil) {
		log("Dumping generated RTLIL:\n");
		log_module(module);
		log("--- END OF RTLIL DUMP ---\n");
	}

	design->add(current_module);
	return current_module;
}

RTLIL::Module *
AST_INTERNAL::process_and_replace_module(RTLIL::Design *design,
                                         RTLIL::Module *old_module,
                                         AstNode *new_ast,
                                         AstNode *original_ast)
{
	// The old module will be deleted. Rename and mark for deletion, using
	// a static counter to make sure we get a unique name.
	static unsigned counter;
	std::ostringstream new_name;
	new_name << old_module->name.str()
		 << "_before_process_and_replace_module_"
		 << counter;
	++counter;

	design->rename(old_module, new_name.str());
	old_module->set_bool_attribute(ID::to_delete);

	// Check if the module was the top module. If it was, we need to remove
	// the top attribute and put it on the new module.
	bool is_top = false;
	if (old_module->get_bool_attribute(ID::initial_top)) {
		old_module->attributes.erase(ID::initial_top);
		is_top = true;
	}

	// Generate RTLIL from AST for the new module and add to the design:
	RTLIL::Module* new_module = process_module(design, new_ast, false, original_ast);

	if (is_top)
		new_module->set_bool_attribute(ID::top);

	return new_module;
}

// renames identifiers in tasks and functions within a package
static void rename_in_package_stmts(AstNode *pkg)
{
	std::unordered_set<std::string> idents;
	for (AstNode *item : pkg->children)
		idents.insert(item->str);
	std::function<void(AstNode*)> rename =
		[&rename, &idents, pkg](AstNode *node) {
			for (AstNode *child : node->children) {
				if (idents.count(child->str))
					child->str = pkg->str + "::" + child->str.substr(1);
				rename(child);
			}
	};
	for (AstNode *item : pkg->children)
		if (item->type == AST_FUNCTION || item->type == AST_TASK)
			rename(item);
}

// create AstModule instances for all modules in the AST tree and add them to 'design'
void AST::process(RTLIL::Design *design, AstNode *ast, bool nodisplay, bool dump_ast1, bool dump_ast2, bool no_dump_ptr, bool dump_vlog1, bool dump_vlog2, bool dump_rtlil,
		bool nolatches, bool nomeminit, bool nomem2reg, bool mem2reg, bool noblackbox, bool lib, bool nowb, bool noopt, bool icells, bool pwires, bool nooverwrite, bool overwrite, bool defer, bool autowire)
{
	current_ast = ast;
	current_ast_mod = nullptr;
	flag_nodisplay = nodisplay;
	flag_dump_ast1 = dump_ast1;
	flag_dump_ast2 = dump_ast2;
	flag_no_dump_ptr = no_dump_ptr;
	flag_dump_vlog1 = dump_vlog1;
	flag_dump_vlog2 = dump_vlog2;
	flag_dump_rtlil = dump_rtlil;
	flag_nolatches = nolatches;
	flag_nomeminit = nomeminit;
	flag_nomem2reg = nomem2reg;
	flag_mem2reg = mem2reg;
	flag_noblackbox = noblackbox;
	flag_lib = lib;
	flag_nowb = nowb;
	flag_noopt = noopt;
	flag_icells = icells;
	flag_pwires = pwires;
	flag_autowire = autowire;

	ast->fixup_hierarchy_flags(true);

	log_assert(current_ast->type == AST_DESIGN);
	for (AstNode *child : current_ast->children)
	{
		if (child->type == AST_MODULE || child->type == AST_INTERFACE)
		{
			for (auto n : design->verilog_globals)
				child->children.push_back(n->clone());

			// append nodes from previous packages using package-qualified names
			for (auto &n : design->verilog_packages) {
				for (auto &o : n->children) {
					AstNode *cloned_node = o->clone();
					// log("cloned node %s\n", type2str(cloned_node->type).c_str());
					if (cloned_node->type == AST_ENUM) {
						for (auto &e : cloned_node->children) {
							log_assert(e->type == AST_ENUM_ITEM);
							e->str = n->str + std::string("::") + e->str.substr(1);
						}
					} else {
						cloned_node->str = n->str + std::string("::") + cloned_node->str.substr(1);
					}
					child->children.push_back(cloned_node);
				}
			}

			if (flag_icells && child->str.compare(0, 2, "\\$") == 0)
				child->str = child->str.substr(1);

			bool defer_local = defer;
			if (!defer_local)
				for (const AstNode *node : child->children)
					if (node->type == AST_PARAMETER && param_has_no_default(node))
					{
						log("Deferring `%s' because it contains parameter(s) without defaults.\n", child->str.c_str());
						defer_local = true;
						break;
					}


			if (defer_local)
				child->str = "$abstract" + child->str;

			if (design->has(child->str)) {
				RTLIL::Module *existing_mod = design->module(child->str);
				if (!nooverwrite && !overwrite && !existing_mod->get_blackbox_attribute()) {
					log_file_error(child->filename, child->location.first_line, "Re-definition of module `%s'!\n", child->str.c_str());
				} else if (nooverwrite) {
					log("Ignoring re-definition of module `%s' at %s.\n",
							child->str.c_str(), child->loc_string().c_str());
					continue;
				} else {
					log("Replacing existing%s module `%s' at %s.\n",
							existing_mod->get_bool_attribute(ID::blackbox) ? " blackbox" : "",
							child->str.c_str(), child->loc_string().c_str());
					design->remove(existing_mod);
				}
			}

			process_module(design, child, defer_local);
			current_ast_mod = nullptr;
		}
		else if (child->type == AST_PACKAGE) {
			// process enum/other declarations
			child->simplify(true, 1, -1, false);
			rename_in_package_stmts(child);
			design->verilog_packages.push_back(child->clone());
			current_scope.clear();
		}
		else if (child->type == AST_BIND) {
			// top-level bind construct
			for (RTLIL::Binding *binding : child->genBindings())
				design->add(binding);
		}
		else {
			// must be global definition
			if (child->type == AST_PARAMETER)
				child->type = AST_LOCALPARAM; // cannot be overridden
			design->verilog_globals.push_back(child->clone());
			current_scope.clear();
		}
	}
}

// AstModule destructor
AstModule::~AstModule()
{
	if (ast != NULL)
		delete ast;
}


// An interface port with modport is specified like this:
//    <interface_name>.<modport_name>
// This function splits the interface_name from the modport_name, and fails if it is not a valid combination
std::pair<std::string,std::string> AST::split_modport_from_type(std::string name_type)
{
	std::string interface_type = "";
	std::string interface_modport = "";
	size_t ndots = std::count(name_type.begin(), name_type.end(), '.');
	// Separate the interface instance name from any modports:
	if (ndots == 0) { // Does not have modport
		interface_type = name_type;
	}
	else {
		std::stringstream name_type_stream(name_type);
		std::string segment;
		std::vector<std::string> seglist;
		while(std::getline(name_type_stream, segment, '.')) {
			seglist.push_back(segment);
		}
		if (ndots == 1) { // Has modport
			interface_type = seglist[0];
			interface_modport = seglist[1];
		}
		else { // Erroneous port type
			log_error("More than two '.' in signal port type (%s)\n", name_type.c_str());
		}
	}
	return std::pair<std::string,std::string>(interface_type, interface_modport);

}

AstNode * AST::find_modport(AstNode *intf, std::string name)
{
	for (auto &ch : intf->children)
		if (ch->type == AST_MODPORT)
			if (ch->str == name) // Modport found
				return ch;
	return NULL;
}

// Iterate over all wires in an interface and add them as wires in the AST module:
void AST::explode_interface_port(AstNode *module_ast, RTLIL::Module * intfmodule, std::string intfname, AstNode *modport)
{
	for (auto w : intfmodule->wires()){
		AstNode *wire = new AstNode(AST_WIRE, new AstNode(AST_RANGE, AstNode::mkconst_int(w->width -1, true), AstNode::mkconst_int(0, true)));
		std::string origname = log_id(w->name);
		std::string newname = intfname + "." + origname;
		wire->str = newname;
		if (modport != NULL) {
			bool found_in_modport = false;
			// Search for the current wire in the wire list for the current modport
			for (auto &ch : modport->children) {
				if (ch->type == AST_MODPORTMEMBER) {
					std::string compare_name = "\\" + origname;
					if (ch->str == compare_name) { // Found signal. The modport decides whether it is input or output
						found_in_modport = true;
						wire->is_input = ch->is_input;
						wire->is_output = ch->is_output;
						break;
					}
				}
			}
			if (found_in_modport) {
				module_ast->children.push_back(wire);
			}
			else { // If not found in modport, do not create port
				delete wire;
			}
		}
		else { // If no modport, set inout
			wire->is_input = true;
			wire->is_output = true;
			module_ast->children.push_back(wire);
		}
	}
}

// AstModules may contain cells marked with ID::reprocess_after, which indicates
// that it should be reprocessed once the specified module has been elaborated.
bool AstModule::reprocess_if_necessary(RTLIL::Design *design)
{
	for (const RTLIL::Cell *cell : cells())
	{
		std::string modname = cell->get_string_attribute(ID::reprocess_after);
		if (modname.empty())
			continue;
		if (design->module(modname) || design->module("$abstract" + modname)) {
			log("Reprocessing module %s because instantiated module %s has become available.\n",
					log_id(name), log_id(modname));
			loadconfig();
			process_and_replace_module(design, this, ast, NULL);
			return true;
		}
	}
	return false;
}

// When an interface instance is found in a module, the whole RTLIL for the module will be rederived again
// from AST. The interface members are copied into the AST module with the prefix of the interface.
void AstModule::expand_interfaces(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Module*> &local_interfaces)
{
	loadconfig();

	AstNode *new_ast = ast->clone();
	for (auto &intf : local_interfaces) {
		std::string intfname = intf.first.str();
		RTLIL::Module *intfmodule = intf.second;
		for (auto w : intfmodule->wires()){
			AstNode *wire = new AstNode(AST_WIRE, new AstNode(AST_RANGE, AstNode::mkconst_int(w->width -1, true), AstNode::mkconst_int(0, true)));
			std::string newname = log_id(w->name);
			newname = intfname + "." + newname;
			wire->str = newname;
			new_ast->children.push_back(wire);
		}
	}

	AstNode *ast_before_replacing_interface_ports = new_ast->clone();

	// Explode all interface ports. Note this will only have an effect on 'top
	// level' modules. Other sub-modules will have their interface ports
	// exploded via the derive(..) function
	for (size_t i =0; i<new_ast->children.size(); i++)
	{
		AstNode *ch2 = new_ast->children[i];
		if (ch2->type == AST_INTERFACEPORT) { // Is an interface port
			std::string name_port = ch2->str; // Name of the interface port
			if (ch2->children.size() > 0) {
				for(size_t j=0; j<ch2->children.size();j++) {
					AstNode *ch = ch2->children[j];
					if(ch->type == AST_INTERFACEPORTTYPE) { // Found the AST node containing the type of the interface
						std::pair<std::string,std::string> res = split_modport_from_type(ch->str);
						std::string interface_type = res.first;
						std::string interface_modport = res.second; // Is "", if no modport
						if (design->module(interface_type) != nullptr) {
							// Add a cell to the module corresponding to the interface port such that
							// it can further propagated down if needed:
							AstNode *celltype_for_intf = new AstNode(AST_CELLTYPE);
							celltype_for_intf->str = interface_type;
							AstNode *cell_for_intf = new AstNode(AST_CELL, celltype_for_intf);
							cell_for_intf->str = name_port + "_inst_from_top_dummy";
							new_ast->children.push_back(cell_for_intf);

							// Get all members of this non-overridden dummy interface instance:
							RTLIL::Module *intfmodule = design->module(interface_type); // All interfaces should at this point in time (assuming
							                                                              // reprocess_module is called from the hierarchy pass) be
							                                                              // present in design->modules_
							AstModule *ast_module_of_interface = (AstModule*)intfmodule;
							std::string interface_modport_compare_str = "\\" + interface_modport;
							AstNode *modport = find_modport(ast_module_of_interface->ast, interface_modport_compare_str); // modport == NULL if no modport
							// Iterate over all wires in the interface and add them to the module:
							explode_interface_port(new_ast, intfmodule, name_port, modport);
						}
						break;
					}
				}
			}
		}
	}

	// Generate RTLIL from AST for the new module and add to the design,
	// renaming this module to move it out of the way.
	RTLIL::Module* new_module =
		process_and_replace_module(design, this, new_ast, ast_before_replacing_interface_ports);

	delete new_ast;

	// Set the attribute "interfaces_replaced_in_module" so that it does not happen again.
	new_module->set_bool_attribute(ID::interfaces_replaced_in_module);
}

// create a new parametric module (when needed) and return the name of the generated module - WITH support for interfaces
// This method is used to explode the interface when the interface is a port of the module (not instantiated inside)
RTLIL::IdString AstModule::derive(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, const dict<RTLIL::IdString, RTLIL::Module*> &interfaces, const dict<RTLIL::IdString, RTLIL::IdString> &modports, bool /*mayfail*/)
{
	AstNode *new_ast = NULL;
	std::string modname = derive_common(design, parameters, &new_ast);

	// Since interfaces themselves may be instantiated with different parameters,
	// "modname" must also take those into account, so that unique modules
	// are derived for any variant of interface connections:
	std::string interf_info = "";

	bool has_interfaces = false;
	for(auto &intf : interfaces) {
		interf_info += log_id(intf.second->name);
		has_interfaces = true;
	}

	std::string new_modname = modname;
	if (has_interfaces)
		new_modname += "$interfaces$" + interf_info;


	if (!design->has(new_modname)) {
		if (!new_ast) {
			auto mod = dynamic_cast<AstModule*>(design->module(modname));
			new_ast = mod->ast->clone();
		}
		modname = new_modname;
		new_ast->str = modname;

		// Iterate over all interfaces which are ports in this module:
		for(auto &intf : interfaces) {
			RTLIL::Module * intfmodule = intf.second;
			std::string intfname = intf.first.str();
			// Check if a modport applies for the interface port:
			AstNode *modport = NULL;
			if (modports.count(intfname) > 0) {
				std::string interface_modport = modports.at(intfname).str();
				AstModule *ast_module_of_interface = (AstModule*)intfmodule;
				AstNode *ast_node_of_interface = ast_module_of_interface->ast;
				modport = find_modport(ast_node_of_interface, interface_modport);
			}
			// Iterate over all wires in the interface and add them to the module:
			explode_interface_port(new_ast, intfmodule, intfname, modport);
		}

		process_module(design, new_ast, false);
		design->module(modname)->check();

		RTLIL::Module* mod = design->module(modname);

		// Now that the interfaces have been exploded, we can delete the dummy port related to every interface.
		for(auto &intf : interfaces) {
			if(mod->wire(intf.first) != nullptr) {
				// Normally, removing wires would be batched together as it's an
				//   expensive operation, however, in this case doing so would mean
				//   that a cell with the same name cannot be created (below)...
				// Since we won't expect many interfaces to exist in a module,
				//   we can let this slide...
				pool<RTLIL::Wire*> to_remove;
				to_remove.insert(mod->wire(intf.first));
				mod->remove(to_remove);
				mod->fixup_ports();
				// We copy the cell of the interface to the sub-module such that it
				//   can further be found if it is propagated down to sub-sub-modules etc.
				RTLIL::Cell *new_subcell = mod->addCell(intf.first, intf.second->name);
				new_subcell->set_bool_attribute(ID::is_interface);
			}
			else {
				log_error("No port with matching name found (%s) in %s. Stopping\n", log_id(intf.first), modname.c_str());
			}
		}

		// If any interfaces were replaced, set the attribute 'interfaces_replaced_in_module':
		if (interfaces.size() > 0) {
			mod->set_bool_attribute(ID::interfaces_replaced_in_module);
		}

	} else {
		modname = new_modname;
		log("Found cached RTLIL representation for module `%s'.\n", modname.c_str());
	}

	delete new_ast;
	return modname;
}

// create a new parametric module (when needed) and return the name of the generated module - without support for interfaces
RTLIL::IdString AstModule::derive(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, bool /*mayfail*/)
{
	bool quiet = false;
	log("quiet %d\n", quiet);

	AstNode *new_ast = NULL;
	std::string modname = derive_common(design, parameters, &new_ast, quiet);

	if (!design->has(modname) && new_ast) {
		new_ast->str = modname;
		process_module(design, new_ast, false, NULL, quiet);
		design->module(modname)->check();
	} else if (!quiet) {
		log("Found cached RTLIL representation for module `%s'.\n", modname.c_str());
	}

	delete new_ast;
	return modname;
}

static std::string serialize_param_value(const RTLIL::Const &val) {
	std::string res;
	if (val.flags & RTLIL::ConstFlags::CONST_FLAG_STRING)
		res.push_back('t');
	if (val.flags & RTLIL::ConstFlags::CONST_FLAG_SIGNED)
		res.push_back('s');
	if (val.flags & RTLIL::ConstFlags::CONST_FLAG_REAL)
		res.push_back('r');
	res += stringf("%d", GetSize(val));
	res.push_back('\'');
	for (int i = GetSize(val) - 1; i >= 0; i--) {
		switch (val.bits[i]) {
			case RTLIL::State::S0: res.push_back('0'); break;
			case RTLIL::State::S1: res.push_back('1'); break;
			case RTLIL::State::Sx: res.push_back('x'); break;
			case RTLIL::State::Sz: res.push_back('z'); break;
			case RTLIL::State::Sa: res.push_back('?'); break;
			case RTLIL::State::Sm: res.push_back('m'); break;
		}
	}
	return res;
}

std::string AST::derived_module_name(std::string stripped_name, const std::vector<std::pair<RTLIL::IdString, RTLIL::Const>> &parameters) {
	std::string para_info;
	for (const auto &elem : parameters)
		para_info += stringf("%s=%s", elem.first.c_str(), serialize_param_value(elem.second).c_str());

	if (para_info.size() > 60)
		return "$paramod$" + sha1(para_info) + stripped_name;
	else
		return "$paramod" + stripped_name + para_info;
}

// create a new parametric module (when needed) and return the name of the generated module
std::string AstModule::derive_common(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, AstNode **new_ast_out, bool quiet)
{
	std::string stripped_name = name.str();
	(*new_ast_out) = nullptr;

	if (stripped_name.compare(0, 9, "$abstract") == 0)
		stripped_name = stripped_name.substr(9);

	int para_counter = 0;
	std::vector<std::pair<RTLIL::IdString, RTLIL::Const>> named_parameters;
	for (const auto child : ast->children) {
		if (child->type != AST_PARAMETER)
			continue;
		para_counter++;
		auto it = parameters.find(child->str);
		if (it != parameters.end()) {
			if (!quiet)
				log("Parameter %s = %s\n", child->str.c_str(), log_signal(it->second));
			named_parameters.emplace_back(child->str, it->second);
			continue;
		}
		it = parameters.find(stringf("$%d", para_counter));
		if (it != parameters.end()) {
			if (!quiet)
				log("Parameter %d (%s) = %s\n", para_counter, child->str.c_str(), log_signal(it->second));
			named_parameters.emplace_back(child->str, it->second);
			continue;
		}
	}

	std::string modname = stripped_name;
	if (parameters.size()) // not named_parameters to cover hierarchical defparams
		modname = derived_module_name(stripped_name, named_parameters);

	if (design->has(modname))
		return modname;

	if (!quiet)
		log_header(design, "Executing AST frontend in derive mode using pre-parsed AST for module `%s'.\n", stripped_name.c_str());
	loadconfig();

	pool<IdString> rewritten;
	rewritten.reserve(GetSize(parameters));

	AstNode *new_ast = ast->clone();
	if (!new_ast->attributes.count(ID::hdlname))
		new_ast->set_attribute(ID::hdlname, AstNode::mkconst_str(stripped_name.substr(1)));

	para_counter = 0;
	for (auto child : new_ast->children) {
		if (child->type != AST_PARAMETER)
			continue;
		para_counter++;
		auto it = parameters.find(child->str);
		if (it != parameters.end()) {
			if (!quiet)
				log("Parameter %s = %s\n", child->str.c_str(), log_signal(it->second));
			goto rewrite_parameter;
		}
		it = parameters.find(stringf("$%d", para_counter));
		if (it != parameters.end()) {
			if (!quiet)
				log("Parameter %d (%s) = %s\n", para_counter, child->str.c_str(), log_signal(it->second));
			goto rewrite_parameter;
		}
		continue;
	rewrite_parameter:
		if (param_has_no_default(child))
			child->children.insert(child->children.begin(), nullptr);
		delete child->children.at(0);
		if ((it->second.flags & RTLIL::CONST_FLAG_REAL) != 0) {
			child->children[0] = new AstNode(AST_REALVALUE);
			child->children[0]->realvalue = std::stod(it->second.decode_string());
		} else if ((it->second.flags & RTLIL::CONST_FLAG_STRING) != 0)
			child->children[0] = AstNode::mkconst_str(it->second.decode_string());
		else
			child->children[0] = AstNode::mkconst_bits(it->second.bits, (it->second.flags & RTLIL::CONST_FLAG_SIGNED) != 0);
		rewritten.insert(it->first);
	}

	if (GetSize(rewritten) < GetSize(parameters))
		for (const auto &param : parameters) {
			if (rewritten.count(param.first))
				continue;
			AstNode *defparam = new AstNode(AST_DEFPARAM, new AstNode(AST_IDENTIFIER));
			defparam->children[0]->str = param.first.str();
			if ((param.second.flags & RTLIL::CONST_FLAG_STRING) != 0)
				defparam->children.push_back(AstNode::mkconst_str(param.second.decode_string()));
			else
				defparam->children.push_back(AstNode::mkconst_bits(param.second.bits, (param.second.flags & RTLIL::CONST_FLAG_SIGNED) != 0));
			new_ast->children.push_back(defparam);
		}

	new_ast->fixup_hierarchy_flags(true);
	(*new_ast_out) = new_ast;
	return modname;
}

RTLIL::Module *AstModule::clone() const
{
	AstModule *new_mod = new AstModule;
	new_mod->name = name;
	cloneInto(new_mod);

	new_mod->ast = ast->clone();
	new_mod->nolatches = nolatches;
	new_mod->nomeminit = nomeminit;
	new_mod->nomem2reg = nomem2reg;
	new_mod->mem2reg = mem2reg;
	new_mod->noblackbox = noblackbox;
	new_mod->lib = lib;
	new_mod->nowb = nowb;
	new_mod->noopt = noopt;
	new_mod->icells = icells;
	new_mod->pwires = pwires;
	new_mod->autowire = autowire;

	return new_mod;
}

void AstModule::loadconfig() const
{
	current_ast = NULL;
	flag_dump_ast1 = false;
	flag_dump_ast2 = false;
	flag_dump_vlog1 = false;
	flag_dump_vlog2 = false;
	flag_nolatches = nolatches;
	flag_nomeminit = nomeminit;
	flag_nomem2reg = nomem2reg;
	flag_mem2reg = mem2reg;
	flag_noblackbox = noblackbox;
	flag_lib = lib;
	flag_nowb = nowb;
	flag_noopt = noopt;
	flag_icells = icells;
	flag_pwires = pwires;
	flag_autowire = autowire;
}

void AstNode::input_error(const char *format, ...) const
{
	va_list ap;
	va_start(ap, format);
	logv_file_error(filename, location.first_line, format, ap);
}

YOSYS_NAMESPACE_END
