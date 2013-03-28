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

// instanciate global variables (public API)
namespace AST {
	std::string current_filename;
	void (*set_line_num)(int) = NULL;
	int (*get_line_num)() = NULL;
}

// instanciate global variables (private API)
namespace AST_INTERNAL {
	bool flag_dump_ast, flag_dump_ast_diff, flag_dump_vlog, flag_nolatches, flag_nomem2reg, flag_mem2reg, flag_lib;
	AstNode *current_ast, *current_ast_mod;
	std::map<std::string, AstNode*> current_scope;
	RTLIL::SigSpec *genRTLIL_subst_from = NULL;
	RTLIL::SigSpec *genRTLIL_subst_to = NULL;
	AstNode *current_top_block, *current_block, *current_block_child;
	AstModule *current_module;
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
	X(AST_WIRE)
	X(AST_MEMORY)
	X(AST_AUTOWIRE)
	X(AST_PARAMETER)
	X(AST_LOCALPARAM)
	X(AST_PARASET)
	X(AST_ARGUMENT)
	X(AST_RANGE)
	X(AST_CONSTANT)
	X(AST_CELLTYPE)
	X(AST_IDENTIFIER)
	X(AST_PREFIX)
	X(AST_FCALL)
	X(AST_TO_SIGNED)
	X(AST_TO_UNSIGNED)
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
	X(AST_LT)
	X(AST_LE)
	X(AST_EQ)
	X(AST_NE)
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
	X(AST_TCALL)
	X(AST_ASSIGN)
	X(AST_CELL)
	X(AST_PRIMITIVE)
	X(AST_ALWAYS)
	X(AST_BLOCK)
	X(AST_ASSIGN_EQ)
	X(AST_ASSIGN_LE)
	X(AST_CASE)
	X(AST_COND)
	X(AST_DEFAULT)
	X(AST_FOR)
	X(AST_GENVAR)
	X(AST_GENFOR)
	X(AST_GENIF)
	X(AST_GENBLOCK)
	X(AST_POSEDGE)
	X(AST_NEGEDGE)
	X(AST_EDGE)
#undef X
	default:
		assert(!"Missing enum to string def in AST::type2str().");
		abort();
	}
}

// create new node (AstNode constructor)
// (the optional child arguments make it easier to create AST trees)
AstNode::AstNode(AstNodeType type, AstNode *child1, AstNode *child2)
{
	this->type = type;
	filename = current_filename;
	linenum = get_line_num();
	is_input = false;
	is_output = false;
	is_reg = false;
	is_signed = false;
	range_valid = false;
	port_id = 0;
	range_left = -1;
	range_right = 0;
	integer = 0;
	id2ast = NULL;

	if (child1)
		children.push_back(child1);
	if (child2)
		children.push_back(child2);
}

// create a (deep recursive) copy of a node
AstNode *AstNode::clone()
{
	AstNode *that = new AstNode;
	*that = *this;
	for (auto &it : that->children)
		it = it->clone();
	for (auto &it : that->attributes)
		it.second = it.second->clone();
	return that;
}

// create a (deep recursive) copy of a node use 'other' as target root node
void AstNode::cloneInto(AstNode *other)
{
	AstNode *tmp = clone();
	other->delete_children();
	*other = *tmp;
	tmp->children.clear();
	tmp->attributes.clear();
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
void AstNode::dumpAst(FILE *f, std::string indent, AstNode *other)
{
	if (f == NULL) {
		for (auto f : log_files)
			dumpAst(f, indent, other);
		return;
	}
	if (other != NULL) {
		if (type != other->type)
			goto found_diff_to_other;
		if (children.size() != other->children.size())
			goto found_diff_to_other;
		if (str != other->str)
			goto found_diff_to_other;
		if (bits != other->bits)
			goto found_diff_to_other;
		if (is_input != other->is_input)
			goto found_diff_to_other;
		if (is_output != other->is_output)
			goto found_diff_to_other;
		if (is_reg != other->is_reg)
			goto found_diff_to_other;
		if (is_signed != other->is_signed)
			goto found_diff_to_other;
		if (range_valid != other->range_valid)
			goto found_diff_to_other;
		if (port_id != other->port_id)
			goto found_diff_to_other;
		if (range_left != other->range_left)
			goto found_diff_to_other;
		if (range_right != other->range_right)
			goto found_diff_to_other;
		if (integer != other->integer)
			goto found_diff_to_other;
		if (0) {
	found_diff_to_other:
			other->dumpAst(f, indent + "- ");
			this->dumpAst(f, indent + "+ ");
			return;
		}
	}

	std::string type_name = type2str(type);
	fprintf(f, "%s%s <%s:%d>", indent.c_str(), type_name.c_str(), filename.c_str(), linenum);
	if (!str.empty())
		fprintf(f, " str='%s'", str.c_str());
	if (!bits.empty()) {
		fprintf(f, " bits='");
		for (size_t i = bits.size(); i > 0; i--)
			fprintf(f, "%c", bits[i-1] == RTLIL::S0 ? '0' :
					bits[i-1] == RTLIL::S1 ? '1' :
					bits[i-1] == RTLIL::Sx ? 'x' :
					bits[i-1] == RTLIL::Sz ? 'z' : '?');
		fprintf(f, "'(%zd)", bits.size());
	}
	if (is_input)
		fprintf(f, " input");
	if (is_output)
		fprintf(f, " output");
	if (is_reg)
		fprintf(f, " reg");
	if (is_signed)
		fprintf(f, " signed");
	if (port_id > 0)
		fprintf(f, " port=%d", port_id);
	if (range_valid || range_left != -1 || range_right != 0)
		fprintf(f, " range=[%d:%d]%s", range_left, range_right, range_valid ? "" : "!");
	if (integer != 0)
		fprintf(f, " int=%u", (int)integer);
	fprintf(f, "\n");

	for (size_t i = 0; i < children.size(); i++)
		children[i]->dumpAst(f, indent + "  ", other ? other->children[i] : NULL);
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

// dump AST node as verilog pseudo-code
void AstNode::dumpVlog(FILE *f, std::string indent)
{
	bool first = true;
	std::string txt;
	std::vector<AstNode*> rem_children1, rem_children2;

	if (f == NULL) {
		for (auto f : log_files)
			dumpVlog(f, indent);
		return;
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
			if (child->type == AST_PARAMETER || child->type == AST_LOCALPARAM)
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

	case AST_RANGE:
		if (range_valid)
			fprintf(f, "[%d:%d]", range_left, range_right);
		else {
			for (auto child : children) {
				fprintf(f, "%c", first ? '[' : ':');
				child->dumpVlog(f, "");
				first = false;
			}
			fprintf(f, "]");
		}
		break;

	case AST_ALWAYS:
		fprintf(f, "%s" "always @(", indent.c_str());
		for (auto child : children) {
			if (child->type != AST_POSEDGE && child->type != AST_NEGEDGE && child->type != AST_EDGE)
				continue;
			if (!first)
				fprintf(f, ", ");
			child->dumpVlog(f, "");
			first = false;
		}
		fprintf(f, ")\n");
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
		fprintf(f, "%s", id2vl(str).c_str());
		for (auto child : children)
			child->dumpVlog(f, "");
		break;

	case AST_CONSTANT:
		if (!str.empty())
			fprintf(f, "\"%s\"", str.c_str());
		else if (bits.size() == 32)
			fprintf(f, "%d", RTLIL::Const(bits).as_int());
		else
			fprintf(f, "%zd'b %s", bits.size(), RTLIL::Const(bits).as_string().c_str());
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
		for (auto child : children) {
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
		fprintf(f, "%s(", txt.c_str());
		children[0]->dumpVlog(f, "");
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
	if (0) { case AST_LT:           txt = "<";   }
	if (0) { case AST_LE:           txt = "<=";  }
	if (0) { case AST_EQ:           txt = "==";  }
	if (0) { case AST_NE:           txt = "!=";  }
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
	if (is_reg != other.is_reg)
		return false;
	if (is_signed != other.is_signed)
		return false;
	if (range_valid != other.range_valid)
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
		node->bits.push_back((v & 1) ? RTLIL::S1 : RTLIL::S0);
		v = v >> 1;
	}
	node->range_valid = true;
	node->range_left = width-1;
	node->range_right = 0;
	return node;
}

// create an AST node for a constant (using a bit vector as value)
AstNode *AstNode::mkconst_bits(const std::vector<RTLIL::State> &v, bool is_signed)
{
	AstNode *node = new AstNode(AST_CONSTANT);
	node->is_signed = is_signed;
	node->bits = v;
	for (size_t i = 0; i < 32; i++) {
		if (i < node->bits.size())
			node->integer |= (node->bits[i] == RTLIL::S1) << i;
		else if (is_signed)
			node->integer |= (node->bits.back() == RTLIL::S1) << i;
	}
	node->range_valid = true;
	node->range_left = node->bits.size();
	node->range_right = 0;
	return node;
}

// create a new AstModule from an AST_MODULE AST node
static AstModule* process_module(AstNode *ast)
{
	assert(ast->type == AST_MODULE);
	log("Generating RTLIL representation for module `%s'.\n", ast->str.c_str());

	current_ast_mod = ast;
	AstNode *ast_before_simplify = ast->clone();

	while (ast->simplify(false, false, false, 0)) { }

	if (flag_dump_ast) {
		log("Dumping verilog AST (as requested by %s option):\n", flag_dump_ast_diff ? "dump_ast_diff" : "dump_ast");
		ast->dumpAst(NULL, "    ", flag_dump_ast_diff ? ast_before_simplify : NULL);
		log("--- END OF AST DUMP ---\n");
	}

	if (flag_dump_vlog) {
		log("Dumping verilog AST (as requested by dump_vlog option):\n");
		ast->dumpVlog(NULL, "    ");
		log("--- END OF AST DUMP ---\n");
	}

	if (flag_lib) {
		std::vector<AstNode*> new_children;
		for (auto child : ast->children) {
			if (child->type == AST_WIRE && (child->is_input || child->is_output))
				new_children.push_back(child);
			else
				delete child;
		}
		ast->children.swap(new_children);
		ast->attributes["\\placeholder"] = AstNode::mkconst_int(0, false, 0);
	}

	current_module = new AstModule;
	current_module->ast = NULL;
	current_module->name = ast->str;
	current_module->attributes["\\src"] = stringf("%s:%d", ast->filename.c_str(), ast->linenum);
	for (auto &attr : ast->attributes) {
		if (attr.second->type != AST_CONSTANT)
			log_error("Attribute `%s' with non-constant value at %s:%d!\n",
					attr.first.c_str(), ast->filename.c_str(), ast->linenum);
		current_module->attributes[attr.first].str = attr.second->str;
		current_module->attributes[attr.first].bits = attr.second->bits;
	}
	for (size_t i = 0; i < ast->children.size(); i++) {
		AstNode *node = ast->children[i];
		if (node->type == AST_WIRE || node->type == AST_MEMORY)
			node->genRTLIL();
	}
	for (size_t i = 0; i < ast->children.size(); i++) {
		AstNode *node = ast->children[i];
		if (node->type != AST_WIRE && node->type != AST_MEMORY)
			node->genRTLIL();
	}

	current_module->ast = ast_before_simplify;
	current_module->nolatches = flag_nolatches;
	current_module->nomem2reg = flag_nomem2reg;
	current_module->mem2reg = flag_mem2reg;
	current_module->lib = flag_lib;
	return current_module;
}

// create AstModule instances for all modules in the AST tree and add them to 'design'
void AST::process(RTLIL::Design *design, AstNode *ast, bool dump_ast, bool dump_ast_diff, bool dump_vlog, bool nolatches, bool nomem2reg, bool mem2reg, bool lib)
{
	current_ast = ast;
	flag_dump_ast = dump_ast;
	flag_dump_ast_diff = dump_ast_diff;
	flag_dump_vlog = dump_vlog;
	flag_nolatches = nolatches;
	flag_nomem2reg = nomem2reg;
	flag_mem2reg = mem2reg;
	flag_lib = lib;

	assert(current_ast->type == AST_DESIGN);
	for (auto it = current_ast->children.begin(); it != current_ast->children.end(); it++) {
		if (design->modules.count((*it)->str) != 0)
			log_error("Re-definition of module `%s' at %s:%d!\n",
					(*it)->str.c_str(), (*it)->filename.c_str(), (*it)->linenum);
		design->modules[(*it)->str] = process_module(*it);
	}
}

// AstModule destructor
AstModule::~AstModule()
{
	if (ast != NULL)
		delete ast;
}

// create a new parametric module (when needed) and return the name of the generated module
RTLIL::IdString AstModule::derive(RTLIL::Design *design, std::map<RTLIL::IdString, RTLIL::Const> parameters)
{
	log_header("Executing AST frontend in derive mode using pre-parsed AST for module `%s'.\n", name.c_str());

	current_ast = NULL;
	flag_dump_ast = false;
	flag_dump_ast_diff = false;
	flag_dump_vlog = false;
	flag_nolatches = nolatches;
	flag_nomem2reg = nomem2reg;
	flag_mem2reg = mem2reg;
	flag_lib = lib;
	use_internal_line_num();

	std::vector<unsigned char> hash_data;
	hash_data.insert(hash_data.end(), name.begin(), name.end());
	hash_data.push_back(0);

	AstNode *new_ast = ast->clone();

	int para_counter = 0;
	for (auto it = new_ast->children.begin(); it != new_ast->children.end(); it++) {
		AstNode *child = *it;
		if (child->type != AST_PARAMETER)
			continue;
		para_counter++;
		std::string para_id = child->str;
		if (parameters.count(child->str) > 0) {
			log("Parameter %s = %s\n", child->str.c_str(), log_signal(RTLIL::SigSpec(parameters[child->str])));
	rewrite_parameter:
			child->delete_children();
			child->children.push_back(AstNode::mkconst_bits(parameters[para_id].bits, false));
			hash_data.insert(hash_data.end(), child->str.begin(), child->str.end());
			hash_data.push_back(0);
			hash_data.insert(hash_data.end(), parameters[para_id].bits.begin(), parameters[para_id].bits.end());
			hash_data.push_back(0xff);
			parameters.erase(para_id);
			continue;
		}
		char buf[100];
		snprintf(buf, 100, "$%d", para_counter);
		if (parameters.count(buf) > 0) {
			para_id = buf;
			log("Parameter %d (%s) = %s\n", para_counter, child->str.c_str(), log_signal(RTLIL::SigSpec(parameters[para_id])));
			goto rewrite_parameter;
		}
	}
	if (parameters.size() > 0)
		log_error("Requested parameter `%s' does not exist in module `%s'!\n", parameters.begin()->first.c_str(), name.c_str());

	unsigned char hash[20];
	unsigned char *hash_data2 = new unsigned char[hash_data.size()];
	for (size_t i = 0; i < hash_data.size(); i++)
		hash_data2[i] = hash_data[i];
	sha1::calc(hash_data2, hash_data.size(), hash);
	delete[] hash_data2;

	char hexstring[41];
	sha1::toHexString(hash, hexstring);

	std::string modname = "$paramod$" + std::string(hexstring) + "$" + name;

	if (design->modules.count(modname) == 0) {
		new_ast->str = modname;
		design->modules[modname] = process_module(new_ast);
	} else {
		log("Found cached RTLIL representation for module `%s'.\n", modname.c_str());
	}

	delete new_ast;
	return modname;
}

// recompile a module from AST with updated widths for auto-wires
// (auto-wires are wires that are used but not declared an thus have an automatically determined width)
void AstModule::update_auto_wires(std::map<RTLIL::IdString, int> auto_sizes)
{
	log_header("Executing AST frontend in update_auto_wires mode using pre-parsed AST for module `%s'.\n", name.c_str());

	current_ast = NULL;
	flag_dump_ast = false;
	flag_dump_ast_diff = false;
	flag_dump_vlog = false;
	flag_nolatches = nolatches;
	flag_nomem2reg = nomem2reg;
	flag_mem2reg = mem2reg;
	flag_lib = lib;
	use_internal_line_num();

	for (auto it = auto_sizes.begin(); it != auto_sizes.end(); it++) {
		log("Adding extra wire declaration to AST: wire [%d:0] %s\n", it->second - 1, it->first.c_str());
		AstNode *wire = new AstNode(AST_WIRE, new AstNode(AST_RANGE, AstNode::mkconst_int(it->second - 1, true), AstNode::mkconst_int(0, true)));
		wire->str = it->first;
		ast->children.insert(ast->children.begin(), wire);
	}

	AstModule *newmod =  process_module(ast);

	delete ast;
	ast = newmod->ast;
	newmod->ast = NULL;

	wires.swap(newmod->wires);
	cells.swap(newmod->cells);
	processes.swap(newmod->processes);
	connections.swap(newmod->connections);
	attributes.swap(newmod->attributes);
	delete newmod;
}

// internal dummy line number callbacks
namespace {
	int internal_line_num;
	void internal_set_line_num(int n) {
		internal_line_num = n;
	}
	int internal_get_line_num() {
		return internal_line_num;
	}
}

// use internal dummy line number callbacks
void AST::use_internal_line_num()
{
	set_line_num = &internal_set_line_num;
	get_line_num = &internal_get_line_num;
}

