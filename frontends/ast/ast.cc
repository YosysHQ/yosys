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

#include "kernel/yosys.h"
#include "libs/sha1/sha1.h"
#include "ast.h"

YOSYS_NAMESPACE_BEGIN

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
	bool flag_dump_ast1, flag_dump_ast2, flag_dump_vlog, flag_dump_rtlil, flag_nolatches, flag_nomeminit;
	bool flag_nomem2reg, flag_mem2reg, flag_lib, flag_noopt, flag_icells, flag_autowire;
	AstNode *current_ast, *current_ast_mod;
	std::map<std::string, AstNode*> current_scope;
	const dict<RTLIL::SigBit, RTLIL::SigBit> *genRTLIL_subst_ptr = NULL;
	RTLIL::SigSpec ignoreThisSignalsInInitial;
	AstNode *current_always, *current_top_block, *current_block, *current_block_child;
	AstModule *current_module;
	bool current_always_clocked;
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
	X(AST_FCALL)
	X(AST_TO_BITS)
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
	X(AST_POSEDGE)
	X(AST_NEGEDGE)
	X(AST_EDGE)
	X(AST_PACKAGE)
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
		log_error("Attribute `%s' with non-constant value at %s:%d!\n",
				id.c_str(), attr->filename.c_str(), attr->linenum);

	return attr->integer != 0;
}

// create new node (AstNode constructor)
// (the optional child arguments make it easier to create AST trees)
AstNode::AstNode(AstNodeType type, AstNode *child1, AstNode *child2, AstNode *child3)
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	this->type = type;
	filename = current_filename;
	linenum = get_line_num();
	is_input = false;
	is_output = false;
	is_reg = false;
	is_signed = false;
	is_string = false;
	range_valid = false;
	range_swapped = false;
	port_id = 0;
	range_left = -1;
	range_right = 0;
	integer = 0;
	realvalue = 0;
	id2ast = NULL;
	basic_prep = false;

	if (child1)
		children.push_back(child1);
	if (child2)
		children.push_back(child2);
	if (child3)
		children.push_back(child3);
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
void AstNode::dumpAst(FILE *f, std::string indent)
{
	if (f == NULL) {
		for (auto f : log_files)
			dumpAst(f, indent);
		return;
	}

	std::string type_name = type2str(type);
	fprintf(f, "%s%s <%s:%d>", indent.c_str(), type_name.c_str(), filename.c_str(), linenum);

	if (id2ast)
		fprintf(f, " [%p -> %p]", this, id2ast);
	else
		fprintf(f, " [%p]", this);

	if (!str.empty())
		fprintf(f, " str='%s'", str.c_str());
	if (!bits.empty()) {
		fprintf(f, " bits='");
		for (size_t i = bits.size(); i > 0; i--)
			fprintf(f, "%c", bits[i-1] == RTLIL::S0 ? '0' :
					bits[i-1] == RTLIL::S1 ? '1' :
					bits[i-1] == RTLIL::Sx ? 'x' :
					bits[i-1] == RTLIL::Sz ? 'z' : '?');
		fprintf(f, "'(%d)", GetSize(bits));
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
		fprintf(f, " %srange=[%d:%d]%s", range_swapped ? "swapped_" : "", range_left, range_right, range_valid ? "" : "!");
	if (integer != 0)
		fprintf(f, " int=%u", (int)integer);
	if (realvalue != 0)
		fprintf(f, " real=%e", realvalue);
	if (!multirange_dimensions.empty()) {
		fprintf(f, " multirange=[");
		for (int v : multirange_dimensions)
			fprintf(f, " %d", v);
		fprintf(f, " ]");
	}
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
		if (!children.empty() && children[0]->type == AST_CONDX)
			fprintf(f, "%s" "casex (", indent.c_str());
		else if (!children.empty() && children[0]->type == AST_CONDZ)
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
		else if (is_signed && !node->bits.empty())
			node->integer |= (node->bits.back() == RTLIL::S1) << i;
	}
	node->range_valid = true;
	node->range_left = node->bits.size()-1;
	node->range_right = 0;
	return node;
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
			data.push_back((ch & 1) ? RTLIL::S1 : RTLIL::S0);
			ch = ch >> 1;
		}
	}
	AstNode *node = AstNode::mkconst_bits(data, false);
	node->is_string = true;
	node->str = str;
	return node;
}

bool AstNode::bits_only_01()
{
	for (auto bit : bits)
		if (bit != RTLIL::S0 && bit != RTLIL::S1)
			return false;
	return true;
}

RTLIL::Const AstNode::bitsAsConst(int width, bool is_signed)
{
	std::vector<RTLIL::State> bits = this->bits;
	if (width >= 0 && width < int(bits.size()))
		bits.resize(width);
	if (width >= 0 && width > int(bits.size())) {
		RTLIL::State extbit = RTLIL::State::S0;
		if (is_signed && !bits.empty())
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

RTLIL::Const AstNode::asAttrConst()
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

RTLIL::Const AstNode::asParaConst()
{
	RTLIL::Const val = asAttrConst();
	if (is_signed)
		val.flags |= RTLIL::CONST_FLAG_SIGNED;
	return val;
}

bool AstNode::asBool()
{
	log_assert(type == AST_CONSTANT);
	for (auto &bit : bits)
		if (bit == RTLIL::State::S1)
			return true;
	return false;
}

int AstNode::isConst()
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

// create a new AstModule from an AST_MODULE AST node
static AstModule* process_module(AstNode *ast, bool defer)
{
	log_assert(ast->type == AST_MODULE);

	if (defer)
		log("Storing AST representation for module `%s'.\n", ast->str.c_str());
	else
		log("Generating RTLIL representation for module `%s'.\n", ast->str.c_str());

	current_module = new AstModule;
	current_module->ast = NULL;
	current_module->name = ast->str;
	current_module->attributes["\\src"] = stringf("%s:%d", ast->filename.c_str(), ast->linenum);

	current_ast_mod = ast;
	AstNode *ast_before_simplify = ast->clone();

	if (flag_dump_ast1) {
		log("Dumping Verilog AST before simplification:\n");
		ast->dumpAst(NULL, "    ");
		log("--- END OF AST DUMP ---\n");
	}

	if (!defer)
	{
		while (ast->simplify(!flag_noopt, false, false, 0, -1, false, false)) { }

		if (flag_dump_ast2) {
			log("Dumping Verilog AST after simplification:\n");
			ast->dumpAst(NULL, "    ");
			log("--- END OF AST DUMP ---\n");
		}

		if (flag_dump_vlog) {
			log("Dumping Verilog AST (as requested by dump_vlog option):\n");
			ast->dumpVlog(NULL, "    ");
			log("--- END OF AST DUMP ---\n");
		}

		if (flag_lib) {
			std::vector<AstNode*> new_children;
			for (auto child : ast->children) {
				if (child->type == AST_WIRE && (child->is_input || child->is_output)) {
					new_children.push_back(child);
				} else if (child->type == AST_PARAMETER) {
					child->delete_children();
					child->children.push_back(AstNode::mkconst_int(0, false, 0));
					new_children.push_back(child);
				} else {
					delete child;
				}
			}
			ast->children.swap(new_children);
			ast->attributes["\\blackbox"] = AstNode::mkconst_int(1, false);
		}

		ignoreThisSignalsInInitial = RTLIL::SigSpec();

		for (auto &attr : ast->attributes) {
			if (attr.second->type != AST_CONSTANT)
				log_error("Attribute `%s' with non-constant value at %s:%d!\n",
						attr.first.c_str(), ast->filename.c_str(), ast->linenum);
			current_module->attributes[attr.first] = attr.second->asAttrConst();
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
	}

	current_module->ast = ast_before_simplify;
	current_module->nolatches = flag_nolatches;
	current_module->nomeminit = flag_nomeminit;
	current_module->nomem2reg = flag_nomem2reg;
	current_module->mem2reg = flag_mem2reg;
	current_module->lib = flag_lib;
	current_module->noopt = flag_noopt;
	current_module->icells = flag_icells;
	current_module->autowire = flag_autowire;
	current_module->fixup_ports();

	if (flag_dump_rtlil) {
		log("Dumping generated RTLIL:\n");
		log_module(current_module);
		log("--- END OF RTLIL DUMP ---\n");
	}

	return current_module;
}

// create AstModule instances for all modules in the AST tree and add them to 'design'
void AST::process(RTLIL::Design *design, AstNode *ast, bool dump_ast1, bool dump_ast2, bool dump_vlog, bool dump_rtlil,
		bool nolatches, bool nomeminit, bool nomem2reg, bool mem2reg, bool lib, bool noopt, bool icells, bool ignore_redef, bool defer, bool autowire)
{
	current_ast = ast;
	flag_dump_ast1 = dump_ast1;
	flag_dump_ast2 = dump_ast2;
	flag_dump_vlog = dump_vlog;
	flag_dump_rtlil = dump_rtlil;
	flag_nolatches = nolatches;
	flag_nomeminit = nomeminit;
	flag_nomem2reg = nomem2reg;
	flag_mem2reg = mem2reg;
	flag_lib = lib;
	flag_noopt = noopt;
	flag_icells = icells;
	flag_autowire = autowire;

	std::vector<AstNode*> global_decls;

	log_assert(current_ast->type == AST_DESIGN);
	for (auto it = current_ast->children.begin(); it != current_ast->children.end(); it++)
	{
		if ((*it)->type == AST_MODULE)
		{
			for (auto n : global_decls)
				(*it)->children.push_back(n->clone());

			for (auto n : design->verilog_packages){
				for (auto o : n->children) {
					AstNode *cloned_node = o->clone();
					cloned_node->str = n->str + std::string("::") + cloned_node->str.substr(1);
					(*it)->children.push_back(cloned_node);
				}
			}

			if (flag_icells && (*it)->str.substr(0, 2) == "\\$")
				(*it)->str = (*it)->str.substr(1);

			if (defer)
				(*it)->str = "$abstract" + (*it)->str;

			if (design->has((*it)->str)) {
				if (!ignore_redef)
					log_error("Re-definition of module `%s' at %s:%d!\n",
							(*it)->str.c_str(), (*it)->filename.c_str(), (*it)->linenum);
				log("Ignoring re-definition of module `%s' at %s:%d!\n",
						(*it)->str.c_str(), (*it)->filename.c_str(), (*it)->linenum);
				continue;
			}

			design->add(process_module(*it, defer));
		}
		else if ((*it)->type == AST_PACKAGE)
			design->verilog_packages.push_back((*it)->clone());
		else
			global_decls.push_back(*it);
	}
}

// AstModule destructor
AstModule::~AstModule()
{
	if (ast != NULL)
		delete ast;
}

// create a new parametric module (when needed) and return the name of the generated module
RTLIL::IdString AstModule::derive(RTLIL::Design *design, dict<RTLIL::IdString, RTLIL::Const> parameters)
{
	std::string stripped_name = name.str();

	if (stripped_name.substr(0, 9) == "$abstract")
		stripped_name = stripped_name.substr(9);

	log_header(design, "Executing AST frontend in derive mode using pre-parsed AST for module `%s'.\n", stripped_name.c_str());

	current_ast = NULL;
	flag_dump_ast1 = false;
	flag_dump_ast2 = false;
	flag_dump_vlog = false;
	flag_nolatches = nolatches;
	flag_nomeminit = nomeminit;
	flag_nomem2reg = nomem2reg;
	flag_mem2reg = mem2reg;
	flag_lib = lib;
	flag_noopt = noopt;
	flag_icells = icells;
	flag_autowire = autowire;
	use_internal_line_num();

	std::string para_info;
	AstNode *new_ast = ast->clone();

	int para_counter = 0;
	int orig_parameters_n = parameters.size();
	for (auto it = new_ast->children.begin(); it != new_ast->children.end(); it++) {
		AstNode *child = *it;
		if (child->type != AST_PARAMETER)
			continue;
		para_counter++;
		std::string para_id = child->str;
		if (parameters.count(para_id) > 0) {
			log("Parameter %s = %s\n", child->str.c_str(), log_signal(RTLIL::SigSpec(parameters[child->str])));
	rewrite_parameter:
			para_info += stringf("%s=%s", child->str.c_str(), log_signal(RTLIL::SigSpec(parameters[para_id])));
			delete child->children.at(0);
			child->children[0] = AstNode::mkconst_bits(parameters[para_id].bits, (parameters[para_id].flags & RTLIL::CONST_FLAG_SIGNED) != 0);
			parameters.erase(para_id);
			continue;
		}
		para_id = stringf("$%d", para_counter);
		if (parameters.count(para_id) > 0) {
			log("Parameter %d (%s) = %s\n", para_counter, child->str.c_str(), log_signal(RTLIL::SigSpec(parameters[para_id])));
			goto rewrite_parameter;
		}
	}
	if (parameters.size() > 0)
		log_error("Requested parameter `%s' does not exist in module `%s'!\n", parameters.begin()->first.c_str(), stripped_name.c_str());

	std::string modname;

	if (orig_parameters_n == 0)
		modname = stripped_name;
	else if (para_info.size() > 60)
		modname = "$paramod$" + sha1(para_info) + stripped_name;
	else
		modname = "$paramod" + stripped_name + para_info;

	if (!design->has(modname)) {
		new_ast->str = modname;
		design->add(process_module(new_ast, false));
		design->module(modname)->check();
	} else {
		log("Found cached RTLIL representation for module `%s'.\n", modname.c_str());
	}

	delete new_ast;
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
	new_mod->lib = lib;
	new_mod->noopt = noopt;
	new_mod->icells = icells;
	new_mod->autowire = autowire;

	return new_mod;
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

YOSYS_NAMESPACE_END

