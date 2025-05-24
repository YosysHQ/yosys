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
 *  The Verilog frontend.
 *
 *  This frontend is using the AST frontend library (see frontends/ast/).
 *  Thus this frontend does not generate RTLIL code directly but creates an
 *  AST directly from the Verilog parse tree and then passes this AST to
 *  the AST frontend library.
 *
 *  ---
 *
 *  This is the actual bison parser for Verilog code. The AST ist created directly
 *  from the bison reduce functions here. Note that this code uses a few global
 *  variables to hold the state of the AST generator and therefore this parser is
 *  not reentrant.
 *
 */

%require "3.0"
%language "c++"
%define api.value.type variant
%define api.prefix {frontend_verilog_yy}
%define api.token.constructor

%param { YOSYS_NAMESPACE_PREFIX VERILOG_FRONTEND::VerilogLexer* lexer }

%code {
    // Tell Bison to use lexer.nextToken() for getting tokens
	#undef yylex
    #define yylex(dummy) lexer->nextToken()
}

%{
#include <list>
#include <stack>
#include <memory>
#include <string.h>
#include "frontends/verilog/verilog_frontend.h"
#include "kernel/log.h"

typedef frontend_verilog_yy::parser::semantic_type YYSTYPE;
typedef frontend_verilog_yy::location YYLTYPE;
USING_YOSYS_NAMESPACE;
using namespace AST;
using namespace VERILOG_FRONTEND;

YOSYS_NAMESPACE_BEGIN
namespace VERILOG_FRONTEND {
	int port_counter;
	dict<std::string, int> port_stubs;
	dict<IdString, std::unique_ptr<AstNode>> *attr_list, default_attr_list;
	std::stack<dict<IdString, std::unique_ptr<AstNode>> *> attr_list_stack;
	dict<IdString, std::unique_ptr<AstNode>> *albuf;
	std::vector<UserTypeMap> user_type_stack;
	dict<std::string, AstNode*> pkg_user_types;
	std::vector<AstNode*> ast_stack;
	std::unique_ptr<AstNode> astbuf1, astbuf2, astbuf3;
	AstNode* cell_hack;
	AstNode* member_hack;
	struct AstNode *current_function_or_task;
	struct AstNode *current_ast, *current_ast_mod;
	int current_function_or_task_port_id;
	std::vector<char> case_type_stack;
	bool do_not_require_port_stubs;
	bool default_nettype_wire;
	bool sv_mode, formal_mode, lib_mode, specify_mode;
	bool noassert_mode, noassume_mode, norestrict_mode;
	bool assume_asserts_mode, assert_assumes_mode;
	bool current_wire_rand, current_wire_const;
	bool current_modport_input, current_modport_output;
	std::istream *lexin;
};
YOSYS_NAMESPACE_END

#define SET_AST_NODE_LOC(WHICH, BEGIN, END) \
    do { (WHICH)->location.first_line = (BEGIN).begin.line; \
    (WHICH)->location.first_column = (BEGIN).begin.column; \
    (WHICH)->location.last_line = (END).end.line; \
    (WHICH)->location.last_column = (END).end.column; } while(0)

#define SET_RULE_LOC(LHS, BEGIN, END) \
    do { (LHS).begin = BEGIN.begin; \
    (LHS).end = (END).end; } while(0)

void frontend_verilog_yy::parser::error(const frontend_verilog_yy::parser::location_type& loc, const std::string& msg)
{
	(void) loc;
    frontend_verilog_yyerror("%s", msg.c_str());
}

static void append_attr(AstNode *ast, dict<IdString, std::unique_ptr<AstNode>> *al)
{
	for (auto &it : *al) {
		ast->attributes[it.first] = std::move(it.second);
	}
	delete al;
}

static void append_attr_clone(AstNode *ast, dict<IdString, std::unique_ptr<AstNode>> *al)
{
	for (auto &it : *al) {
		ast->attributes[it.first] = it.second->clone();
	}
}

static void free_attr(dict<IdString, std::unique_ptr<AstNode>> *al)
{
	delete al;
}

static AstNode* saveChild(std::unique_ptr<AstNode> child) {
	auto* child_leaky = child.get();
	ast_stack.back()->children.push_back(std::move(child));
	return child_leaky;
}
static AstNode* pushChild(std::unique_ptr<AstNode> child) {
	auto* child_leaky = saveChild(std::move(child));
	ast_stack.push_back(child_leaky);
	return child_leaky;
}

static void addWiretypeNode(std::string *name, AstNode* node)
{
	log_assert(node);
	node->is_custom_type = true;
	node->children.push_back(std::make_unique<AstNode>(AST_WIRETYPE));
	node->children.back()->str = *name;
	delete name;
}

static void addTypedefNode(std::string *name, std::unique_ptr<AstNode> node)
{
	log_assert((bool)node);
	AstNode* tnode = saveChild(std::make_unique<AstNode>(AST_TYPEDEF, std::move(node)));
	log_assert((bool)name);
	tnode->str = *name;
	auto &user_types = user_type_stack.back();
	user_types[*name] = tnode;
	if (current_ast_mod && current_ast_mod->type == AST_PACKAGE) {
		// typedef inside a package so we need the qualified name
		auto qname = current_ast_mod->str + "::" + (*name).substr(1);
		pkg_user_types[qname] = tnode;
	}
	delete name;
}

static void enterTypeScope()
{
	user_type_stack.push_back(UserTypeMap());
}

static void exitTypeScope()
{
	user_type_stack.pop_back();
}

static bool isInLocalScope(const std::string *name)
{
	// tests if a name was declared in the current block scope
	auto &user_types = user_type_stack.back();
	return (user_types.count(*name) > 0);
}

static std::unique_ptr<AstNode> makeRange(int msb = 31, int lsb = 0, bool isSigned = true)
{
	auto range = std::make_unique<AstNode>(AST_RANGE);
	range->children.push_back(AstNode::mkconst_int(msb, true));
	range->children.push_back(AstNode::mkconst_int(lsb, true));
	range->is_signed = isSigned;
	return range;
}

static void addRange(AstNode *parent, int msb = 31, int lsb = 0, bool isSigned = true)
{
	auto range = makeRange(msb, lsb, isSigned);
	parent->children.push_back(std::move(range));
}

static std::unique_ptr<AstNode> checkRange(AstNode *type_node, std::unique_ptr<AstNode> range_node)
{
	if (type_node->range_left >= 0 && type_node->range_right >= 0) {
		// type already restricts the range
		if (range_node) {
			frontend_verilog_yyerror("integer/genvar types cannot have packed dimensions.");
		}
		else {
			range_node = makeRange(type_node->range_left, type_node->range_right, false);
		}
	}

	if (range_node) {
		bool valid = true;
		if (range_node->type == AST_RANGE) {
			valid = range_node->children.size() == 2;
		} else {  // AST_MULTIRANGE
			for (auto& child : range_node->children) {
				valid = valid && child->children.size() == 2;
			}
		}
		if (!valid)
			frontend_verilog_yyerror("wire/reg/logic packed dimension must be of the form [<expr>:<expr>]");
	}

	return range_node;
}

static void rewriteRange(AstNode *rangeNode)
{
	if (rangeNode->type == AST_RANGE && rangeNode->children.size() == 1) {
		// SV array size [n], rewrite as [0:n-1]
		rangeNode->children.push_back(std::make_unique<AstNode>(AST_SUB, std::move(rangeNode->children[0]), AstNode::mkconst_int(1, true)));
		rangeNode->children[0] = AstNode::mkconst_int(0, false);
	}
}

static void rewriteAsMemoryNode(AstNode *node, std::unique_ptr<AstNode> rangeNode)
{
	node->type = AST_MEMORY;
	if (rangeNode->type == AST_MULTIRANGE) {
		for (auto& child : rangeNode->children)
			rewriteRange(child.get());
	} else
		rewriteRange(rangeNode.get());
	node->children.push_back(std::move(rangeNode));
}

static void checkLabelsMatch(const char *element, const std::string *before, const std::string *after)
{
	if (!before && after)
		frontend_verilog_yyerror("%s missing where end label (%s) was given.",
			element, after->c_str() + 1);
	if (before && after && *before != *after)
		frontend_verilog_yyerror("%s (%s) and end label (%s) don't match.",
			element, before->c_str() + 1, after->c_str() + 1);
}

// This transforms a loop like
//   for (genvar i = 0; i < 10; i++) begin : blk
// to
//   genvar _i;
//   for (_i = 0; _i < 10; _i++) begin : blk
//     localparam i = _i;
// where `_i` is actually some auto-generated name.
static void rewriteGenForDeclInit(AstNode *loop)
{
	// check if this generate for loop contains an inline declaration
	log_assert(loop->type == AST_GENFOR);
	auto& decl = loop->children[0];
	if (decl->type == AST_ASSIGN_EQ)
		return;

	log_assert(decl->type == AST_GENVAR);
	log_assert(loop->children.size() == 5);

	// identify each component of the loop
	AstNode *init = loop->children[1].get();
	AstNode *cond = loop->children[2].get();
	AstNode *incr = loop->children[3].get();
	AstNode *body = loop->children[4].get();
	log_assert(init->type == AST_ASSIGN_EQ);
	log_assert(incr->type == AST_ASSIGN_EQ);
	log_assert(body->type == AST_GENBLOCK);

	// create a unique name for the genvar
	std::string old_str = decl->str;
	std::string new_str = stringf("$genfordecl$%d$%s", autoidx++, old_str.c_str());

	// rename and move the genvar declaration to the containing description
	decl->str = new_str;
	log_assert(current_ast_mod != nullptr);
	current_ast_mod->children.push_back(std::move(decl));

	// create a new localparam with old name so that the items in the loop
	// can simply use the old name and shadow it as necessary
	auto indirect = std::make_unique<AstNode>(AST_LOCALPARAM);
	indirect->str = old_str;
	auto ident = std::make_unique<AstNode>(AST_IDENTIFIER);
	ident->str = new_str;
	indirect->children.push_back(std::move(ident));

	body->children.insert(body->children.begin(), std::move(indirect));

	// only perform the renaming for the initialization, guard, and
	// incrementation to enable proper shadowing of the synthetic localparam
	std::function<void(AstNode*)> substitute = [&](AstNode *node) {
		if (node->type == AST_IDENTIFIER && node->str == old_str)
			node->str = new_str;
		for (auto& child : node->children)
			substitute(child.get());
	};
	substitute(init);
	substitute(cond);
	substitute(incr);
	loop->children.erase(loop->children.begin());
}

static void ensureAsgnExprAllowed()
{
	if (!sv_mode)
		frontend_verilog_yyerror("Assignments within expressions are only supported in SystemVerilog mode.");
	if (ast_stack.back()->type != AST_BLOCK)
		frontend_verilog_yyerror("Assignments within expressions are only permitted within procedures.");
}

// add a pre/post-increment/decrement statement
static const AstNode *addIncOrDecStmt(dict<IdString, std::unique_ptr<AstNode>> *stmt_attr,
					  std::unique_ptr<AstNode> lhs,
				      dict<IdString, std::unique_ptr<AstNode>> *op_attr, AST::AstNodeType op,
				      YYLTYPE begin, YYLTYPE end)
{
	auto one = AstNode::mkconst_int(1, true);
	auto rhs = std::make_unique<AstNode>(op, lhs->clone(), std::move(one));
	if (op_attr != nullptr)
		append_attr(rhs.get(), op_attr);
	auto stmt_owned = std::make_unique<AstNode>(AST_ASSIGN_EQ, std::move(lhs), std::move(rhs));
	auto* stmt = stmt_owned.get();
	ast_stack.back()->children.push_back(std::move(stmt_owned));
	SET_AST_NODE_LOC(stmt, begin, end);
	if (stmt_attr != nullptr)
		append_attr(stmt, stmt_attr);
	return stmt;
}

// create a pre/post-increment/decrement expression, and add the corresponding statement
static std::unique_ptr<AstNode> addIncOrDecExpr(std::unique_ptr<AstNode> lhs, dict<IdString, std::unique_ptr<AstNode>> *attr, AST::AstNodeType op, YYLTYPE begin, YYLTYPE end, bool undo)
{
	ensureAsgnExprAllowed();
	const AstNode *stmt = addIncOrDecStmt(nullptr, std::move(lhs), attr, op, begin, end);
	log_assert(stmt->type == AST_ASSIGN_EQ);
	auto expr = stmt->children[0]->clone();
	if (undo) {
		auto minus_one = AstNode::mkconst_int(-1, true, 1);
		expr = std::make_unique<AstNode>(op, std::move(expr), std::move(minus_one));
	}
	SET_AST_NODE_LOC(expr.get(), begin, end);
	return expr;
}

// add a binary operator assignment statement, e.g., a += b
static std::unique_ptr<AstNode> addAsgnBinopStmt(dict<IdString, std::unique_ptr<AstNode>> *attr, std::unique_ptr<AstNode> eq_lhs, AST::AstNodeType op, std::unique_ptr<AstNode> rhs, YYLTYPE begin, YYLTYPE end)
{
	SET_AST_NODE_LOC(rhs.get(), end, end);
	if (op == AST_SHIFT_LEFT || op == AST_SHIFT_RIGHT ||
		op == AST_SHIFT_SLEFT || op == AST_SHIFT_SRIGHT) {
		rhs = std::make_unique<AstNode>(AST_TO_UNSIGNED, std::move(rhs));
		SET_AST_NODE_LOC(rhs.get(), end, end);
	}
	auto binop_lhs = eq_lhs->clone();
	auto eq_rhs_owned = std::make_unique<AstNode>(op, std::move(binop_lhs), std::move(rhs));
	auto* eq_rhs = eq_rhs_owned.get();
	auto ret_lhs = eq_lhs->clone();
	auto stmt_owned = std::make_unique<AstNode>(AST_ASSIGN_EQ, std::move(eq_lhs), std::move(eq_rhs_owned));
	auto* stmt = stmt_owned.get();
	SET_AST_NODE_LOC(eq_rhs, begin, end);
	SET_AST_NODE_LOC(stmt, begin, end);
	ast_stack.back()->children.push_back(std::move(stmt_owned));
	if (attr != nullptr)
		append_attr(stmt, attr);
	return ret_lhs;
}

%}

%code requires {
#include <map>
#include <string>
#include <memory>
#include "frontends/verilog/verilog_frontend.h"

struct specify_target {
	char polarity_op;
	std::unique_ptr<YOSYS_NAMESPACE_PREFIX AST::AstNode> dst, dat;
	specify_target& operator=(specify_target&& other) noexcept {
		if (this != &other) {
			dst = std::move(other.dst);
			dat = std::move(other.dat);
			polarity_op = other.polarity_op;
		}
		return *this;
	}
};

struct specify_triple {
	std::unique_ptr<YOSYS_NAMESPACE_PREFIX AST::AstNode> t_min, t_avg, t_max;
	specify_triple& operator=(specify_triple&& other) noexcept {
		if (this != &other) {
			t_min = std::move(other.t_min);
			t_avg = std::move(other.t_avg);
			t_max = std::move(other.t_max);
		}
		return *this;
	}
};

struct specify_rise_fall {
	specify_triple rise;
	specify_triple fall;
};

using string_t = std::string *;
using ast_t = std::unique_ptr<YOSYS_NAMESPACE_PREFIX AST::AstNode>;
using al_t = YOSYS_NAMESPACE_PREFIX dict<YOSYS_NAMESPACE_PREFIX RTLIL::IdString, std::unique_ptr<YOSYS_NAMESPACE_PREFIX AST::AstNode>>*;
using specify_target_ptr_t = std::unique_ptr<struct specify_target>;
using specify_triple_ptr_t = std::unique_ptr<struct specify_triple>;
using specify_rise_fall_ptr_t = std::unique_ptr<struct specify_rise_fall>;
using boolean_t = bool;
using ch_t = char;
using integer_t = int;
using ast_node_type_t = YOSYS_NAMESPACE_PREFIX AST::AstNodeType;
}

%token <string_t> string_t
%token <ast_t> ast_t
%token <al_t> al_t
%token <specify_target_ptr_t> specify_target_ptr_t
%token <specify_triple_ptr_t> specify_triple_ptr_t
%token <specify_rise_fall_ptr_t> specify_rise_fall_ptr_t
%token <boolean_t> boolean_t
%token <ch_t> ch_t
%token <integer_t> integer_t
%token <ast_node_type_t> ast_node_type_t

%token <string_t> TOK_STRING TOK_ID TOK_CONSTVAL TOK_REALVAL TOK_PRIMITIVE
%token <string_t> TOK_SVA_LABEL TOK_SPECIFY_OPER TOK_MSG_TASKS
%token <string_t> TOK_BASE TOK_BASED_CONSTVAL TOK_UNBASED_UNSIZED_CONSTVAL
%token <string_t> TOK_USER_TYPE TOK_PKG_USER_TYPE
%token TOK_ASSERT TOK_ASSUME TOK_RESTRICT TOK_COVER TOK_FINAL
%token ATTR_BEGIN ATTR_END DEFATTR_BEGIN DEFATTR_END
%token TOK_MODULE TOK_ENDMODULE TOK_PARAMETER TOK_LOCALPARAM TOK_DEFPARAM
%token TOK_PACKAGE TOK_ENDPACKAGE TOK_PACKAGESEP
%token TOK_INTERFACE TOK_ENDINTERFACE TOK_MODPORT TOK_VAR TOK_WILDCARD_CONNECT
%token TOK_INPUT TOK_OUTPUT TOK_INOUT TOK_WIRE TOK_WAND TOK_WOR TOK_REG TOK_LOGIC
%token TOK_INTEGER TOK_SIGNED TOK_ASSIGN TOK_ALWAYS TOK_INITIAL
%token TOK_ALWAYS_FF TOK_ALWAYS_COMB TOK_ALWAYS_LATCH
%token TOK_BEGIN TOK_END TOK_IF TOK_ELSE TOK_FOR TOK_WHILE TOK_REPEAT
%token TOK_DPI_FUNCTION TOK_POSEDGE TOK_NEGEDGE TOK_OR TOK_AUTOMATIC
%token TOK_CASE TOK_CASEX TOK_CASEZ TOK_ENDCASE TOK_DEFAULT
%token TOK_FUNCTION TOK_ENDFUNCTION TOK_TASK TOK_ENDTASK TOK_SPECIFY
%token TOK_IGNORED_SPECIFY TOK_ENDSPECIFY TOK_SPECPARAM TOK_SPECIFY_AND TOK_IGNORED_SPECIFY_AND
%token TOK_GENERATE TOK_ENDGENERATE TOK_GENVAR TOK_REAL
%token TOK_SYNOPSYS_FULL_CASE TOK_SYNOPSYS_PARALLEL_CASE
%token TOK_SUPPLY0 TOK_SUPPLY1 TOK_TO_SIGNED TOK_TO_UNSIGNED
%token TOK_POS_INDEXED TOK_NEG_INDEXED TOK_PROPERTY TOK_ENUM TOK_TYPEDEF
%token TOK_RAND TOK_CONST TOK_CHECKER TOK_ENDCHECKER TOK_EVENTUALLY
%token TOK_INCREMENT TOK_DECREMENT TOK_UNIQUE TOK_UNIQUE0 TOK_PRIORITY
%token TOK_STRUCT TOK_PACKED TOK_UNSIGNED TOK_INT TOK_BYTE TOK_SHORTINT TOK_LONGINT TOK_VOID TOK_UNION
%token TOK_BIT_OR_ASSIGN TOK_BIT_AND_ASSIGN TOK_BIT_XOR_ASSIGN TOK_ADD_ASSIGN
%token TOK_SUB_ASSIGN TOK_DIV_ASSIGN TOK_MOD_ASSIGN TOK_MUL_ASSIGN
%token TOK_SHL_ASSIGN TOK_SHR_ASSIGN TOK_SSHL_ASSIGN TOK_SSHR_ASSIGN
%token TOK_BIND TOK_TIME_SCALE

%token TOK_EXCL "!"
%token TOK_HASH "#"
%token TOK_PERC "%"
%token TOK_AMP "&"
%token TOK_LPAREN "("
%token TOK_RPAREN ")"
%token TOK_ASTER "*"
%token TOK_PLUS "+"
%token TOK_COMMA ","
%token TOK_MINUS "-"
%token TOK_DOT "."
%token TOK_SLASH "/"
%token TOK_COL ":"
%token TOK_SEMICOL ";"
%token TOK_LT "<"
%token TOK_EQ "="
%token TOK_GT ">"
%token TOK_QUE "?"
%token TOK_AT "@"
%token TOK_LBRA "["
%token TOK_RBRA "]"
%token TOK_CARET "^"
%token TOK_UNDER "_"
%token TOK_LCURL "{"
%token TOK_PIPE "|"
%token TOK_RCURL "}"
%token TOK_TILDE "~"
%token TOK_n "n"
%token TOK_p "p"
%token TOK_x "x"
%token TOK_z "z"

%type <ast_t> range range_or_multirange non_opt_range non_opt_multirange
%type <ast_t> wire_type expr basic_expr concat_list rvalue lvalue lvalue_concat_list non_io_wire_type io_wire_type
%type <string_t> opt_label opt_sva_label tok_prim_wrapper hierarchical_id hierarchical_type_id integral_number
%type <string_t> type_name
%type <ast_t> opt_enum_init enum_type struct_type enum_struct_type func_return_type typedef_base_type
%type <boolean_t> opt_property always_comb_or_latch always_or_always_ff
%type <boolean_t> opt_signedness_default_signed opt_signedness_default_unsigned
%type <integer_t> integer_atom_type integer_vector_type
%type <al_t> attr case_attr
%type <ast_t> struct_union
%type <ast_node_type_t> asgn_binop inc_or_dec_op
%type <ast_t> genvar_identifier

%type <specify_target_ptr_t> specify_target
%type <specify_triple_ptr_t> specify_triple specify_opt_triple
%type <specify_rise_fall_ptr_t> specify_rise_fall
%type <ast_t> specify_if specify_condition
%type <ch_t> specify_edge

// operator precedence from low to high
%left OP_LOR
%left OP_LAND
%left TOK_PIPE OP_NOR
%left TOK_CARET OP_XNOR
%left TOK_AMP OP_NAND
%left OP_EQ OP_NE OP_EQX OP_NEX
%left TOK_LT OP_LE OP_GE TOK_GT
%left OP_SHL OP_SHR OP_SSHL OP_SSHR
%left TOK_PLUS TOK_MINUS
%left TOK_ASTER TOK_SLASH TOK_PERC
%left OP_POW
%precedence OP_CAST
%precedence UNARY_OPS

%define parse.error verbose
%define parse.lac full

%precedence FAKE_THEN
%precedence TOK_ELSE

%debug
%locations

%%

input: {
	(void)yynerrs_;
	ast_stack.clear();
	ast_stack.push_back(current_ast);
} design {
	ast_stack.pop_back();
	log_assert(GetSize(ast_stack) == 0);
	default_attr_list.clear();
};

design:
	module design |
	defattr design |
	task_func_decl design |
	param_decl design |
	localparam_decl design |
	typedef_decl design |
	package design |
	interface design |
	bind_directive design |
	%empty;

attr:
	{
		if (attr_list != nullptr)
			attr_list_stack.push(attr_list);
		attr_list = new dict<IdString, std::unique_ptr<AstNode>>;
		for (auto &it : default_attr_list)
			(*attr_list)[it.first] = it.second->clone();
	} attr_opt {
		$$ = attr_list;
		if (!attr_list_stack.empty()) {
			attr_list = attr_list_stack.top();
			attr_list_stack.pop();
		} else
			attr_list = nullptr;
	};

attr_opt:
	attr_opt ATTR_BEGIN opt_attr_list ATTR_END {
		SET_RULE_LOC(@$, @2, @$);
	}|
	%empty;

defattr:
	DEFATTR_BEGIN {
		if (attr_list != nullptr)
			attr_list_stack.push(attr_list);
		attr_list = new dict<IdString, std::unique_ptr<AstNode>>;
		default_attr_list.clear();
	} opt_attr_list {
		attr_list->swap(default_attr_list);
		delete attr_list;
		if (!attr_list_stack.empty()) {
			attr_list = attr_list_stack.top();
			attr_list_stack.pop();
		} else
			attr_list = nullptr;
	} DEFATTR_END;

opt_attr_list:
	attr_list | %empty;

attr_list:
	attr_assign |
	attr_list TOK_COMMA attr_assign;

attr_assign:
	hierarchical_id {
		(*attr_list)[*$1] = AstNode::mkconst_int(1, false);
	} |
	hierarchical_id TOK_EQ expr {
		(*attr_list)[*$1] = std::move($3);
	};

hierarchical_id:
	TOK_ID {
		$$ = $1;
	} |
	hierarchical_id TOK_PACKAGESEP TOK_ID {
		if ($3->compare(0, 1, "\\") == 0)
			*$1 += "::" + $3->substr(1);
		else
			*$1 += "::" + *$3;
		$$ = $1;
	} |
	hierarchical_id TOK_DOT TOK_ID {
		if ($3->compare(0, 1, "\\") == 0)
			*$1 += "." + $3->substr(1);
		else
			*$1 += "." + *$3;
		$$ = $1;
	};

hierarchical_type_id:
	TOK_USER_TYPE
	| TOK_PKG_USER_TYPE				// package qualified type name
	| TOK_LPAREN TOK_USER_TYPE TOK_RPAREN	{ $$ = $2; }		// non-standard grammar
	;

module:
	attr TOK_MODULE {
		enterTypeScope();
	} TOK_ID {
		do_not_require_port_stubs = false;
		AstNode* mod = pushChild(std::make_unique<AstNode>(AST_MODULE));
		current_ast_mod = mod;
		port_stubs.clear();
		port_counter = 0;
		mod->str = *$4;
		append_attr(mod, $1);
	} module_para_opt module_args_opt TOK_SEMICOL module_body TOK_ENDMODULE opt_label {
		if (port_stubs.size() != 0)
			frontend_verilog_yyerror("Missing details for module port `%s'.",
					port_stubs.begin()->first.c_str());
		SET_AST_NODE_LOC(ast_stack.back(), @2, @$);
		ast_stack.pop_back();
		log_assert(ast_stack.size() == 1);
		checkLabelsMatch("Module name", $4, $11);
		current_ast_mod = nullptr;
		exitTypeScope();
	};

module_para_opt:
	TOK_HASH TOK_LPAREN module_para_list TOK_RPAREN | %empty;

module_para_list:
	single_module_para | module_para_list TOK_COMMA single_module_para;

single_module_para:
	%empty |
	attr TOK_PARAMETER {
		astbuf1 = std::make_unique<AstNode>(AST_PARAMETER);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
		append_attr(astbuf1.get(), $1);
	} param_type single_param_decl |
	attr TOK_LOCALPARAM {
		astbuf1 = std::make_unique<AstNode>(AST_LOCALPARAM);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
		append_attr(astbuf1.get(), $1);
	} param_type single_param_decl |
	single_param_decl;

module_args_opt:
	TOK_LPAREN TOK_RPAREN | %empty | TOK_LPAREN module_args optional_comma TOK_RPAREN;

module_args:
	module_arg | module_args TOK_COMMA module_arg;

optional_comma:
	TOK_COMMA | %empty;

module_arg_opt_assignment:
	TOK_EQ expr {
		if (ast_stack.back()->children.size() > 0 && ast_stack.back()->children.back()->type == AST_WIRE) {
			if (ast_stack.back()->children.back()->is_input) {
				auto& n = ast_stack.back()->children.back();
				n->attributes[ID::defaultvalue] = std::move($2);
			} else {
				auto wire = std::make_unique<AstNode>(AST_IDENTIFIER);
				wire->str = ast_stack.back()->children.back()->str;
				if (ast_stack.back()->children.back()->is_reg || ast_stack.back()->children.back()->is_logic)
					ast_stack.back()->children.push_back(std::make_unique<AstNode>(AST_INITIAL, std::make_unique<AstNode>(AST_BLOCK, std::make_unique<AstNode>(AST_ASSIGN_LE, std::move(wire), std::move($2)))));
				else
					ast_stack.back()->children.push_back(std::make_unique<AstNode>(AST_ASSIGN, std::move(wire), std::move($2)));
			}
		} else
			frontend_verilog_yyerror("SystemVerilog interface in module port list cannot have a default value.");
	} |
	%empty;

module_arg:
	TOK_ID {
		if (ast_stack.back()->children.size() > 0 && ast_stack.back()->children.back()->type == AST_WIRE) {
			auto node = ast_stack.back()->children.back()->clone();
			node->str = *$1;
			node->port_id = ++port_counter;
			SET_AST_NODE_LOC(node.get(), @1, @1);
			ast_stack.back()->children.push_back(std::move(node));
		} else {
			if (port_stubs.count(*$1) != 0)
				frontend_verilog_yyerror("Duplicate module port `%s'.", $1->c_str());
			port_stubs[*$1] = ++port_counter;
		}
	} module_arg_opt_assignment |
	TOK_ID {
		astbuf1 = std::make_unique<AstNode>(AST_INTERFACEPORT);
		astbuf1->children.push_back(std::make_unique<AstNode>(AST_INTERFACEPORTTYPE));
		astbuf1->children[0]->str = *$1;
	} TOK_ID {  /* SV interfaces */
		if (!sv_mode)
			frontend_verilog_yyerror("Interface found in port list (%s). This is not supported unless read_verilog is called with -sv!", $3->c_str());
		astbuf2 = astbuf1->clone(); // really only needed if multiple instances of same type.
		astbuf2->str = *$3;
		astbuf2->port_id = ++port_counter;
		ast_stack.back()->children.push_back(std::move(astbuf2));
	} module_arg_opt_assignment |
	attr wire_type range_or_multirange TOK_ID {
		auto node = std::move($2);
		node->str = *$4;
		SET_AST_NODE_LOC(node.get(), @4, @4);
		node->port_id = ++port_counter;
		auto range = checkRange(node.get(), std::move($3));
		if (range != nullptr)
			node->children.push_back(std::move(range));
		if (!node->is_input && !node->is_output)
			frontend_verilog_yyerror("Module port `%s' is neither input nor output.", $4->c_str());
		if (node->is_reg && node->is_input && !node->is_output && !sv_mode)
			frontend_verilog_yyerror("Input port `%s' is declared as register.", $4->c_str());
		append_attr(node.get(), $1);
		ast_stack.back()->children.push_back(std::move(node));
	} module_arg_opt_assignment |
	TOK_DOT TOK_DOT TOK_DOT {
		do_not_require_port_stubs = true;
	};

package:
	attr TOK_PACKAGE {
		enterTypeScope();
	} TOK_ID {
		AstNode* mod = pushChild(std::make_unique<AstNode>(AST_PACKAGE));
		current_ast_mod = mod;
		mod->str = *$4;
		append_attr(mod, $1);
	} TOK_SEMICOL package_body TOK_ENDPACKAGE opt_label {
		ast_stack.pop_back();
		checkLabelsMatch("Package name", $4, $9);
		current_ast_mod = nullptr;
		exitTypeScope();
	};

package_body:
	package_body package_body_stmt | %empty;

package_body_stmt:
	typedef_decl | localparam_decl | param_decl | task_func_decl;

interface:
	TOK_INTERFACE {
		enterTypeScope();
	} TOK_ID {
		do_not_require_port_stubs = false;
		AstNode* intf = pushChild(std::make_unique<AstNode>(AST_INTERFACE));
		current_ast_mod = intf;
		port_stubs.clear();
		port_counter = 0;
		intf->str = *$3;
	} module_para_opt module_args_opt TOK_SEMICOL interface_body TOK_ENDINTERFACE {
		if (port_stubs.size() != 0)
			frontend_verilog_yyerror("Missing details for module port `%s'.",
				port_stubs.begin()->first.c_str());
		ast_stack.pop_back();
		log_assert(ast_stack.size() == 1);
		current_ast_mod = nullptr;
		exitTypeScope();
	};

interface_body:
	interface_body interface_body_stmt | %empty;

interface_body_stmt:
	param_decl | localparam_decl | typedef_decl | defparam_decl | wire_decl | always_stmt | assign_stmt |
	modport_stmt | bind_directive;

bind_directive:
	TOK_BIND {
		(void)pushChild(std::make_unique<AstNode>(AST_BIND));
	}
	bind_target {
		// bind_target should have added at least one child
		log_assert(ast_stack.back()->children.size() >= 1);
	}
	TOK_ID {
		// The single_cell parser in cell_list_no_array uses astbuf1 as
		// a sort of template for constructing cells.
		astbuf1 = std::make_unique<AstNode>(AST_CELL);
		astbuf1->children.push_back(std::make_unique<AstNode>(AST_CELLTYPE));
		astbuf1->children[0]->str = *$5;
	}
	cell_parameter_list_opt cell_list_no_array TOK_SEMICOL {
		// cell_list should have added at least one more child
		log_assert(ast_stack.back()->children.size() >= 2);
		(void)astbuf1.reset();
		ast_stack.pop_back();
	};

// bind_target matches the target of the bind (everything before
// bind_instantiation in the IEEE 1800 spec).
//
// We can't use the BNF from the spec directly because it's ambiguous:
// something like "bind foo bar_i (.*)" can either be interpreted with "foo" as
// a module or interface identifier (matching bind_target_scope in the spec) or
// by considering foo as a degenerate hierarchical identifier with no TOK_DOT
// characters, followed by no bit select (which matches bind_target_instance in
// the spec).
//
// Instead, we resolve everything as an instance name and then deal with the
// ambiguity when converting to RTLIL / in the hierarchy pass.
bind_target:
	bind_target_instance opt_bind_target_instance_list;

// An optional list of target instances for a bind statement, introduced by a
// colon.
opt_bind_target_instance_list:
	TOK_COL bind_target_instance_list |
	%empty;

bind_target_instance_list:
	bind_target_instance |
	bind_target_instance_list TOK_COMMA bind_target_instance;

// A single target instance for a bind statement. The top of ast_stack will be
// the bind node where we should add it.
bind_target_instance:
	hierarchical_id {
		auto node = std::make_unique<AstNode>(AST_IDENTIFIER);
		node->str = *$1;
		ast_stack.back()->children.push_back(std::move(node));
	};

mintypmax_expr:
	expr { } |
	expr TOK_COL expr TOK_COL expr { };

non_opt_delay:
	TOK_HASH TOK_ID { } |
	TOK_HASH TOK_CONSTVAL { } |
	TOK_HASH TOK_REALVAL { } |
	// our `expr` doesn't have time_scale, so we need the parenthesized variant
	TOK_HASH TOK_TIME_SCALE |
	TOK_HASH TOK_LPAREN TOK_TIME_SCALE TOK_RPAREN |
	TOK_HASH TOK_LPAREN mintypmax_expr TOK_RPAREN |
	TOK_HASH TOK_LPAREN mintypmax_expr TOK_COMMA mintypmax_expr TOK_RPAREN |
	TOK_HASH TOK_LPAREN mintypmax_expr TOK_COMMA mintypmax_expr TOK_COMMA mintypmax_expr TOK_RPAREN;

delay:
	non_opt_delay | %empty;

io_wire_type:
	{ astbuf3 = std::make_unique<AstNode>(AST_WIRE); current_wire_rand = false; current_wire_const = false; }
	wire_type_token_io wire_type_const_rand opt_wire_type_token wire_type_signedness
	{ $$ = std::move(astbuf3); SET_RULE_LOC(@$, @2, @$); };

non_io_wire_type:
	{ astbuf3 = std::make_unique<AstNode>(AST_WIRE); current_wire_rand = false; current_wire_const = false; }
	wire_type_const_rand wire_type_token wire_type_signedness
	{ $$ = std::move(astbuf3); SET_RULE_LOC(@$, @2, @$); };

wire_type:
	io_wire_type { $$ = std::move($1); }  |
	non_io_wire_type { $$ = std::move($1); };

wire_type_token_io:
	TOK_INPUT {
		astbuf3->is_input = true;
	} |
	TOK_OUTPUT {
		astbuf3->is_output = true;
	} |
	TOK_INOUT {
		astbuf3->is_input = true;
		astbuf3->is_output = true;
	};

wire_type_signedness:
	TOK_SIGNED   { astbuf3->is_signed = true;  } |
	TOK_UNSIGNED { astbuf3->is_signed = false; } |
	%empty;

wire_type_const_rand:
	TOK_RAND TOK_CONST {
	    current_wire_rand = true;
	    current_wire_const = true;
	} |
	TOK_CONST {
	    current_wire_const = true;
	} |
	TOK_RAND {
	    current_wire_rand = true;
	} |
	%empty;

opt_wire_type_token:
	wire_type_token | %empty;

wire_type_token:
	// nets
	net_type {
	} |
	net_type logic_type {
	} |
	// regs
	TOK_REG {
		astbuf3->is_reg = true;
	} |
	TOK_VAR TOK_REG {
		astbuf3->is_reg = true;
	} |
	// logics
	TOK_VAR {
		astbuf3->is_logic = true;
	} |
	TOK_VAR logic_type {
		astbuf3->is_logic = true;
	} |
	logic_type {
		astbuf3->is_logic = true;
	} |
	TOK_GENVAR {
		astbuf3->type = AST_GENVAR;
		astbuf3->is_reg = true;
		astbuf3->is_signed = true;
		astbuf3->range_left = 31;
		astbuf3->range_right = 0;
	};

net_type:
	TOK_WOR {
		astbuf3->is_wor = true;
	} |
	TOK_WAND {
		astbuf3->is_wand = true;
	} |
	TOK_WIRE;

logic_type:
	TOK_LOGIC {
	} |
	integer_atom_type {
		astbuf3->range_left = $1 - 1;
		astbuf3->range_right = 0;
		astbuf3->is_signed = true;
	} |
	hierarchical_type_id {
		addWiretypeNode($1, astbuf3.get());
	};

integer_atom_type:
	TOK_INTEGER	{ $$ = 32; } |
	TOK_INT		{ $$ = 32; } |
	TOK_SHORTINT	{ $$ = 16; } |
	TOK_LONGINT	{ $$ = 64; } |
	TOK_BYTE	{ $$ =  8; } ;

integer_vector_type:
	TOK_LOGIC { $$ = token::TOK_LOGIC; } |
	TOK_REG   { $$ = token::TOK_REG; } ;

non_opt_range:
	TOK_LBRA expr TOK_COL expr TOK_RBRA {
		$$ = std::make_unique<AstNode>(AST_RANGE);
		$$->children.push_back(std::move($2));
		$$->children.push_back(std::move($4));
	} |
	TOK_LBRA expr TOK_POS_INDEXED expr TOK_RBRA {
		$$ = std::make_unique<AstNode>(AST_RANGE);
		auto expr = std::make_unique<AstNode>(AST_SELFSZ, std::move($2));
		$$->children.push_back(std::make_unique<AstNode>(AST_SUB, std::make_unique<AstNode>(AST_ADD, expr->clone(), std::move($4)), AstNode::mkconst_int(1, true)));
		$$->children.push_back(std::make_unique<AstNode>(AST_ADD, std::move(expr), AstNode::mkconst_int(0, true)));
	} |
	TOK_LBRA expr TOK_NEG_INDEXED expr TOK_RBRA {
		$$ = std::make_unique<AstNode>(AST_RANGE);
		auto expr = std::make_unique<AstNode>(AST_SELFSZ, std::move($2));
		$$->children.push_back(std::make_unique<AstNode>(AST_ADD, expr->clone(), AstNode::mkconst_int(0, true)));
		$$->children.push_back(std::make_unique<AstNode>(AST_SUB, std::make_unique<AstNode>(AST_ADD, std::move(expr), AstNode::mkconst_int(1, true)), std::move($4)));
	} |
	TOK_LBRA expr TOK_RBRA {
		$$ = std::make_unique<AstNode>(AST_RANGE);
		$$->children.push_back(std::move($2));
	};

non_opt_multirange:
	non_opt_range non_opt_range {
		$$ = std::make_unique<AstNode>(AST_MULTIRANGE, std::move($1), std::move($2));
	} |
	non_opt_multirange non_opt_range {
		$$ = std::move($1);
		$$->children.push_back(std::move($2));
	};

range:
	non_opt_range {
		$$ = std::move($1);
	} |
	%empty {
		$$ = nullptr;
	};

range_or_multirange:
	range { $$ = std::move($1); } |
	non_opt_multirange { $$ = std::move($1); };

module_body:
	module_body module_body_stmt |
	/* the following line makes the generate..endgenrate keywords optional */
	module_body gen_stmt |
	module_body gen_block |
	module_body TOK_SEMICOL |
	%empty;

module_body_stmt:
	task_func_decl | specify_block | param_decl | localparam_decl | typedef_decl | defparam_decl | specparam_declaration | wire_decl | assign_stmt | cell_stmt |
	enum_decl | struct_decl | bind_directive |
	always_stmt | TOK_GENERATE module_gen_body TOK_ENDGENERATE | defattr | assert_property | checker_decl | ignored_specify_block;

checker_decl:
	TOK_CHECKER TOK_ID TOK_SEMICOL {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_GENBLOCK));
		node->str = *$2;
	} module_body TOK_ENDCHECKER {
		ast_stack.pop_back();
	};

task_func_decl:
	attr TOK_DPI_FUNCTION TOK_ID TOK_ID {
		current_function_or_task = saveChild(std::make_unique<AstNode>(AST_DPI_FUNCTION, AstNode::mkconst_str(*$3), AstNode::mkconst_str(*$4)));
		current_function_or_task->str = *$4;
		append_attr(current_function_or_task, $1);
	} opt_dpi_function_args TOK_SEMICOL {
		current_function_or_task = nullptr;
	} |
	attr TOK_DPI_FUNCTION TOK_ID TOK_EQ TOK_ID TOK_ID {
		current_function_or_task = saveChild(std::make_unique<AstNode>(AST_DPI_FUNCTION, AstNode::mkconst_str(*$5), AstNode::mkconst_str(*$3)));
		current_function_or_task->str = *$6;
		append_attr(current_function_or_task, $1);
	} opt_dpi_function_args TOK_SEMICOL {
		current_function_or_task = nullptr;
	} |
	attr TOK_DPI_FUNCTION TOK_ID TOK_COL TOK_ID TOK_EQ TOK_ID TOK_ID {
		current_function_or_task = saveChild(std::make_unique<AstNode>(AST_DPI_FUNCTION, AstNode::mkconst_str(*$7), AstNode::mkconst_str(*$3 + ":" + RTLIL::unescape_id(*$5))));
		current_function_or_task->str = *$8;
		append_attr(current_function_or_task, $1);
	} opt_dpi_function_args TOK_SEMICOL {
		current_function_or_task = nullptr;
	} |
	attr TOK_TASK opt_automatic TOK_ID {
		current_function_or_task = pushChild(std::make_unique<AstNode>(AST_TASK));
		current_function_or_task->str = *$4;
		append_attr(current_function_or_task, $1);
		current_function_or_task_port_id = 1;
	} task_func_args_opt TOK_SEMICOL task_func_body TOK_ENDTASK {
		current_function_or_task = nullptr;
		ast_stack.pop_back();
	} |
	attr TOK_FUNCTION opt_automatic TOK_VOID TOK_ID {
		// The difference between void functions and tasks is that
		// always_comb's implicit sensitivity list behaves as if functions were
		// inlined, but ignores signals read only in tasks. This only matters
		// for event based simulation, and for synthesis we can treat a void
		// function like a task.
		current_function_or_task = pushChild(std::make_unique<AstNode>(AST_TASK));
		current_function_or_task->str = *$5;
		append_attr(current_function_or_task, $1);
		current_function_or_task_port_id = 1;
	} task_func_args_opt TOK_SEMICOL task_func_body TOK_ENDFUNCTION {
		current_function_or_task = nullptr;
		ast_stack.pop_back();
	} |
	attr TOK_FUNCTION opt_automatic func_return_type TOK_ID {
		current_function_or_task = pushChild(std::make_unique<AstNode>(AST_FUNCTION));
		current_function_or_task->str = *$5;
		append_attr(current_function_or_task, $1);
		auto outreg = std::make_unique<AstNode>(AST_WIRE);
		outreg->str = *$5;
		outreg->is_signed = false;
		outreg->is_reg = true;
		if ($4 != nullptr) {
			outreg->is_signed = $4->is_signed;
			$4->is_signed = false;
			outreg->is_custom_type = $4->type == AST_WIRETYPE;
			outreg->children.push_back(std::move($4));
		}
		current_function_or_task->children.push_back(std::move(outreg));
		current_function_or_task_port_id = 1;
	} task_func_args_opt TOK_SEMICOL task_func_body TOK_ENDFUNCTION {
		current_function_or_task = nullptr;
		ast_stack.pop_back();
	};

func_return_type:
	hierarchical_type_id {
		$$ = std::make_unique<AstNode>(AST_WIRETYPE);
		$$->str = *$1;
	} |
	opt_type_vec opt_signedness_default_unsigned {
		$$ = makeRange(0, 0, $2);
	} |
	opt_type_vec opt_signedness_default_unsigned non_opt_range {
		$$ = std::move($3);
		$$->is_signed = $2;
	} |
	integer_atom_type opt_signedness_default_signed {
		$$ = makeRange($1 - 1, 0, $2);
	};

opt_type_vec:
	  %empty
	| TOK_REG
	| TOK_LOGIC
	;

opt_signedness_default_signed:
	  %empty	{ $$ = true; }
	| TOK_SIGNED	{ $$ = true; }
	| TOK_UNSIGNED	{ $$ = false; }
	;
opt_signedness_default_unsigned:
	  %empty	{ $$ = false; }
	| TOK_SIGNED	{ $$ = true; }
	| TOK_UNSIGNED	{ $$ = false; }
	;

dpi_function_arg:
	TOK_ID TOK_ID {
		current_function_or_task->children.push_back(AstNode::mkconst_str(*$1));
	} |
	TOK_ID {
		current_function_or_task->children.push_back(AstNode::mkconst_str(*$1));
	};

opt_dpi_function_args:
	TOK_LPAREN dpi_function_args TOK_RPAREN |
	%empty;

dpi_function_args:
	dpi_function_args TOK_COMMA dpi_function_arg |
	dpi_function_args TOK_COMMA |
	dpi_function_arg |
	%empty;

opt_automatic:
	TOK_AUTOMATIC |
	%empty;

task_func_args_opt:
	TOK_LPAREN TOK_RPAREN | %empty | TOK_LPAREN {
		albuf = nullptr;
		astbuf1 = nullptr;
		astbuf2 = nullptr;
	} task_func_args optional_comma {
		(void)astbuf1.reset();
		if (astbuf2 != nullptr)
			(void)astbuf2.reset();
		free_attr(albuf);
	} TOK_RPAREN;

task_func_args:
	task_func_port | task_func_args TOK_COMMA task_func_port;

task_func_port:
	attr wire_type range_or_multirange {
		bool prev_was_input = true;
		bool prev_was_output = false;
		if (albuf) {
			prev_was_input = astbuf1->is_input;
			prev_was_output = astbuf1->is_output;
			(void)astbuf1.reset();
			if (astbuf2 != nullptr)
				(void)astbuf2.reset();
			free_attr(albuf);
		}
		albuf = $1;
		astbuf1 = std::move($2);
		astbuf2 = checkRange(astbuf1.get(), std::move($3));
		if (!astbuf1->is_input && !astbuf1->is_output) {
			if (!sv_mode)
				frontend_verilog_yyerror("task/function argument direction missing");
			astbuf1->is_input = prev_was_input;
			astbuf1->is_output = prev_was_output;
		}
	} wire_name |
	{
		if (!astbuf1) {
			if (!sv_mode)
				frontend_verilog_yyerror("task/function argument direction missing");
			albuf = new dict<IdString, std::unique_ptr<AstNode>>;
			astbuf1 = std::make_unique<AstNode>(AST_WIRE);
			current_wire_rand = false;
			current_wire_const = false;
			astbuf1->is_input = true;
			astbuf2 = nullptr;
		}
	} wire_name;

task_func_body:
	task_func_body behavioral_stmt |
	%empty;

/*************************** specify parser ***************************/

specify_block:
	TOK_SPECIFY specify_item_list TOK_ENDSPECIFY;

specify_item_list:
	specify_item specify_item_list |
	%empty;

specify_item:
	specify_if TOK_LPAREN specify_edge expr TOK_SPECIFY_OPER specify_target TOK_RPAREN TOK_EQ specify_rise_fall TOK_SEMICOL {
		auto en_expr = std::move($1);
		char specify_edge = $3;
		auto src_expr = std::move($4);
		string *oper = $5;
		specify_target_ptr_t target = std::move($6);
		specify_rise_fall_ptr_t timing = std::move($9);

		if (specify_edge != 0 && target->dat == nullptr)
			frontend_verilog_yyerror("Found specify edge but no data spec.\n");

		auto cell_owned = std::make_unique<AstNode>(AST_CELL);
		auto cell = cell_owned.get();
		ast_stack.back()->children.push_back(std::move(cell_owned));
		cell->str = stringf("$specify$%d", autoidx++);
		cell->children.push_back(std::make_unique<AstNode>(AST_CELLTYPE));
		cell->children.back()->str = target->dat ? "$specify3" : "$specify2";
		SET_AST_NODE_LOC(cell, en_expr.get() ? @1 : @2, @10);

		char oper_polarity = 0;
		char oper_type = oper->at(0);

		if (oper->size() == 3) {
			oper_polarity = oper->at(0);
			oper_type = oper->at(1);
		}

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, AstNode::mkconst_int(oper_type == '*', false, 1)));
		cell->children.back()->str = "\\FULL";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, AstNode::mkconst_int(oper_polarity != 0, false, 1)));
		cell->children.back()->str = "\\SRC_DST_PEN";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, AstNode::mkconst_int(oper_polarity == '+', false, 1)));
		cell->children.back()->str = "\\SRC_DST_POL";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(timing->rise.t_min)));
		cell->children.back()->str = "\\T_RISE_MIN";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(timing->rise.t_avg)));
		cell->children.back()->str = "\\T_RISE_TYP";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(timing->rise.t_max)));
		cell->children.back()->str = "\\T_RISE_MAX";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(timing->fall.t_min)));
		cell->children.back()->str = "\\T_FALL_MIN";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(timing->fall.t_avg)));
		cell->children.back()->str = "\\T_FALL_TYP";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(timing->fall.t_max)));
		cell->children.back()->str = "\\T_FALL_MAX";

		cell->children.push_back(std::make_unique<AstNode>(AST_ARGUMENT, en_expr ? std::move(en_expr) : AstNode::mkconst_int(1, false, 1)));
		cell->children.back()->str = "\\EN";

		cell->children.push_back(std::make_unique<AstNode>(AST_ARGUMENT, std::move(src_expr)));
		cell->children.back()->str = "\\SRC";

		cell->children.push_back(std::make_unique<AstNode>(AST_ARGUMENT, std::move(target->dst)));
		cell->children.back()->str = "\\DST";

		if (target->dat)
		{
			cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, AstNode::mkconst_int(specify_edge != 0, false, 1)));
			cell->children.back()->str = "\\EDGE_EN";

			cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, AstNode::mkconst_int(specify_edge == 'p', false, 1)));
			cell->children.back()->str = "\\EDGE_POL";

			cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, AstNode::mkconst_int(target->polarity_op != 0, false, 1)));
			cell->children.back()->str = "\\DAT_DST_PEN";

			cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, AstNode::mkconst_int(target->polarity_op == '+', false, 1)));
			cell->children.back()->str = "\\DAT_DST_POL";

			cell->children.push_back(std::make_unique<AstNode>(AST_ARGUMENT, std::move(target->dat)));
			cell->children.back()->str = "\\DAT";
		}

		delete oper;
	} |
	TOK_ID TOK_LPAREN specify_edge expr specify_condition TOK_COMMA specify_edge expr specify_condition TOK_COMMA specify_triple specify_opt_triple TOK_RPAREN TOK_SEMICOL {
		if (*$1 != "$setup" && *$1 != "$hold" && *$1 != "$setuphold" && *$1 != "$removal" && *$1 != "$recovery" &&
				*$1 != "$recrem" && *$1 != "$skew" && *$1 != "$timeskew" && *$1 != "$fullskew" && *$1 != "$nochange")
			frontend_verilog_yyerror("Unsupported specify rule type: %s\n", $1->c_str());

		auto src_pen = AstNode::mkconst_int($3 != 0, false, 1);
		auto src_pol = AstNode::mkconst_int($3 == 'p', false, 1);
		auto src_expr = std::move($4), src_en = $5 ? std::move($5) : AstNode::mkconst_int(1, false, 1);

		auto dst_pen = AstNode::mkconst_int($7 != 0, false, 1);
		auto dst_pol = AstNode::mkconst_int($7 == 'p', false, 1);
		auto dst_expr = std::move($8), dst_en = $9 ? std::move($9) : AstNode::mkconst_int(1, false, 1);

		specify_triple_ptr_t limit = std::move($11);
		specify_triple_ptr_t limit2 = std::move($12);

		auto cell_owned = std::make_unique<AstNode>(AST_CELL);
		auto cell = cell_owned.get();
		ast_stack.back()->children.push_back(std::move(cell_owned));
		cell->str = stringf("$specify$%d", autoidx++);
		cell->children.push_back(std::make_unique<AstNode>(AST_CELLTYPE));
		cell->children.back()->str = "$specrule";
		SET_AST_NODE_LOC(cell, @1, @14);

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, AstNode::mkconst_str(*$1)));
		cell->children.back()->str = "\\TYPE";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(limit->t_min)));
		cell->children.back()->str = "\\T_LIMIT_MIN";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(limit->t_avg)));
		cell->children.back()->str = "\\T_LIMIT_TYP";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(limit->t_max)));
		cell->children.back()->str = "\\T_LIMIT_MAX";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, limit2 ? std::move(limit2->t_min) : AstNode::mkconst_int(0, true)));
		cell->children.back()->str = "\\T_LIMIT2_MIN";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, limit2 ? std::move(limit2->t_avg) : AstNode::mkconst_int(0, true)));
		cell->children.back()->str = "\\T_LIMIT2_TYP";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, limit2 ? std::move(limit2->t_max) : AstNode::mkconst_int(0, true)));
		cell->children.back()->str = "\\T_LIMIT2_MAX";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(src_pen)));
		cell->children.back()->str = "\\SRC_PEN";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(src_pol)));
		cell->children.back()->str = "\\SRC_POL";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(dst_pen)));
		cell->children.back()->str = "\\DST_PEN";

		cell->children.push_back(std::make_unique<AstNode>(AST_PARASET, std::move(dst_pol)));
		cell->children.back()->str = "\\DST_POL";

		cell->children.push_back(std::make_unique<AstNode>(AST_ARGUMENT, std::move(src_en)));
		cell->children.back()->str = "\\SRC_EN";

		cell->children.push_back(std::make_unique<AstNode>(AST_ARGUMENT, std::move(src_expr)));
		cell->children.back()->str = "\\SRC";

		cell->children.push_back(std::make_unique<AstNode>(AST_ARGUMENT, std::move(dst_en)));
		cell->children.back()->str = "\\DST_EN";

		cell->children.push_back(std::make_unique<AstNode>(AST_ARGUMENT, std::move(dst_expr)));
		cell->children.back()->str = "\\DST";
	};

specify_opt_triple:
	TOK_COMMA specify_triple {
		$$ = std::move($2);
	} |
	%empty {
		$$ = nullptr;
	};

specify_if:
	TOK_IF TOK_LPAREN expr TOK_RPAREN {
		$$ = std::move($3);
	} |
	%empty {
		$$ = nullptr;
	};

specify_condition:
	TOK_SPECIFY_AND expr {
		$$ = std::move($2);
	} |
	%empty {
		$$ = nullptr;
	};

specify_target:
	expr {
		$$ = std::make_unique<struct specify_target>();
		$$->polarity_op = 0;
		$$->dst = std::move($1);
		$$->dat = nullptr;
	} |
	TOK_LPAREN expr TOK_COL expr TOK_RPAREN{
		$$ = std::make_unique<struct specify_target>();
		$$->polarity_op = 0;
		$$->dst = std::move($2);
		$$->dat = std::move($4);
	} |
	TOK_LPAREN expr TOK_NEG_INDEXED expr TOK_RPAREN{
		$$ = std::make_unique<struct specify_target>();
		$$->polarity_op = '-';
		$$->dst = std::move($2);
		$$->dat = std::move($4);
	} |
	TOK_LPAREN expr TOK_POS_INDEXED expr TOK_RPAREN{
		$$ = std::make_unique<struct specify_target>();
		$$->polarity_op = '+';
		$$->dst = std::move($2);
		$$->dat = std::move($4);
	};

specify_edge:
	TOK_POSEDGE { $$ = 'p'; } |
	TOK_NEGEDGE { $$ = 'n'; } |
	%empty { $$ = 0; };

specify_rise_fall:
	specify_triple {
		$$ = std::make_unique<struct specify_rise_fall>();
		$$->fall.t_min = $1->t_min->clone();
		$$->fall.t_avg = $1->t_avg->clone();
		$$->fall.t_max = $1->t_max->clone();
		$$->rise = std::move(*$1);
	} |
	TOK_LPAREN specify_triple TOK_COMMA specify_triple TOK_RPAREN {
		$$ = std::make_unique<struct specify_rise_fall>();
		$$->rise = std::move(*$2);
		$$->fall = std::move(*$4);
	} |
	TOK_LPAREN specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_RPAREN {
		$$ = std::make_unique<struct specify_rise_fall>();
		$$->rise = std::move(*$2);
		$$->fall = std::move(*$4);
		log_file_warning(current_filename, @$.begin.line, "Path delay expressions beyond rise/fall not currently supported. Ignoring.\n");
	} |
	TOK_LPAREN specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_RPAREN {
		$$ = std::make_unique<struct specify_rise_fall>();
		$$->rise = std::move(*$2);
		$$->fall = std::move(*$4);
		log_file_warning(current_filename, @$.begin.line, "Path delay expressions beyond rise/fall not currently supported. Ignoring.\n");
	} |
	TOK_LPAREN specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_COMMA specify_triple TOK_RPAREN {
		$$ = std::make_unique<struct specify_rise_fall>();
		$$->rise = std::move(*$2);
		$$->fall = std::move(*$4);
		log_file_warning(current_filename, @$.begin.line, "Path delay expressions beyond rise/fall not currently supported. Ignoring.\n");
	}

specify_triple:
	expr {
		$$ = std::make_unique<struct specify_triple>();
		$$->t_avg = $1->clone();
		$$->t_max = $1->clone();
		$$->t_min = std::move($1);
	} |
	expr TOK_COL expr TOK_COL expr {
		$$ = std::make_unique<struct specify_triple>();
		$$->t_min = std::move($1);
		$$->t_avg = std::move($3);
		$$->t_max = std::move($5);
	};

/******************** ignored specify parser **************************/

ignored_specify_block:
	TOK_IGNORED_SPECIFY ignored_specify_item_opt TOK_ENDSPECIFY |
	TOK_IGNORED_SPECIFY TOK_ENDSPECIFY ;

ignored_specify_item_opt:
	ignored_specify_item_opt ignored_specify_item |
	ignored_specify_item ;

ignored_specify_item:
	specparam_declaration
	// | pulsestyle_declaration
	// | showcancelled_declaration
	| path_declaration
	| system_timing_declaration
	;

specparam_declaration:
	TOK_SPECPARAM list_of_specparam_assignments TOK_SEMICOL |
	TOK_SPECPARAM specparam_range list_of_specparam_assignments TOK_SEMICOL ;

// IEEE 1364-2005 calls this sinmply 'range' but the current 'range' rule allows empty match
// and the 'non_opt_range' rule allows index ranges not allowed by 1364-2005
// exxxxtending this for SV specparam would change this anyhow
specparam_range:
	TOK_LBRA ignspec_constant_expression TOK_COL ignspec_constant_expression TOK_RBRA ;

list_of_specparam_assignments:
	specparam_assignment | list_of_specparam_assignments TOK_COMMA specparam_assignment;

specparam_assignment:
	ignspec_id TOK_EQ ignspec_expr ;

ignspec_opt_cond:
	TOK_IF TOK_LPAREN ignspec_expr TOK_RPAREN | %empty;

path_declaration :
	simple_path_declaration TOK_SEMICOL
	// | edge_sensitive_path_declaration
	// | state_dependent_path_declaration
	;

simple_path_declaration :
	ignspec_opt_cond parallel_path_description TOK_EQ path_delay_value |
	ignspec_opt_cond full_path_description TOK_EQ path_delay_value
	;

path_delay_value :
	TOK_LPAREN ignspec_expr list_of_path_delay_extra_expressions TOK_RPAREN
	|     ignspec_expr
	|     ignspec_expr list_of_path_delay_extra_expressions
	;

list_of_path_delay_extra_expressions :
	TOK_COMMA ignspec_expr
	| TOK_COMMA ignspec_expr list_of_path_delay_extra_expressions
	;

specify_edge_identifier :
	TOK_POSEDGE | TOK_NEGEDGE ;

parallel_path_description :
	TOK_LPAREN specify_input_terminal_descriptor opt_polarity_operator TOK_EQ TOK_GT specify_output_terminal_descriptor TOK_RPAREN |
	TOK_LPAREN specify_edge_identifier specify_input_terminal_descriptor TOK_EQ TOK_GT TOK_LPAREN specify_output_terminal_descriptor opt_polarity_operator TOK_COL ignspec_expr TOK_RPAREN TOK_RPAREN |
	TOK_LPAREN specify_edge_identifier specify_input_terminal_descriptor TOK_EQ TOK_GT TOK_LPAREN specify_output_terminal_descriptor TOK_POS_INDEXED ignspec_expr TOK_RPAREN TOK_RPAREN ;

full_path_description :
	TOK_LPAREN list_of_path_inputs TOK_ASTER TOK_GT list_of_path_outputs TOK_RPAREN |
	TOK_LPAREN specify_edge_identifier list_of_path_inputs TOK_ASTER TOK_GT TOK_LPAREN list_of_path_outputs opt_polarity_operator TOK_COL ignspec_expr TOK_RPAREN TOK_RPAREN |
	TOK_LPAREN specify_edge_identifier list_of_path_inputs TOK_ASTER TOK_GT TOK_LPAREN list_of_path_outputs TOK_POS_INDEXED ignspec_expr TOK_RPAREN TOK_RPAREN ;

// This was broken into 2 rules to solve shift/reduce conflicts
list_of_path_inputs :
	specify_input_terminal_descriptor                  opt_polarity_operator  |
	specify_input_terminal_descriptor more_path_inputs opt_polarity_operator ;

more_path_inputs :
    TOK_COMMA specify_input_terminal_descriptor |
    more_path_inputs TOK_COMMA specify_input_terminal_descriptor ;

list_of_path_outputs :
	specify_output_terminal_descriptor |
	list_of_path_outputs TOK_COMMA specify_output_terminal_descriptor ;

opt_polarity_operator :
	TOK_PLUS | TOK_MINUS | %empty;

// Good enough for the time being
specify_input_terminal_descriptor :
	ignspec_id ;

// Good enough for the time being
specify_output_terminal_descriptor :
	ignspec_id ;

system_timing_declaration :
	ignspec_id TOK_LPAREN system_timing_args TOK_RPAREN TOK_SEMICOL ;

system_timing_arg :
	TOK_POSEDGE ignspec_id |
	TOK_NEGEDGE ignspec_id |
	ignspec_expr ;

system_timing_args :
	system_timing_arg |
	system_timing_args TOK_IGNORED_SPECIFY_AND system_timing_arg |
	system_timing_args TOK_COMMA system_timing_arg ;

// for the time being this is OK, but we may write our own expr here.
// as I'm not sure it is legal to use a full expr here (probably not)
// On the other hand, other rules requiring constant expressions also use 'expr'
// (such as param assignment), so we may leave this as-is, perhaps adding runtime checks for constant-ness
ignspec_constant_expression:
	expr {  };

ignspec_expr:
	expr {  } |
	expr TOK_COL expr TOK_COL expr {
	};

ignspec_id:
	TOK_ID {  }
	range_or_multirange {  };

/**********************************************************************/

param_signed:
	TOK_SIGNED {
		astbuf1->is_signed = true;
	} | TOK_UNSIGNED {
		astbuf1->is_signed = false;
	} | %empty;

param_integer:
	type_atom {
		astbuf1->is_reg = false;
	};

param_real:
	TOK_REAL {
		astbuf1->children.push_back(std::make_unique<AstNode>(AST_REALVALUE));
	};

param_range:
	range {
		if ($1 != nullptr) {
			astbuf1->children.push_back(std::move($1));
		}
	};

param_integer_type: param_integer param_signed;
param_range_type:
	type_vec param_signed {
		addRange(astbuf1.get(), 0, 0);
	} |
	type_vec param_signed non_opt_range {
		astbuf1->children.push_back(std::move($3));
	};
param_implicit_type: param_signed param_range;

param_type:
	param_integer_type | param_real | param_range_type | param_implicit_type |
	hierarchical_type_id {
		addWiretypeNode($1, astbuf1.get());
	};

param_decl:
	attr TOK_PARAMETER {
		astbuf1 = std::make_unique<AstNode>(AST_PARAMETER);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
		append_attr(astbuf1.get(), $1);
	} param_type param_decl_list TOK_SEMICOL {
		(void)astbuf1.reset();
	};

localparam_decl:
	attr TOK_LOCALPARAM {
		astbuf1 = std::make_unique<AstNode>(AST_LOCALPARAM);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
		append_attr(astbuf1.get(), $1);
	} param_type param_decl_list TOK_SEMICOL {
		(void)astbuf1.reset();
	};

param_decl_list:
	single_param_decl | param_decl_list TOK_COMMA single_param_decl;

single_param_decl:
	single_param_decl_ident TOK_EQ expr {
		AstNode *decl = ast_stack.back()->children.back().get();
		log_assert(decl->type == AST_PARAMETER || decl->type == AST_LOCALPARAM);
		decl->children[0] = std::move($3);
	} |
	single_param_decl_ident {
		AstNode *decl = ast_stack.back()->children.back().get();
		if (decl->type != AST_PARAMETER) {
			log_assert(decl->type == AST_LOCALPARAM);
			frontend_verilog_yyerror("localparam initialization is missing!");
		}
		if (!sv_mode)
			frontend_verilog_yyerror("Parameter defaults can only be omitted in SystemVerilog mode!");
		decl->children.erase(decl->children.begin());
	};

single_param_decl_ident:
	TOK_ID {
		std::unique_ptr<AstNode> node_owned;
		if (astbuf1 == nullptr) {
			if (!sv_mode)
				frontend_verilog_yyerror("In pure Verilog (not SystemVerilog), parameter/localparam with an initializer must use the parameter/localparam keyword");
			node_owned = std::make_unique<AstNode>(AST_PARAMETER);
			node_owned->children.push_back(AstNode::mkconst_int(0, true));
		} else {
			node_owned = astbuf1->clone();
		}
		node_owned->str = *$1;
		auto node = node_owned.get();
		ast_stack.back()->children.push_back(std::move(node_owned));
		SET_AST_NODE_LOC(node, @1, @1);
	};

defparam_decl:
	TOK_DEFPARAM defparam_decl_list TOK_SEMICOL;

defparam_decl_list:
	single_defparam_decl | defparam_decl_list TOK_COMMA single_defparam_decl;

single_defparam_decl:
	range rvalue TOK_EQ expr {
		auto node = std::make_unique<AstNode>(AST_DEFPARAM);
		node->children.push_back(std::move($2));
		node->children.push_back(std::move($4));
		if ($1 != nullptr)
			node->children.push_back(std::move($1));
		ast_stack.back()->children.push_back(std::move(node));
	};

/////////
// enum
/////////

enum_type: TOK_ENUM {
		static int enum_count;
		// create parent node for the enum
		astbuf2 = std::make_unique<AstNode>(AST_ENUM);
		astbuf2->str = std::string("$enum");
		astbuf2->str += std::to_string(enum_count++);
		log_assert(!cell_hack);
		cell_hack = astbuf2.get();
		ast_stack.back()->children.push_back(std::move(astbuf2));
		// create the template for the names
		astbuf1 = std::make_unique<AstNode>(AST_ENUM_ITEM);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
	} enum_base_type TOK_LCURL enum_name_list optional_comma TOK_RCURL {
		// create template for the enum vars
		log_assert(cell_hack);
		auto tnode_owned = astbuf1->clone();
		auto* tnode = tnode_owned.get();
		astbuf1 = std::move(tnode_owned);
		tnode->type = AST_WIRE;
		tnode->attributes[ID::enum_type] = AstNode::mkconst_str(cell_hack->str);
		cell_hack = nullptr;
		// drop constant but keep any range
		tnode->children.erase(tnode->children.begin());
		$$ = astbuf1->clone();
	};

enum_base_type: type_atom type_signing
	| type_vec type_signing range	{ if ($3) astbuf1->children.push_back(std::move($3)); }
	| %empty			{ astbuf1->is_reg = true; addRange(astbuf1.get()); }
	;

type_atom:
	integer_atom_type {
		astbuf1->is_reg = true;
		astbuf1->is_signed = true;
		addRange(astbuf1.get(), $1 - 1, 0);
	};

type_vec: TOK_REG		{ astbuf1->is_reg   = true; }		// unsigned
	| TOK_LOGIC		{ astbuf1->is_logic = true; }		// unsigned
	;

type_signing:
	  TOK_SIGNED		{ astbuf1->is_signed = true; }
	| TOK_UNSIGNED		{ astbuf1->is_signed = false; }
	| %empty
	;

enum_name_list: enum_name_decl
	| enum_name_list TOK_COMMA enum_name_decl
	;

enum_name_decl:
	TOK_ID opt_enum_init {
		// put in fn
		log_assert((bool)astbuf1);
		log_assert((bool)cell_hack);
		auto node = astbuf1->clone();
		node->str = *$1;
		SET_AST_NODE_LOC(node.get(), @1, @1);
		node->children[0] = $2 ? std::move($2) : std::make_unique<AstNode>(AST_NONE);
		cell_hack->children.push_back(std::move(node));
	}
	;

opt_enum_init:
	TOK_EQ basic_expr		{ $$ = std::move($2); }	// TODO: restrict this
	| %empty		{ $$ = nullptr; }
	;

enum_var_list:
	enum_var
	| enum_var_list TOK_COMMA enum_var
	;

enum_var: TOK_ID {
		log_assert((bool)astbuf1);
		auto node = astbuf1->clone();
		node->str = *$1;
		SET_AST_NODE_LOC(node.get(), @1, @1);
		node->is_enum = true;
		ast_stack.back()->children.push_back(std::move(node));
	}
	;

enum_decl: enum_type enum_var_list TOK_SEMICOL		{  }
	;

//////////////////
// struct or union
//////////////////

struct_decl:
	attr struct_type {
		append_attr(astbuf2.get(), $1);
	} struct_var_list TOK_SEMICOL {
		(void)astbuf2.reset();
	}
	;

struct_type:
	struct_union {
		astbuf2 = std::move($1);
	} struct_body {
		$$ = astbuf2->clone();
	}
	;

struct_union:
	  TOK_STRUCT		{ $$ = std::make_unique<AstNode>(AST_STRUCT); }
	| TOK_UNION		{ $$ = std::make_unique<AstNode>(AST_UNION); }
	;

struct_body: opt_packed TOK_LCURL struct_member_list TOK_RCURL
	;

opt_packed:
	TOK_PACKED opt_signed_struct |
	%empty { frontend_verilog_yyerror("Only PACKED supported at this time"); };

opt_signed_struct:
	  TOK_SIGNED		{ astbuf2->is_signed = true; }
	| TOK_UNSIGNED		{ astbuf2->is_signed = false; }
	| %empty // default is unsigned
	;

struct_member_list: struct_member
	| struct_member_list struct_member
	;

struct_member: struct_member_type member_name_list TOK_SEMICOL		{ (void)astbuf1.reset(); }
	;

member_name_list:
	  member_name
	| member_name_list TOK_COMMA member_name
	;

member_name: TOK_ID {
		astbuf1->str = $1->substr(1);
		astbuf3 = astbuf1->clone();
		log_assert(!member_hack);
		member_hack = astbuf3.get();
		SET_AST_NODE_LOC(member_hack, @1, @1);
		astbuf2->children.push_back(std::move(astbuf3));
	} range {
		log_assert((bool)member_hack);
		if ($3) member_hack->children.push_back(std::move($3));
		member_hack = nullptr;
	}
	;

struct_member_type: { astbuf1 = std::make_unique<AstNode>(AST_STRUCT_ITEM); } member_type_token
	;

member_type_token:
	member_type range_or_multirange {
		auto range = checkRange(astbuf1.get(), std::move($2));
		if (range)
			astbuf1->children.push_back(std::move(range));
	}
	| {
		(void)astbuf1.reset();
	} struct_union {
			// stash state on ast_stack
			// sketchy!
			ast_stack.push_back(astbuf2.release());
			astbuf2 = std::move($2);
		} struct_body  {
			astbuf1 = std::move(astbuf2);
			// recover state
			astbuf2.reset(ast_stack.back());
			ast_stack.pop_back();
		}
	;

member_type: type_atom type_signing
	| type_vec type_signing
	| hierarchical_type_id { addWiretypeNode($1, astbuf1.get()); }
	;

struct_var_list: struct_var
	| struct_var_list TOK_COMMA struct_var
	;

struct_var:
	TOK_ID	{
		auto var_node = astbuf2->clone();
		var_node->str = *$1;
		SET_AST_NODE_LOC(var_node.get(), @1, @1);
		ast_stack.back()->children.push_back(std::move(var_node));
	};

/////////
// wire
/////////

wire_decl:
	attr wire_type range_or_multirange {
		albuf = $1;
		astbuf1 = std::move($2);
		astbuf2 = checkRange(astbuf1.get(), std::move($3));
	} delay wire_name_list {
		(void)astbuf1.reset();
		if (astbuf2 != nullptr)
			(void)astbuf2.reset();
		free_attr(albuf);
	} TOK_SEMICOL |
	attr TOK_SUPPLY0 TOK_ID {
		ast_stack.back()->children.push_back(std::make_unique<AstNode>(AST_WIRE));
		ast_stack.back()->children.back()->str = *$3;
		append_attr(ast_stack.back()->children.back().get(), $1);
		ast_stack.back()->children.push_back(std::make_unique<AstNode>(AST_ASSIGN, std::make_unique<AstNode>(AST_IDENTIFIER), AstNode::mkconst_int(0, false, 1)));
		ast_stack.back()->children.back()->children[0]->str = *$3;
	} opt_supply_wires TOK_SEMICOL |
	attr TOK_SUPPLY1 TOK_ID {
		ast_stack.back()->children.push_back(std::make_unique<AstNode>(AST_WIRE));
		ast_stack.back()->children.back()->str = *$3;
		append_attr(ast_stack.back()->children.back().get(), $1);
		ast_stack.back()->children.push_back(std::make_unique<AstNode>(AST_ASSIGN, std::make_unique<AstNode>(AST_IDENTIFIER), AstNode::mkconst_int(1, false, 1)));
		ast_stack.back()->children.back()->children[0]->str = *$3;
	} opt_supply_wires TOK_SEMICOL;

opt_supply_wires:
	%empty |
	opt_supply_wires TOK_COMMA TOK_ID {
		auto wire_node = ast_stack.back()->children.at(GetSize(ast_stack.back()->children)-2)->clone();
		auto assign_node = ast_stack.back()->children.at(GetSize(ast_stack.back()->children)-1)->clone();
		wire_node->str = *$3;
		assign_node->children[0]->str = *$3;
		ast_stack.back()->children.push_back(std::move(wire_node));
		ast_stack.back()->children.push_back(std::move(assign_node));
	};

wire_name_list:
	wire_name_and_opt_assign | wire_name_list TOK_COMMA wire_name_and_opt_assign;

wire_name_and_opt_assign:
	wire_name {
		bool attr_anyconst = false;
		bool attr_anyseq = false;
		bool attr_allconst = false;
		bool attr_allseq = false;
		if (ast_stack.back()->children.back()->get_bool_attribute(ID::anyconst)) {
			ast_stack.back()->children.back()->attributes.erase(ID::anyconst);
			attr_anyconst = true;
		}
		if (ast_stack.back()->children.back()->get_bool_attribute(ID::anyseq)) {
			ast_stack.back()->children.back()->attributes.erase(ID::anyseq);
			attr_anyseq = true;
		}
		if (ast_stack.back()->children.back()->get_bool_attribute(ID::allconst)) {
			ast_stack.back()->children.back()->attributes.erase(ID::allconst);
			attr_allconst = true;
		}
		if (ast_stack.back()->children.back()->get_bool_attribute(ID::allseq)) {
			ast_stack.back()->children.back()->attributes.erase(ID::allseq);
			attr_allseq = true;
		}
		if (current_wire_rand || attr_anyconst || attr_anyseq || attr_allconst || attr_allseq) {
			auto wire = std::make_unique<AstNode>(AST_IDENTIFIER);
			auto fcall = std::make_unique<AstNode>(AST_FCALL);
			wire->str = ast_stack.back()->children.back()->str;
			fcall->str = current_wire_const ? "\\$anyconst" : "\\$anyseq";
			if (attr_anyconst)
				fcall->str = "\\$anyconst";
			if (attr_anyseq)
				fcall->str = "\\$anyseq";
			if (attr_allconst)
				fcall->str = "\\$allconst";
			if (attr_allseq)
				fcall->str = "\\$allseq";
			fcall->attributes[ID::reg] = AstNode::mkconst_str(RTLIL::unescape_id(wire->str));
			ast_stack.back()->children.push_back(std::make_unique<AstNode>(AST_ASSIGN, std::move(wire), std::move(fcall)));
		}
	} |
	wire_name TOK_EQ expr {
		auto wire = std::make_unique<AstNode>(AST_IDENTIFIER);
		wire->str = ast_stack.back()->children.back()->str;
		if (astbuf1->is_input) {
			astbuf1->attributes[ID::defaultvalue] = std::move($3);
		}
		else if (astbuf1->is_reg || astbuf1->is_logic){
			auto assign = std::make_unique<AstNode>(AST_ASSIGN_LE, std::move(wire), std::move($3));
			SET_AST_NODE_LOC(assign.get(), @1, @3);
			auto block = std::make_unique<AstNode>(AST_BLOCK, std::move(assign));
			SET_AST_NODE_LOC(block.get(), @1, @3);
			auto init = std::make_unique<AstNode>(AST_INITIAL, std::move(block));
			SET_AST_NODE_LOC(init.get(), @1, @3);

			ast_stack.back()->children.push_back(std::move(init));
		}
		else {
			auto assign = std::make_unique<AstNode>(AST_ASSIGN, std::move(wire), std::move($3));
			SET_AST_NODE_LOC(assign.get(), @1, @3);
			ast_stack.back()->children.push_back(std::move(assign));
		}

	};

wire_name:
	TOK_ID range_or_multirange {
		if (astbuf1 == nullptr)
			frontend_verilog_yyerror("Internal error - should not happen - no AST_WIRE node.");
		auto node = astbuf1->clone();
		node->str = *$1;
		append_attr_clone(node.get(), albuf);
		if (astbuf2 != nullptr)
			node->children.push_back(astbuf2->clone());
		if ($2 != nullptr) {
			if (node->is_input || node->is_output)
				frontend_verilog_yyerror("input/output/inout ports cannot have unpacked dimensions.");
			if (!astbuf2 && !node->is_custom_type) {
				addRange(node.get(), 0, 0, false);
			}
			rewriteAsMemoryNode(node.get(), std::move($2));
		}
		if (current_function_or_task) {
			if (node->is_input || node->is_output)
				node->port_id = current_function_or_task_port_id++;
		} else if (ast_stack.back()->type == AST_GENBLOCK) {
			if (node->is_input || node->is_output)
				frontend_verilog_yyerror("Cannot declare module port `%s' within a generate block.", $1->c_str());
		} else {
			if (do_not_require_port_stubs && (node->is_input || node->is_output) && port_stubs.count(*$1) == 0) {
				port_stubs[*$1] = ++port_counter;
			}
			if (port_stubs.count(*$1) != 0) {
				if (!node->is_input && !node->is_output)
					frontend_verilog_yyerror("Module port `%s' is neither input nor output.", $1->c_str());
				if (node->is_reg && node->is_input && !node->is_output && !sv_mode)
					frontend_verilog_yyerror("Input port `%s' is declared as register.", $1->c_str());
				node->port_id = port_stubs[*$1];
				port_stubs.erase(*$1);
			} else {
				if (node->is_input || node->is_output)
					frontend_verilog_yyerror("Module port `%s' is not declared in module header.", $1->c_str());
			}
		}
		//FIXME: for some reason, TOK_ID has a location which always points to one column *after* the real last column...
		SET_AST_NODE_LOC(node.get(), @1, @1);
		ast_stack.back()->children.push_back(std::move(node));

	};

assign_stmt:
	TOK_ASSIGN delay assign_expr_list TOK_SEMICOL;

assign_expr_list:
	assign_expr | assign_expr_list TOK_COMMA assign_expr;

assign_expr:
	lvalue TOK_EQ expr {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_ASSIGN, std::move($1), std::move($3)));
		SET_AST_NODE_LOC(node, @$, @$);
	};

type_name: TOK_ID		// first time seen
	 | TOK_USER_TYPE	{ if (isInLocalScope($1)) frontend_verilog_yyerror("Duplicate declaration of TYPEDEF '%s'", $1->c_str()+1); $$ = std::move($1); }
	 ;

typedef_decl:
	TOK_TYPEDEF typedef_base_type range_or_multirange type_name range_or_multirange TOK_SEMICOL {
		astbuf1 = std::move($2);
		astbuf2 = checkRange(astbuf1.get(), std::move($3));
		bool has_a_range = (bool)astbuf2;
		if (astbuf2) {
			astbuf1->children.push_back(std::move(astbuf2));
		}

		if ($5 != nullptr) {
			if (!has_a_range && !astbuf1->is_custom_type) {
				addRange(astbuf1.get(), 0, 0, false);
			}
			rewriteAsMemoryNode(astbuf1.get(), std::move($5));
		}
		addTypedefNode($4, std::move(astbuf1)); }
	| TOK_TYPEDEF enum_struct_type type_name TOK_SEMICOL   { addTypedefNode($3, std::move($2)); }
	;

typedef_base_type:
	hierarchical_type_id {
		$$ = std::make_unique<AstNode>(AST_WIRE);
		$$->is_logic = true;
		addWiretypeNode($1, $$.get());
	} |
	integer_vector_type opt_signedness_default_unsigned {
		$$ = std::make_unique<AstNode>(AST_WIRE);
		if ($1 == token::TOK_REG) {
			$$->is_reg = true;
		} else {
			$$->is_logic = true;
		}
		$$->is_signed = $2;
	} |
	integer_atom_type opt_signedness_default_signed {
		$$ = std::make_unique<AstNode>(AST_WIRE);
		$$->is_logic = true;
		$$->is_signed = $2;
		$$->range_left = $1 - 1;
		$$->range_right = 0;
	};

enum_struct_type:
	  enum_type { $$ = std::move($1); }
	| struct_type { $$ = std::move($1); }
	;

cell_stmt:
	attr TOK_ID {
		astbuf1 = std::make_unique<AstNode>(AST_CELL);
		append_attr(astbuf1.get(), $1);
		astbuf1->children.push_back(std::make_unique<AstNode>(AST_CELLTYPE));
		astbuf1->children[0]->str = *$2;
	} cell_parameter_list_opt cell_list TOK_SEMICOL {
		(void)astbuf1.reset();
	} |
	attr tok_prim_wrapper delay {
		astbuf1 = std::make_unique<AstNode>(AST_PRIMITIVE);
		astbuf1->str = *$2;
		append_attr(astbuf1.get(), $1);
	} prim_list TOK_SEMICOL {
		(void)astbuf1.reset();
	};

tok_prim_wrapper:
	TOK_PRIMITIVE {
		$$ = $1;
	} |
	TOK_OR {
		$$ = new std::string("or");
	};

cell_list:
	single_cell |
	cell_list TOK_COMMA single_cell;

single_cell:
	single_cell_no_array | single_cell_arraylist;

single_cell_no_array:
	TOK_ID {
		astbuf2 = astbuf1->clone();
		if (astbuf2->type != AST_PRIMITIVE)
			astbuf2->str = *$1;
		// TODO optimize again
		cell_hack = astbuf2.get();
		ast_stack.back()->children.push_back(std::move(astbuf2));
	} TOK_LPAREN cell_port_list TOK_RPAREN {
		log_assert(cell_hack);
		SET_AST_NODE_LOC(cell_hack, @1, @$);
		cell_hack = nullptr;
	}

single_cell_arraylist:
	TOK_ID non_opt_range {
		astbuf2 = astbuf1->clone();
		if (astbuf2->type != AST_PRIMITIVE)
			astbuf2->str = *$1;
		// TODO optimize again
		cell_hack = astbuf2.get();
		ast_stack.back()->children.push_back(std::make_unique<AstNode>(AST_CELLARRAY, std::move($2), std::move(astbuf2)));
	} TOK_LPAREN cell_port_list TOK_RPAREN{
		log_assert(cell_hack);
		SET_AST_NODE_LOC(cell_hack, @1, @$);
		cell_hack = nullptr;
	};

cell_list_no_array:
	single_cell_no_array |
	cell_list_no_array TOK_COMMA single_cell_no_array;

prim_list:
	single_prim |
	prim_list TOK_COMMA single_prim;

single_prim:
	single_cell |
	/* no name */ {
		astbuf2 = astbuf1->clone();
		log_assert(!cell_hack);
		cell_hack = astbuf2.get();
		// TODO optimize again
		ast_stack.back()->children.push_back(std::move(astbuf2));
	} TOK_LPAREN cell_port_list TOK_RPAREN {
		log_assert(cell_hack);
		SET_AST_NODE_LOC(cell_hack, @1, @$);
		cell_hack = nullptr;
	}

cell_parameter_list_opt:
	TOK_HASH TOK_LPAREN cell_parameter_list TOK_RPAREN | %empty;

cell_parameter_list:
	cell_parameter | cell_parameter_list TOK_COMMA cell_parameter;

cell_parameter:
	%empty |
	expr {
		auto node = std::make_unique<AstNode>(AST_PARASET);
		node->children.push_back(std::move($1));
		astbuf1->children.push_back(std::move(node));
	} |
	TOK_DOT TOK_ID TOK_LPAREN TOK_RPAREN {
		// just ignore empty parameters
	} |
	TOK_DOT TOK_ID TOK_LPAREN expr TOK_RPAREN {
		auto node = std::make_unique<AstNode>(AST_PARASET);
		node->str = *$2;
		node->children.push_back(std::move($4));
		astbuf1->children.push_back(std::move(node));
	};

cell_port_list:
	cell_port_list_rules {
		// remove empty args from end of list
		while (!cell_hack->children.empty()) {
			auto& node = cell_hack->children.back();
			if (node->type != AST_ARGUMENT) break;
			if (!node->children.empty()) break;
			if (!node->str.empty()) break;
			cell_hack->children.pop_back();
		}

		// check port types
		bool has_positional_args = false;
		bool has_named_args = false;
		for (auto& node : cell_hack->children) {
			if (node->type != AST_ARGUMENT) continue;
			if (node->str.empty())
				has_positional_args = true;
			else
				has_named_args = true;
		}

		if (has_positional_args && has_named_args)
			frontend_verilog_yyerror("Mix of positional and named cell ports.");
	};

cell_port_list_rules:
	cell_port | cell_port_list_rules TOK_COMMA cell_port;

cell_port:
	attr {
		auto node = std::make_unique<AstNode>(AST_ARGUMENT);
		cell_hack->children.push_back(std::move(node));
		free_attr($1);
	} |
	attr expr {
		auto node = std::make_unique<AstNode>(AST_ARGUMENT);
		node->children.push_back(std::move($2));
		cell_hack->children.push_back(std::move(node));
		free_attr($1);
	} |
	attr TOK_DOT TOK_ID TOK_LPAREN expr TOK_RPAREN {
		auto node = std::make_unique<AstNode>(AST_ARGUMENT);
		node->str = *$3;
		node->children.push_back(std::move($5));
		cell_hack->children.push_back(std::move(node));
		free_attr($1);
	} |
	attr TOK_DOT TOK_ID TOK_LPAREN TOK_RPAREN {
		auto node = std::make_unique<AstNode>(AST_ARGUMENT);
		node->str = *$3;
		cell_hack->children.push_back(std::move(node));
		free_attr($1);
	} |
	attr TOK_DOT TOK_ID {
		auto node = std::make_unique<AstNode>(AST_ARGUMENT);
		node->str = *$3;
		node->children.push_back(std::make_unique<AstNode>(AST_IDENTIFIER));
		node->children.back()->str = *$3;
		cell_hack->children.push_back(std::move(node));
		free_attr($1);
	} |
	attr TOK_WILDCARD_CONNECT {
		if (!sv_mode)
			frontend_verilog_yyerror("Wildcard port connections are only supported in SystemVerilog mode.");
		cell_hack->attributes[ID::wildcard_port_conns] = AstNode::mkconst_int(1, false);
		free_attr($1);
	};

always_comb_or_latch:
	TOK_ALWAYS_COMB {
		$$ = false;
	} |
	TOK_ALWAYS_LATCH {
		$$ = true;
	};

always_or_always_ff:
	TOK_ALWAYS {
		$$ = false;
	} |
	TOK_ALWAYS_FF {
		$$ = true;
	};

always_stmt:
	attr always_or_always_ff {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_ALWAYS));
		append_attr(node, $1);
		if ($2)
			node->attributes[ID::always_ff] = AstNode::mkconst_int(1, false);
	} always_cond {
		(void)pushChild(std::make_unique<AstNode>(AST_BLOCK));
	} behavioral_stmt {
		SET_AST_NODE_LOC(ast_stack.back(), @6, @6);
		ast_stack.pop_back();

		SET_AST_NODE_LOC(ast_stack.back(), @2, @$);
		ast_stack.pop_back();

		SET_RULE_LOC(@$, @2, @$);
	} |
	attr always_comb_or_latch {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_ALWAYS));
		append_attr(node, $1);
		if ($2)
			node->attributes[ID::always_latch] = AstNode::mkconst_int(1, false);
		else
			node->attributes[ID::always_comb] = AstNode::mkconst_int(1, false);
		(void)pushChild(std::make_unique<AstNode>(AST_BLOCK));
	} behavioral_stmt {
		ast_stack.pop_back();
		ast_stack.pop_back();
	} |
	attr TOK_INITIAL {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_INITIAL));
		append_attr(node, $1);
		(void)pushChild(std::make_unique<AstNode>(AST_BLOCK));
	} behavioral_stmt {
		ast_stack.pop_back();
		ast_stack.pop_back();
	};

always_cond:
	TOK_AT TOK_LPAREN always_events TOK_RPAREN |
	TOK_AT TOK_LPAREN TOK_ASTER TOK_RPAREN |
	TOK_AT ATTR_BEGIN TOK_RPAREN |
	TOK_AT TOK_LPAREN ATTR_END |
	TOK_AT TOK_ASTER |
	%empty;

always_events:
	always_event |
	always_events TOK_OR always_event |
	always_events TOK_COMMA always_event;

always_event:
	TOK_POSEDGE expr {
		auto node = std::make_unique<AstNode>(AST_POSEDGE);
		SET_AST_NODE_LOC(node.get(), @1, @1);
		node->children.push_back(std::move($2));
		ast_stack.back()->children.push_back(std::move(node));
	} |
	TOK_NEGEDGE expr {
		auto node = std::make_unique<AstNode>(AST_NEGEDGE);
		SET_AST_NODE_LOC(node.get(), @1, @1);
		node->children.push_back(std::move($2));
		ast_stack.back()->children.push_back(std::move(node));
	} |
	expr {
		auto node = std::make_unique<AstNode>(AST_EDGE);
		node->children.push_back(std::move($1));
		ast_stack.back()->children.push_back(std::move(node));
	};

opt_label:
	TOK_COL TOK_ID {
		$$ = $2;
	} |
	%empty {
		$$ = nullptr;
	};

opt_sva_label:
	TOK_SVA_LABEL TOK_COL {
		$$ = $1;
	} |
	%empty {
		$$ = nullptr;
	};

opt_property:
	TOK_PROPERTY {
		$$ = true;
	} |
	TOK_FINAL {
		$$ = false;
	} |
	%empty {
		$$ = false;
	};

modport_stmt:
    TOK_MODPORT TOK_ID {
		AstNode* modport = pushChild(std::make_unique<AstNode>(AST_MODPORT));
        modport->str = *$2;
        
    }  modport_args_opt {
        ast_stack.pop_back();
        log_assert(ast_stack.size() == 2);
    } TOK_SEMICOL

modport_args_opt:
    TOK_LPAREN TOK_RPAREN | TOK_LPAREN modport_args optional_comma TOK_RPAREN;

modport_args:
    modport_arg | modport_args TOK_COMMA modport_arg;

modport_arg:
    modport_type_token modport_member |
    modport_member

modport_member:
    TOK_ID {
		AstNode* modport_member = saveChild(std::make_unique<AstNode>(AST_MODPORTMEMBER));
        modport_member->str = *$1;
        modport_member->is_input = current_modport_input;
        modport_member->is_output = current_modport_output;
        
    }

modport_type_token:
    TOK_INPUT {current_modport_input = 1; current_modport_output = 0;} | TOK_OUTPUT {current_modport_input = 0; current_modport_output = 1;}

assert:
	opt_sva_label TOK_ASSERT opt_property TOK_LPAREN expr TOK_RPAREN TOK_SEMICOL {
		if (noassert_mode) {
			
		} else {
			AstNode* node = saveChild(std::make_unique<AstNode>(assume_asserts_mode ? AST_ASSUME : AST_ASSERT, std::move($5)));
			SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @6);
			if ($1 != nullptr)
				node->str = *$1;
		}
	} |
	opt_sva_label TOK_ASSUME opt_property TOK_LPAREN expr TOK_RPAREN TOK_SEMICOL {
		if (noassume_mode) {
		} else {
			AstNode* node = saveChild(std::make_unique<AstNode>(assert_assumes_mode ? AST_ASSERT : AST_ASSUME, std::move($5)));
			SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @6);
			if ($1 != nullptr)
				node->str = *$1;
		}
	} |
	opt_sva_label TOK_ASSERT opt_property TOK_LPAREN TOK_EVENTUALLY expr TOK_RPAREN TOK_SEMICOL {
		if (noassert_mode) {
		} else {
			AstNode* node = saveChild(std::make_unique<AstNode>(assume_asserts_mode ? AST_FAIR : AST_LIVE, std::move($6)));
			SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @7);
			if ($1 != nullptr)
				node->str = *$1;
		}
	} |
	opt_sva_label TOK_ASSUME opt_property TOK_LPAREN TOK_EVENTUALLY expr TOK_RPAREN TOK_SEMICOL {
		if (noassume_mode) {
		} else {
			AstNode* node = saveChild(std::make_unique<AstNode>(assert_assumes_mode ? AST_LIVE : AST_FAIR, std::move($6)));
			SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @7);
			if ($1 != nullptr)
				node->str = *$1;
		}
	} |
	opt_sva_label TOK_COVER opt_property TOK_LPAREN expr TOK_RPAREN TOK_SEMICOL {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_COVER, std::move($5)));
		SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @6);
		if ($1 != nullptr) {
			node->str = *$1;
		}
	} |
	opt_sva_label TOK_COVER opt_property TOK_LPAREN TOK_RPAREN TOK_SEMICOL {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_COVER, AstNode::mkconst_int(1, false)));
		SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @5);
		if ($1 != nullptr) {
			node->str = *$1;
		}
	} |
	opt_sva_label TOK_COVER TOK_SEMICOL {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_COVER, AstNode::mkconst_int(1, false)));
		SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @2);
		if ($1 != nullptr) {
			node->str = *$1;
		}
	} |
	opt_sva_label TOK_RESTRICT opt_property TOK_LPAREN expr TOK_RPAREN TOK_SEMICOL {
		if (norestrict_mode) {
		} else {
			AstNode* node = saveChild(std::make_unique<AstNode>(AST_ASSUME, std::move($5)));
			SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @6);
			if ($1 != nullptr)
				node->str = *$1;
		}
		if (!$3)
			log_file_warning(current_filename, @$.begin.line, "SystemVerilog does not allow \"restrict\" without \"property\".\n");
	} |
	opt_sva_label TOK_RESTRICT opt_property TOK_LPAREN TOK_EVENTUALLY expr TOK_RPAREN TOK_SEMICOL {
		if (norestrict_mode) {
		} else {
			AstNode* node = saveChild(std::make_unique<AstNode>(AST_FAIR, std::move($6)));
			SET_AST_NODE_LOC(node, ($1 != nullptr ? @1 : @2), @7);
			if ($1 != nullptr)
				node->str = *$1;
		}
		if (!$3)
			log_file_warning(current_filename, @$.begin.line, "SystemVerilog does not allow \"restrict\" without \"property\".\n");
	};

assert_property:
	opt_sva_label TOK_ASSERT TOK_PROPERTY TOK_LPAREN expr TOK_RPAREN TOK_SEMICOL {
		AstNode* node = saveChild(std::make_unique<AstNode>(assume_asserts_mode ? AST_ASSUME : AST_ASSERT, std::move($5)));
		SET_AST_NODE_LOC(node, @1, @6);
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
		}
	} |
	opt_sva_label TOK_ASSUME TOK_PROPERTY TOK_LPAREN expr TOK_RPAREN TOK_SEMICOL {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_ASSUME, std::move($5)));
		SET_AST_NODE_LOC(node, @1, @6);
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
		}
	} |
	opt_sva_label TOK_ASSERT TOK_PROPERTY TOK_LPAREN TOK_EVENTUALLY expr TOK_RPAREN TOK_SEMICOL {
		AstNode* node = saveChild(std::make_unique<AstNode>(assume_asserts_mode ? AST_FAIR : AST_LIVE, std::move($6)));
		SET_AST_NODE_LOC(node, @1, @7);
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
		}
	} |
	opt_sva_label TOK_ASSUME TOK_PROPERTY TOK_LPAREN TOK_EVENTUALLY expr TOK_RPAREN TOK_SEMICOL {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_FAIR, std::move($6)));
		SET_AST_NODE_LOC(node, @1, @7);
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
		}
	} |
	opt_sva_label TOK_COVER TOK_PROPERTY TOK_LPAREN expr TOK_RPAREN TOK_SEMICOL {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_COVER, std::move($5)));
		SET_AST_NODE_LOC(node, @1, @6);
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
		}
	} |
	opt_sva_label TOK_RESTRICT TOK_PROPERTY TOK_LPAREN expr TOK_RPAREN TOK_SEMICOL {
		if (norestrict_mode) {
		} else {
			AstNode* node = saveChild(std::make_unique<AstNode>(AST_ASSUME, std::move($5)));
			SET_AST_NODE_LOC(node, @1, @6);
			if ($1 != nullptr) {
				ast_stack.back()->children.back()->str = *$1;
			}
		}
	} |
	opt_sva_label TOK_RESTRICT TOK_PROPERTY TOK_LPAREN TOK_EVENTUALLY expr TOK_RPAREN TOK_SEMICOL {
		if (norestrict_mode) {
		} else {
			AstNode* node = saveChild(std::make_unique<AstNode>(AST_FAIR, std::move($6)));
			SET_AST_NODE_LOC(node, @1, @7);
			if ($1 != nullptr) {
				ast_stack.back()->children.back()->str = *$1;
			}
		}
	};

simple_behavioral_stmt:
	attr lvalue TOK_EQ delay expr {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_ASSIGN_EQ, std::move($2), std::move($5)));
		SET_AST_NODE_LOC(node, @2, @5);
		append_attr(node, $1);
	} |
	attr lvalue attr inc_or_dec_op {
		addIncOrDecStmt($1, std::move($2), $3, $4, @1, @4);
	} |
	attr inc_or_dec_op attr lvalue {
		addIncOrDecStmt($1, std::move($4), $3, $2, @1, @4);
	} |
	attr lvalue OP_LE delay expr {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_ASSIGN_LE, std::move($2), std::move($5)));
		SET_AST_NODE_LOC(node, @2, @5);
		append_attr(node, $1);
	} |
	attr lvalue asgn_binop delay expr {
		(void)addAsgnBinopStmt($1, std::move($2), $3, std::move($5), @2, @5);
	};

asgn_binop:
	TOK_BIT_OR_ASSIGN { $$ = AST_BIT_OR; } |
	TOK_BIT_AND_ASSIGN { $$ = AST_BIT_AND; } |
	TOK_BIT_XOR_ASSIGN { $$ = AST_BIT_XOR; } |
	TOK_ADD_ASSIGN { $$ = AST_ADD; } |
	TOK_SUB_ASSIGN { $$ = AST_SUB; } |
	TOK_DIV_ASSIGN { $$ = AST_DIV; } |
	TOK_MOD_ASSIGN { $$ = AST_MOD; } |
	TOK_MUL_ASSIGN { $$ = AST_MUL; } |
	TOK_SHL_ASSIGN { $$ = AST_SHIFT_LEFT; } |
	TOK_SHR_ASSIGN { $$ = AST_SHIFT_RIGHT; } |
	TOK_SSHL_ASSIGN { $$ = AST_SHIFT_SLEFT; } |
	TOK_SSHR_ASSIGN { $$ = AST_SHIFT_SRIGHT; } ;

inc_or_dec_op:
	// NOTE: These should only be permitted in SV mode, but Yosys has
	// allowed them in all modes since support for them was added in 2017.
	TOK_INCREMENT { $$ = AST_ADD; } |
	TOK_DECREMENT { $$ = AST_SUB; } ;

for_initialization:
	TOK_ID TOK_EQ expr {
		auto ident = std::make_unique<AstNode>(AST_IDENTIFIER);
		ident->str = *$1;
		auto node = std::make_unique<AstNode>(AST_ASSIGN_EQ, std::move(ident), std::move($3));
		SET_AST_NODE_LOC(node.get(), @1, @3);
		ast_stack.back()->children.push_back(std::move(node));
	} |
	non_io_wire_type range TOK_ID {
		frontend_verilog_yyerror("For loop variable declaration is missing initialization!");
	} |
	non_io_wire_type range TOK_ID TOK_EQ expr {
		if (!sv_mode)
			frontend_verilog_yyerror("For loop inline variable declaration is only supported in SystemVerilog mode!");

		// loop variable declaration
		auto wire = std::move($1);
		auto range = checkRange(wire.get(), std::move($2));
		SET_AST_NODE_LOC(wire.get(), @1, @3);
		SET_AST_NODE_LOC(range.get(), @2, @2);
		if (range != nullptr)
			wire->children.push_back(std::move(range));

		auto ident = std::make_unique<AstNode>(AST_IDENTIFIER);
		ident->str = *$3;
		wire->str = *$3;

		AstNode *parent = ast_stack.at(ast_stack.size() - 2);
		auto& loop = parent->children.back();
		log_assert(ast_stack.back() == loop.get());

		// loop variable initialization
		SET_AST_NODE_LOC(ident.get(), @3, @3);
		auto asgn = std::make_unique<AstNode>(AST_ASSIGN_EQ, std::move(ident), std::move($5));
		SET_AST_NODE_LOC(asgn.get(), @3, @5);
		loop->children.push_back(std::move(asgn));

		// inject a wrapping block to declare the loop variable and
		// contain the current loop
		auto wrapper = std::make_unique<AstNode>(AST_BLOCK);
		wrapper->str = "$fordecl_block$" + std::to_string(autoidx++);
		wrapper->children.push_back(std::move(wire));
		wrapper->children.push_back(std::move(loop));
		parent->children.back() = std::move(wrapper);
	};

// this production creates the obligatory if-else shift/reduce conflict
behavioral_stmt:
	defattr | assert | wire_decl | param_decl | localparam_decl | typedef_decl |
	non_opt_delay behavioral_stmt |
	simple_behavioral_stmt TOK_SEMICOL |
	attr TOK_SEMICOL {
		free_attr($1);
	} |
	attr hierarchical_id {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_TCALL));
		node->str = *$2;
		append_attr(node, $1);
	} opt_arg_list TOK_SEMICOL{
		SET_AST_NODE_LOC(ast_stack.back(), @2, @5);
		ast_stack.pop_back();
	} |
	attr TOK_MSG_TASKS {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_TCALL));
		node->str = *$2;
		append_attr(node, $1);
	} opt_arg_list TOK_SEMICOL{
		SET_AST_NODE_LOC(ast_stack.back(), @2, @5);
		ast_stack.pop_back();
	} |
	attr TOK_BEGIN {
		enterTypeScope();
	} opt_label {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_BLOCK));
		append_attr(node, $1);
		if ($4 != nullptr)
			node->str = *$4;
	} behavioral_stmt_list TOK_END opt_label {
		exitTypeScope();
		checkLabelsMatch("Begin label", $4, $8);
		AstNode *node = ast_stack.back();
		// In SystemVerilog, unnamed blocks with block item declarations
		// create an implicit hierarchy scope
		if (sv_mode && node->str.empty())
		    for (auto& child : node->children)
			if (child->type == AST_WIRE || child->type == AST_MEMORY || child->type == AST_PARAMETER
				|| child->type == AST_LOCALPARAM || child->type == AST_TYPEDEF) {
			    node->str = "$unnamed_block$" + std::to_string(autoidx++);
			    break;
			}
		SET_AST_NODE_LOC(ast_stack.back(), @2, @8);
		ast_stack.pop_back();
	} |
	attr TOK_FOR TOK_LPAREN {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_FOR));
		append_attr(node, $1);
	} for_initialization TOK_SEMICOL expr {
		ast_stack.back()->children.push_back(std::move($7));
	} TOK_SEMICOL simple_behavioral_stmt TOK_RPAREN {
		AstNode* block = pushChild(std::make_unique<AstNode>(AST_BLOCK));
		block->str = "$for_loop$" + std::to_string(autoidx++);
	} behavioral_stmt {
		SET_AST_NODE_LOC(ast_stack.back(), @13, @13);
		ast_stack.pop_back();
		SET_AST_NODE_LOC(ast_stack.back(), @2, @13);
		ast_stack.pop_back();
	} |
	attr TOK_WHILE TOK_LPAREN expr TOK_RPAREN {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_WHILE));
		append_attr(node, $1);
		auto block_owned = std::make_unique<AstNode>(AST_BLOCK);
		auto* block = block_owned.get();
		ast_stack.back()->children.push_back(std::move($4));
		ast_stack.back()->children.push_back(std::move(block_owned));
		ast_stack.push_back(block);
	} behavioral_stmt {
		SET_AST_NODE_LOC(ast_stack.back(), @7, @7);
		ast_stack.pop_back();
		ast_stack.pop_back();
	} |
	attr TOK_REPEAT TOK_LPAREN expr TOK_RPAREN {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_REPEAT));
		append_attr(node, $1);
		auto block_owned = std::make_unique<AstNode>(AST_BLOCK);
		auto* block = block_owned.get();
		ast_stack.back()->children.push_back(std::move($4));
		ast_stack.back()->children.push_back(std::move(block_owned));
		ast_stack.push_back(block);
	} behavioral_stmt {
		SET_AST_NODE_LOC(ast_stack.back(), @7, @7);
		ast_stack.pop_back();
		ast_stack.pop_back();
	} |
	attr TOK_IF TOK_LPAREN expr TOK_RPAREN {
		auto node_owned = std::make_unique<AstNode>(AST_CASE);
		auto* node = node_owned.get();
		auto block_owned = std::make_unique<AstNode>(AST_BLOCK);
		auto* block = block_owned.get();
		auto cond_owned = std::make_unique<AstNode>(AST_COND, AstNode::mkconst_int(1, false, 1), std::move(block_owned));
		SET_AST_NODE_LOC(cond_owned.get(), @4, @4);
		ast_stack.back()->children.push_back(std::move(node_owned));
		node->children.push_back(std::make_unique<AstNode>(AST_REDUCE_BOOL, std::move($4)));
		node->children.push_back(std::move(cond_owned));
		ast_stack.push_back(node);
		ast_stack.push_back(block);
		append_attr(node, $1);
	} behavioral_stmt {
		SET_AST_NODE_LOC(ast_stack.back(), @7, @7);
	} optional_else {
		ast_stack.pop_back();
		SET_AST_NODE_LOC(ast_stack.back(), @2, @9);
		ast_stack.pop_back();
	} |
	case_attr case_type TOK_LPAREN expr TOK_RPAREN {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_CASE, std::move($4)));
		append_attr(node, $1);
		SET_AST_NODE_LOC(ast_stack.back(), @4, @4);
	} opt_synopsys_attr case_body TOK_ENDCASE {
		SET_AST_NODE_LOC(ast_stack.back(), @2, @9);
		case_type_stack.pop_back();
		ast_stack.pop_back();
	};

case_attr:
	attr {
		$$ = $1;
	} |
	attr TOK_UNIQUE0 {
		(*$1)[ID::parallel_case] = AstNode::mkconst_int(1, false);
		$$ = $1;
	} |
	attr TOK_PRIORITY {
		(*$1)[ID::full_case] = AstNode::mkconst_int(1, false);
		$$ = $1;
	} |
	attr TOK_UNIQUE {
		(*$1)[ID::full_case] = AstNode::mkconst_int(1, false);
		(*$1)[ID::parallel_case] = AstNode::mkconst_int(1, false);
		$$ = $1;
	};

case_type:
	TOK_CASE {
		case_type_stack.push_back(0);
	} |
	TOK_CASEX {
		case_type_stack.push_back('x');
	} |
	TOK_CASEZ {
		case_type_stack.push_back('z');
	};

opt_synopsys_attr:
	opt_synopsys_attr TOK_SYNOPSYS_FULL_CASE {
		if (ast_stack.back()->attributes.count(ID::full_case) == 0)
			ast_stack.back()->attributes[ID::full_case] = AstNode::mkconst_int(1, false);
	} |
	opt_synopsys_attr TOK_SYNOPSYS_PARALLEL_CASE {
		if (ast_stack.back()->attributes.count(ID::parallel_case) == 0)
			ast_stack.back()->attributes[ID::parallel_case] = AstNode::mkconst_int(1, false);
	} |
	%empty;

behavioral_stmt_list:
	behavioral_stmt_list behavioral_stmt |
	%empty;

optional_else:
	TOK_ELSE {
		ast_stack.pop_back();
		auto block_owned = std::make_unique<AstNode>(AST_BLOCK);
		auto* block = block_owned.get();
		AstNode* cond = saveChild(
			std::make_unique<AstNode>(AST_COND,
				std::make_unique<AstNode>(AST_DEFAULT),
				std::move(block_owned)));
		ast_stack.push_back(block);
		SET_AST_NODE_LOC(cond, @1, @1);
	} behavioral_stmt {
		SET_AST_NODE_LOC(ast_stack.back(), @3, @3);
	} |
	%empty %prec FAKE_THEN;

case_body:
	case_body case_item |
	%empty;

case_item:
	{
		(void)pushChild(std::make_unique<AstNode>(
				case_type_stack.size() && case_type_stack.back() == 'x' ? AST_CONDX :
				case_type_stack.size() && case_type_stack.back() == 'z' ? AST_CONDZ : AST_COND));
	} case_select {
		(void)pushChild(std::make_unique<AstNode>(AST_BLOCK));
		case_type_stack.push_back(0);
	} behavioral_stmt {
		case_type_stack.pop_back();
		SET_AST_NODE_LOC(ast_stack.back(), @4, @4);
		ast_stack.pop_back();
		ast_stack.pop_back();
	};

gen_case_body:
	gen_case_body gen_case_item |
	%empty;

gen_case_item:
	{
		(void)pushChild(std::make_unique<AstNode>(
				case_type_stack.size() && case_type_stack.back() == 'x' ? AST_CONDX :
				case_type_stack.size() && case_type_stack.back() == 'z' ? AST_CONDZ : AST_COND));
	} case_select {
		case_type_stack.push_back(0);
		SET_AST_NODE_LOC(ast_stack.back(), @2, @2);
	} gen_stmt_block {
		case_type_stack.pop_back();
		ast_stack.pop_back();
	};

case_select:
	case_expr_list TOK_COL |
	TOK_DEFAULT;

case_expr_list:
	TOK_DEFAULT {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_DEFAULT));
		SET_AST_NODE_LOC(node, @1, @1);
	} |
	TOK_SVA_LABEL {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_IDENTIFIER));
		SET_AST_NODE_LOC(node, @1, @1);
	} |
	expr {
		ast_stack.back()->children.push_back(std::move($1));
	} |
	case_expr_list TOK_COMMA expr {
		ast_stack.back()->children.push_back(std::move($3));
	};

rvalue:
	hierarchical_id TOK_LBRA expr TOK_RBRA TOK_DOT rvalue {
		$$ = std::make_unique<AstNode>(AST_PREFIX, std::move($3), std::move($6));
		$$->str = *$1;
		SET_AST_NODE_LOC($$.get(), @1, @6);
	} |
	hierarchical_id range {
		$$ = std::make_unique<AstNode>(AST_IDENTIFIER, std::move($2));
		$$->str = *$1;
		SET_AST_NODE_LOC($$.get(), @1, @1);
		if ($2 == nullptr && ($$->str == "\\$initstate" ||
				$$->str == "\\$anyconst" || $$->str == "\\$anyseq" ||
				$$->str == "\\$allconst" || $$->str == "\\$allseq"))
			$$->type = AST_FCALL;
	} |
	hierarchical_id non_opt_multirange {
		$$ = std::make_unique<AstNode>(AST_IDENTIFIER, std::move($2));
		$$->str = *$1;
		SET_AST_NODE_LOC($$.get(), @1, @1);
	};

lvalue:
	rvalue {
		$$ = std::move($1);
	} |
	TOK_LCURL lvalue_concat_list TOK_RCURL {
		$$ = std::move($2);
	};

lvalue_concat_list:
	expr {
		$$ = std::make_unique<AstNode>(AST_CONCAT);
		$$->children.push_back(std::move($1));
	} |
	expr TOK_COMMA lvalue_concat_list {
		$$ = std::move($3);
		$$->children.push_back(std::move($1));
	};

opt_arg_list:
	TOK_LPAREN arg_list optional_comma TOK_RPAREN |
	%empty;

arg_list:
	arg_list2 |
	%empty;

arg_list2:
	single_arg |
	arg_list TOK_COMMA single_arg;

single_arg:
	expr {
		ast_stack.back()->children.push_back(std::move($1));
	};

module_gen_body:
	module_gen_body gen_stmt_or_module_body_stmt |
	module_gen_body gen_block |
	%empty;

gen_stmt_or_module_body_stmt:
	gen_stmt | module_body_stmt |
	attr TOK_SEMICOL {
		free_attr($1);
	};

genvar_identifier:
	TOK_ID {
		$$ = std::make_unique<AstNode>(AST_IDENTIFIER);
		$$->str = *$1;
	};

genvar_initialization:
	TOK_GENVAR genvar_identifier {
		frontend_verilog_yyerror("Generate for loop variable declaration is missing initialization!");
	} |
	TOK_GENVAR genvar_identifier TOK_EQ expr {
		if (!sv_mode)
			frontend_verilog_yyerror("Generate for loop inline variable declaration is only supported in SystemVerilog mode!");
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_GENVAR));
		node->is_reg = true;
		node->is_signed = true;
		node->range_left = 31;
		node->range_right = 0;
		node->str = $2->str;
		node->children.push_back(checkRange(node, nullptr));
		SET_AST_NODE_LOC(node, @1, @4);
		node = saveChild(std::make_unique<AstNode>(AST_ASSIGN_EQ, std::move($2), std::move($4)));
		SET_AST_NODE_LOC(node, @1, @4);
	} |
	genvar_identifier TOK_EQ expr {
		AstNode* node = saveChild(std::make_unique<AstNode>(AST_ASSIGN_EQ, std::move($1), std::move($3)));
		SET_AST_NODE_LOC(node, @1, @3);
	};

// this production creates the obligatory if-else shift/reduce conflict
gen_stmt:
	TOK_FOR TOK_LPAREN {
		(void)pushChild(std::make_unique<AstNode>(AST_GENFOR));
	} genvar_initialization TOK_SEMICOL expr {
		ast_stack.back()->children.push_back(std::move($6));
	} TOK_SEMICOL simple_behavioral_stmt TOK_RPAREN gen_stmt_block {
		SET_AST_NODE_LOC(ast_stack.back(), @1, @11);
		rewriteGenForDeclInit(ast_stack.back());
		ast_stack.pop_back();
	} |
	TOK_IF TOK_LPAREN expr TOK_RPAREN {
		(void)pushChild(std::make_unique<AstNode>(AST_GENIF));
		ast_stack.back()->children.push_back(std::move($3));
	} gen_stmt_block opt_gen_else {
		SET_AST_NODE_LOC(ast_stack.back(), @1, @7);
		ast_stack.pop_back();
	} |
	case_type TOK_LPAREN expr TOK_RPAREN {
		(void)pushChild(std::make_unique<AstNode>(AST_GENCASE, std::move($3)));
	} gen_case_body TOK_ENDCASE {
		case_type_stack.pop_back();
		SET_AST_NODE_LOC(ast_stack.back(), @1, @7);
		ast_stack.pop_back();
	} |
	TOK_MSG_TASKS {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_TECALL));
		node->str = *$1;
	} opt_arg_list TOK_SEMICOL{
		SET_AST_NODE_LOC(ast_stack.back(), @1, @3);
		ast_stack.pop_back();
	};

gen_block:
	TOK_BEGIN {
		enterTypeScope();
	} opt_label {
		AstNode* node = pushChild(std::make_unique<AstNode>(AST_GENBLOCK));
		node->str = $3 ? *$3 : std::string();
	} module_gen_body TOK_END opt_label {
		exitTypeScope();
		checkLabelsMatch("Begin label", $3, $7);
		SET_AST_NODE_LOC(ast_stack.back(), @1, @7);
		ast_stack.pop_back();
	};

// result is wrapped in a genblock only if necessary
gen_stmt_block:
	{
		(void)pushChild(std::make_unique<AstNode>(AST_GENBLOCK));
	} gen_stmt_or_module_body_stmt {
		SET_AST_NODE_LOC(ast_stack.back(), @2, @2);
		ast_stack.pop_back();
	} | gen_block;

opt_gen_else:
	TOK_ELSE gen_stmt_block | %empty %prec FAKE_THEN;

expr:
	basic_expr {
		$$ = std::move($1);
	} |
	basic_expr TOK_QUE attr expr TOK_COL expr {
		$$ = std::make_unique<AstNode>(AST_TERNARY);
		$$->children.push_back(std::move($1));
		$$->children.push_back(std::move($4));
		$$->children.push_back(std::move($6));
		SET_AST_NODE_LOC($$.get(), @1, @$);
		append_attr($$.get(), $3);
	} |
	inc_or_dec_op attr rvalue {
		$$ = addIncOrDecExpr(std::move($3), $2, $1, @1, @3, false);
	} |
	// TODO: Attributes are allowed in the middle here, but they create some
	// non-trivial conflicts that don't seem worth solving for now.
	rvalue inc_or_dec_op {
		$$ = addIncOrDecExpr(std::move($1), nullptr, $2, @1, @2, true);
	};

basic_expr:
	rvalue {
		$$ = std::move($1);
	} |
	TOK_LPAREN expr TOK_RPAREN integral_number {
		if ($4->compare(0, 1, "'") != 0)
			frontend_verilog_yyerror("Cast operation must be applied on sized constants e.g. (<expr>)<constval> , while %s is not a sized constant.", $4->c_str());
		auto val = const2ast(*$4, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		if (val == nullptr)
			log_error("Value conversion failed: `%s'\n", $4->c_str());
		$$ = std::make_unique<AstNode>(AST_TO_BITS, std::move($2), std::move(val));
	} |
	hierarchical_id integral_number {
		if ($2->compare(0, 1, "'") != 0)
			frontend_verilog_yyerror("Cast operation must be applied on sized constants, e.g. <ID>\'d0, while %s is not a sized constant.", $2->c_str());
		auto bits = std::make_unique<AstNode>(AST_IDENTIFIER);
		bits->str = *$1;
		SET_AST_NODE_LOC(bits.get(), @1, @1);
		auto val = const2ast(*$2, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		SET_AST_NODE_LOC(val.get(), @2, @2);
		if (val == nullptr)
			log_error("Value conversion failed: `%s'\n", $2->c_str());
		$$ = std::make_unique<AstNode>(AST_TO_BITS, std::move(bits), std::move(val));
	} |
	integral_number {
		$$ = const2ast(*$1, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		SET_AST_NODE_LOC($$.get(), @1, @1);
		if ($$ == nullptr)
			log_error("Value conversion failed: `%s'\n", $1->c_str());
	} |
	TOK_REALVAL {
		$$ = std::make_unique<AstNode>(AST_REALVALUE);
		char *p = (char*)malloc(GetSize(*$1) + 1), *q;
		for (int i = 0, j = 0; j < GetSize(*$1); j++)
			if ((*$1)[j] != '_')
				p[i++] = (*$1)[j], p[i] = 0;
		$$->realvalue = strtod(p, &q);
		SET_AST_NODE_LOC($$.get(), @1, @1);
		log_assert(*q == 0);
		free(p);
	} |
	TOK_STRING {
		$$ = AstNode::mkconst_str(*$1);
		SET_AST_NODE_LOC($$.get(), @1, @1);
	} |
	hierarchical_id attr {
		// super sketchy! Orphaned pointer in non-owning ast_stack
		AstNode *node = new AstNode(AST_FCALL);
		node->str = *$1;
		ast_stack.push_back(node);
		SET_AST_NODE_LOC(node, @1, @1);
		append_attr(node, $2);
	} TOK_LPAREN arg_list optional_comma TOK_RPAREN {
		$$.reset(ast_stack.back());
		ast_stack.pop_back();
	} |
	TOK_TO_SIGNED attr TOK_LPAREN expr TOK_RPAREN {
		$$ = std::make_unique<AstNode>(AST_TO_SIGNED, std::move($4));
		append_attr($$.get(), $2);
	} |
	TOK_TO_UNSIGNED attr TOK_LPAREN expr TOK_RPAREN {
		$$ = std::make_unique<AstNode>(AST_TO_UNSIGNED, std::move($4));
		append_attr($$.get(), $2);
	} |
	TOK_LPAREN expr TOK_RPAREN {
		$$ = std::move($2);
	} |
	TOK_LPAREN expr TOK_COL expr TOK_COL expr TOK_RPAREN {
		$$ = std::move($4);
	} |
	TOK_LCURL concat_list TOK_RCURL {
		$$ = std::move($2);
	} |
	TOK_LCURL expr TOK_LCURL concat_list TOK_RCURL TOK_RCURL {
		$$ = std::make_unique<AstNode>(AST_REPLICATE, std::move($2), std::move($4));
	} |
	TOK_TILDE attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_BIT_NOT, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
	} |
	basic_expr TOK_AMP attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_BIT_AND, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_NAND attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_BIT_NOT, std::make_unique<AstNode>(AST_BIT_AND, std::move($1), std::move($4)));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_PIPE attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_BIT_OR, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_NOR attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_BIT_NOT, std::make_unique<AstNode>(AST_BIT_OR, std::move($1), std::move($4)));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_CARET attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_BIT_XOR, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_XNOR attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_BIT_XNOR, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	TOK_AMP attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_REDUCE_AND, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
	} |
	OP_NAND attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_REDUCE_AND, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
		$$ = std::make_unique<AstNode>(AST_LOGIC_NOT, std::move($$));
	} |
	TOK_PIPE attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_REDUCE_OR, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), std::move($2));
	} |
	OP_NOR attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_REDUCE_OR, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
		$$ = std::make_unique<AstNode>(AST_LOGIC_NOT, std::move($$));
		SET_AST_NODE_LOC($$.get(), @1, @3);
	} |
	TOK_CARET attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_REDUCE_XOR, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
	} |
	OP_XNOR attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_REDUCE_XNOR, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
	} |
	basic_expr OP_SHL attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_SHIFT_LEFT, std::move($1), std::make_unique<AstNode>(AST_TO_UNSIGNED, std::move($4)));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_SHR attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_SHIFT_RIGHT, std::move($1), std::make_unique<AstNode>(AST_TO_UNSIGNED, std::move($4)));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_SSHL attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_SHIFT_SLEFT, std::move($1), std::make_unique<AstNode>(AST_TO_UNSIGNED, std::move($4)));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_SSHR attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_SHIFT_SRIGHT, std::move($1), std::make_unique<AstNode>(AST_TO_UNSIGNED, std::move($4)));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_LT attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_LT, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_LE attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_LE, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_EQ attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_EQ, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_NE attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_NE, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_EQX attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_EQX, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_NEX attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_NEX, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_GE attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_GE, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_GT attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_GT, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_PLUS attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_ADD, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_MINUS attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_SUB, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_ASTER attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_MUL, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_SLASH attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_DIV, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr TOK_PERC attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_MOD, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_POW attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_POW, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	TOK_PLUS attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_POS, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
	} |
	TOK_MINUS attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_NEG, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
	} |
	basic_expr OP_LAND attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_LOGIC_AND, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	basic_expr OP_LOR attr basic_expr {
		$$ = std::make_unique<AstNode>(AST_LOGIC_OR, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
		append_attr($$.get(), $3);
	} |
	TOK_EXCL attr basic_expr %prec UNARY_OPS {
		$$ = std::make_unique<AstNode>(AST_LOGIC_NOT, std::move($3));
		SET_AST_NODE_LOC($$.get(), @1, @3);
		append_attr($$.get(), $2);
	} |
	TOK_SIGNED OP_CAST TOK_LPAREN expr TOK_RPAREN {
		if (!sv_mode)
			frontend_verilog_yyerror("Static cast is only supported in SystemVerilog mode.");
		$$ = std::make_unique<AstNode>(AST_TO_SIGNED, std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
	} |
	TOK_UNSIGNED OP_CAST TOK_LPAREN expr TOK_RPAREN {
		if (!sv_mode)
			frontend_verilog_yyerror("Static cast is only supported in SystemVerilog mode.");
		$$ = std::make_unique<AstNode>(AST_TO_UNSIGNED, std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
	} |
	basic_expr OP_CAST TOK_LPAREN expr TOK_RPAREN {
		if (!sv_mode)
			frontend_verilog_yyerror("Static cast is only supported in SystemVerilog mode.");
		$$ = std::make_unique<AstNode>(AST_CAST_SIZE, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
	} |
	typedef_base_type OP_CAST TOK_LPAREN expr TOK_RPAREN {
		if (!sv_mode)
			frontend_verilog_yyerror("Static cast is only supported in SystemVerilog mode.");
		$$ = std::make_unique<AstNode>(AST_CAST_SIZE, std::move($1), std::move($4));
		SET_AST_NODE_LOC($$.get(), @1, @4);
	} |
	TOK_LPAREN expr TOK_EQ expr TOK_RPAREN {
		ensureAsgnExprAllowed();
		$$ = $2->clone();
		auto node = std::make_unique<AstNode>(AST_ASSIGN_EQ, std::move($2), std::move($4));
		SET_AST_NODE_LOC(node.get(), @2, @4);
		ast_stack.back()->children.push_back(std::move(node));
	} |
	TOK_LPAREN expr asgn_binop expr TOK_RPAREN {
		ensureAsgnExprAllowed();
		$$ = addAsgnBinopStmt(nullptr, std::move($2), $3, std::move($4), @2, @4)-> clone();
	};

concat_list:
	expr {
		$$ = std::make_unique<AstNode>(AST_CONCAT, std::move($1));
	} |
	expr TOK_COMMA concat_list {
		$$ = std::move($3);
		$$->children.push_back(std::move($1));
	};

integral_number:
	TOK_CONSTVAL { $$ = $1; } |
	TOK_UNBASED_UNSIZED_CONSTVAL { $$ = $1; } |
	TOK_BASE TOK_BASED_CONSTVAL {
		$1->append(*$2);
		$$ = std::move($1);
	} |
	TOK_CONSTVAL TOK_BASE TOK_BASED_CONSTVAL {
		$1->append(*$2).append(*$3);
		$$ = std::move($1);
	};
