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

%{
#include <list>
#include <string.h>
#include "frontends/verilog/verilog_frontend.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
using namespace AST;
using namespace VERILOG_FRONTEND;

YOSYS_NAMESPACE_BEGIN
namespace VERILOG_FRONTEND {
	int port_counter;
	std::map<std::string, int> port_stubs;
	std::map<std::string, AstNode*> attr_list, default_attr_list;
	std::map<std::string, AstNode*> *albuf;
	std::vector<AstNode*> ast_stack;
	struct AstNode *astbuf1, *astbuf2, *astbuf3;
	struct AstNode *current_function_or_task;
	struct AstNode *current_ast, *current_ast_mod;
	int current_function_or_task_port_id;
	std::vector<char> case_type_stack;
	bool do_not_require_port_stubs;
	bool default_nettype_wire;
	bool sv_mode, formal_mode, lib_mode;
	bool norestrict_mode, assume_asserts_mode;
	std::istream *lexin;
}
YOSYS_NAMESPACE_END

static void append_attr(AstNode *ast, std::map<std::string, AstNode*> *al)
{
	for (auto &it : *al) {
		if (ast->attributes.count(it.first) > 0)
			delete ast->attributes[it.first];
		ast->attributes[it.first] = it.second;
	}
	delete al;
}

static void append_attr_clone(AstNode *ast, std::map<std::string, AstNode*> *al)
{
	for (auto &it : *al) {
		if (ast->attributes.count(it.first) > 0)
			delete ast->attributes[it.first];
		ast->attributes[it.first] = it.second->clone();
	}
}

static void free_attr(std::map<std::string, AstNode*> *al)
{
	for (auto &it : *al)
		delete it.second;
	delete al;
}

%}

%name-prefix "frontend_verilog_yy"

%union {
	std::string *string;
	struct YOSYS_NAMESPACE_PREFIX AST::AstNode *ast;
	std::map<std::string, YOSYS_NAMESPACE_PREFIX AST::AstNode*> *al;
	bool boolean;
}

%token <string> TOK_STRING TOK_ID TOK_CONST TOK_REALVAL TOK_PRIMITIVE
%token ATTR_BEGIN ATTR_END DEFATTR_BEGIN DEFATTR_END
%token TOK_MODULE TOK_ENDMODULE TOK_PARAMETER TOK_LOCALPARAM TOK_DEFPARAM
%token TOK_PACKAGE TOK_ENDPACKAGE TOK_PACKAGESEP
%token TOK_INPUT TOK_OUTPUT TOK_INOUT TOK_WIRE TOK_REG
%token TOK_INTEGER TOK_SIGNED TOK_ASSIGN TOK_ALWAYS TOK_INITIAL
%token TOK_BEGIN TOK_END TOK_IF TOK_ELSE TOK_FOR TOK_WHILE TOK_REPEAT
%token TOK_DPI_FUNCTION TOK_POSEDGE TOK_NEGEDGE TOK_OR
%token TOK_CASE TOK_CASEX TOK_CASEZ TOK_ENDCASE TOK_DEFAULT
%token TOK_FUNCTION TOK_ENDFUNCTION TOK_TASK TOK_ENDTASK
%token TOK_GENERATE TOK_ENDGENERATE TOK_GENVAR TOK_REAL
%token TOK_SYNOPSYS_FULL_CASE TOK_SYNOPSYS_PARALLEL_CASE
%token TOK_SUPPLY0 TOK_SUPPLY1 TOK_TO_SIGNED TOK_TO_UNSIGNED
%token TOK_POS_INDEXED TOK_NEG_INDEXED TOK_ASSERT TOK_ASSUME
%token TOK_RESTRICT TOK_PROPERTY

%type <ast> range range_or_multirange  non_opt_range non_opt_multirange range_or_signed_int
%type <ast> wire_type expr basic_expr concat_list rvalue lvalue lvalue_concat_list
%type <string> opt_label tok_prim_wrapper hierarchical_id
%type <boolean> opt_signed
%type <al> attr

// operator precedence from low to high
%left OP_LOR
%left OP_LAND
%left '|' OP_NOR
%left '^' OP_XNOR
%left '&' OP_NAND
%left OP_EQ OP_NE OP_EQX OP_NEX
%left '<' OP_LE OP_GE '>'
%left OP_SHL OP_SHR OP_SSHL OP_SSHR
%left '+' '-'
%left '*' '/' '%'
%left OP_POW
%right UNARY_OPS

%define parse.error verbose
%define parse.lac full

%expect 2
%debug

%%

input: {
	ast_stack.clear();
	ast_stack.push_back(current_ast);
} design {
	ast_stack.pop_back();
	log_assert(GetSize(ast_stack) == 0);
	for (auto &it : default_attr_list)
		delete it.second;
	default_attr_list.clear();
};

design:
	module design |
	defattr design |
	task_func_decl design |
	param_decl design |
	localparam_decl design |
	package design |
	/* empty */;

attr:
	{
		for (auto &it : attr_list)
			delete it.second;
		attr_list.clear();
		for (auto &it : default_attr_list)
			attr_list[it.first] = it.second->clone();
	} attr_opt {
		std::map<std::string, AstNode*> *al = new std::map<std::string, AstNode*>;
		al->swap(attr_list);
		$$ = al;
	};

attr_opt:
	attr_opt ATTR_BEGIN opt_attr_list ATTR_END |
	/* empty */;

defattr:
	DEFATTR_BEGIN {
		for (auto &it : default_attr_list)
			delete it.second;
		default_attr_list.clear();
		for (auto &it : attr_list)
			delete it.second;
		attr_list.clear();
	} opt_attr_list {
		default_attr_list = attr_list;
		attr_list.clear();
	} DEFATTR_END;

opt_attr_list:
	attr_list | /* empty */;

attr_list:
	attr_assign |
	attr_list ',' attr_assign;

attr_assign:
	hierarchical_id {
		if (attr_list.count(*$1) != 0)
			delete attr_list[*$1];
		attr_list[*$1] = AstNode::mkconst_int(1, false);
		delete $1;
	} |
	hierarchical_id '=' expr {
		if (attr_list.count(*$1) != 0)
			delete attr_list[*$1];
		attr_list[*$1] = $3;
		delete $1;
	};

hierarchical_id:
	TOK_ID {
		$$ = $1;
	} |
	hierarchical_id TOK_PACKAGESEP TOK_ID {
		if ($3->substr(0, 1) == "\\")
			*$1 += "::" + $3->substr(1);
		else
			*$1 += "::" + *$3;
		delete $3;
		$$ = $1;
	} |
	hierarchical_id '.' TOK_ID {
		if ($3->substr(0, 1) == "\\")
			*$1 += "." + $3->substr(1);
		else
			*$1 += "." + *$3;
		delete $3;
		$$ = $1;
	};

module:
	attr TOK_MODULE TOK_ID {
		do_not_require_port_stubs = false;
		AstNode *mod = new AstNode(AST_MODULE);
		ast_stack.back()->children.push_back(mod);
		ast_stack.push_back(mod);
		current_ast_mod = mod;
		port_stubs.clear();
		port_counter = 0;
		mod->str = *$3;
		append_attr(mod, $1);
		delete $3;
	} module_para_opt module_args_opt ';' module_body TOK_ENDMODULE {
		if (port_stubs.size() != 0)
			frontend_verilog_yyerror("Missing details for module port `%s'.",
					port_stubs.begin()->first.c_str());
		ast_stack.pop_back();
		log_assert(ast_stack.size() == 1);
		current_ast_mod = NULL;
	};

module_para_opt:
	'#' '(' { astbuf1 = nullptr; } module_para_list { if (astbuf1) delete astbuf1; } ')' | /* empty */;

module_para_list:
	single_module_para | module_para_list ',' single_module_para;

single_module_para:
	/* empty */ |
	TOK_PARAMETER {
		if (astbuf1) delete astbuf1;
		astbuf1 = new AstNode(AST_PARAMETER);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
	} param_signed param_integer param_range single_param_decl | single_param_decl;

module_args_opt:
	'(' ')' | /* empty */ | '(' module_args optional_comma ')';

module_args:
	module_arg | module_args ',' module_arg;

optional_comma:
	',' | /* empty */;

module_arg_opt_assignment:
	'=' expr {
		if (ast_stack.back()->children.size() > 0 && ast_stack.back()->children.back()->type == AST_WIRE) {
			AstNode *wire = new AstNode(AST_IDENTIFIER);
			wire->str = ast_stack.back()->children.back()->str;
			if (ast_stack.back()->children.back()->is_reg)
				ast_stack.back()->children.push_back(new AstNode(AST_INITIAL, new AstNode(AST_BLOCK, new AstNode(AST_ASSIGN_LE, wire, $2))));
			else
				ast_stack.back()->children.push_back(new AstNode(AST_ASSIGN, wire, $2));
		} else
			frontend_verilog_yyerror("Syntax error.");
	} |
	/* empty */;

module_arg:
	TOK_ID {
		if (ast_stack.back()->children.size() > 0 && ast_stack.back()->children.back()->type == AST_WIRE) {
			AstNode *node = ast_stack.back()->children.back()->clone();
			node->str = *$1;
			node->port_id = ++port_counter;
			ast_stack.back()->children.push_back(node);
		} else {
			if (port_stubs.count(*$1) != 0)
				frontend_verilog_yyerror("Duplicate module port `%s'.", $1->c_str());
			port_stubs[*$1] = ++port_counter;
		}
		delete $1;
	} module_arg_opt_assignment |
	attr wire_type range TOK_ID {
		AstNode *node = $2;
		node->str = *$4;
		node->port_id = ++port_counter;
		if ($3 != NULL)
			node->children.push_back($3);
		if (!node->is_input && !node->is_output)
			frontend_verilog_yyerror("Module port `%s' is neither input nor output.", $4->c_str());
		if (node->is_reg && node->is_input && !node->is_output && !sv_mode)
			frontend_verilog_yyerror("Input port `%s' is declared as register.", $4->c_str());
		ast_stack.back()->children.push_back(node);
		append_attr(node, $1);
		delete $4;
	} module_arg_opt_assignment |
	'.' '.' '.' {
		do_not_require_port_stubs = true;
	};

package:
	attr TOK_PACKAGE TOK_ID {
		AstNode *mod = new AstNode(AST_PACKAGE);
		ast_stack.back()->children.push_back(mod);
		ast_stack.push_back(mod);
		current_ast_mod = mod;
		mod->str = *$3;
		append_attr(mod, $1);
	} ';' package_body TOK_ENDPACKAGE {
		ast_stack.pop_back();
		current_ast_mod = NULL;
	};

package_body:
	package_body package_body_stmt |;

package_body_stmt:
	localparam_decl;

non_opt_delay:
	'#' '(' expr ')' { delete $3; } |
	'#' '(' expr ':' expr ':' expr ')' { delete $3; delete $5; delete $7; };

delay:
	non_opt_delay | /* empty */;

wire_type:
	{
		astbuf3 = new AstNode(AST_WIRE);
	} wire_type_token_list delay {
		$$ = astbuf3;
	};

wire_type_token_list:
	wire_type_token | wire_type_token_list wire_type_token;

wire_type_token:
	TOK_INPUT {
		astbuf3->is_input = true;
	} |
	TOK_OUTPUT {
		astbuf3->is_output = true;
	} |
	TOK_INOUT {
		astbuf3->is_input = true;
		astbuf3->is_output = true;
	} |
	TOK_WIRE {
	} |
	TOK_REG {
		astbuf3->is_reg = true;
	} |
	TOK_INTEGER {
		astbuf3->is_reg = true;
		astbuf3->range_left = 31;
		astbuf3->range_right = 0;
		astbuf3->is_signed = true;
	} |
	TOK_GENVAR {
		astbuf3->type = AST_GENVAR;
		astbuf3->is_reg = true;
		astbuf3->range_left = 31;
		astbuf3->range_right = 0;
	} |
	TOK_SIGNED {
		astbuf3->is_signed = true;
	};

non_opt_range:
	'[' expr ':' expr ']' {
		$$ = new AstNode(AST_RANGE);
		$$->children.push_back($2);
		$$->children.push_back($4);
	} |
	'[' expr TOK_POS_INDEXED expr ']' {
		$$ = new AstNode(AST_RANGE);
		$$->children.push_back(new AstNode(AST_SUB, new AstNode(AST_ADD, $2->clone(), $4), AstNode::mkconst_int(1, true)));
		$$->children.push_back(new AstNode(AST_ADD, $2, AstNode::mkconst_int(0, true)));
	} |
	'[' expr TOK_NEG_INDEXED expr ']' {
		$$ = new AstNode(AST_RANGE);
		$$->children.push_back(new AstNode(AST_ADD, $2, AstNode::mkconst_int(0, true)));
		$$->children.push_back(new AstNode(AST_SUB, new AstNode(AST_ADD, $2->clone(), AstNode::mkconst_int(1, true)), $4));
	} |
	'[' expr ']' {
		$$ = new AstNode(AST_RANGE);
		$$->children.push_back($2);
	};

non_opt_multirange:
	non_opt_range non_opt_range {
		$$ = new AstNode(AST_MULTIRANGE, $1, $2);
	} |
	non_opt_multirange non_opt_range {
		$$ = $1;
		$$->children.push_back($2);
	};

range:
	non_opt_range {
		$$ = $1;
	} |
	/* empty */ {
		$$ = NULL;
	};

range_or_multirange:
	range { $$ = $1; } |
	non_opt_multirange { $$ = $1; };

range_or_signed_int:
	range {
		$$ = $1;
	} |
	TOK_INTEGER {
		$$ = new AstNode(AST_RANGE);
		$$->children.push_back(AstNode::mkconst_int(31, true));
		$$->children.push_back(AstNode::mkconst_int(0, true));
		$$->is_signed = true;
	};

module_body:
	module_body module_body_stmt |
	/* the following line makes the generate..endgenrate keywords optional */
	module_body gen_stmt |
	/* empty */;

module_body_stmt:
	task_func_decl | param_decl | localparam_decl | defparam_decl | wire_decl | assign_stmt | cell_stmt |
	always_stmt | TOK_GENERATE module_gen_body TOK_ENDGENERATE | defattr | assert_property;

task_func_decl:
	attr TOK_DPI_FUNCTION TOK_ID TOK_ID {
		current_function_or_task = new AstNode(AST_DPI_FUNCTION, AstNode::mkconst_str(*$3), AstNode::mkconst_str(*$4));
		current_function_or_task->str = *$4;
		append_attr(current_function_or_task, $1);
		ast_stack.back()->children.push_back(current_function_or_task);
		delete $3;
		delete $4;
	} opt_dpi_function_args ';' {
		current_function_or_task = NULL;
	} |
	attr TOK_DPI_FUNCTION TOK_ID '=' TOK_ID TOK_ID {
		current_function_or_task = new AstNode(AST_DPI_FUNCTION, AstNode::mkconst_str(*$5), AstNode::mkconst_str(*$3));
		current_function_or_task->str = *$6;
		append_attr(current_function_or_task, $1);
		ast_stack.back()->children.push_back(current_function_or_task);
		delete $3;
		delete $5;
		delete $6;
	} opt_dpi_function_args ';' {
		current_function_or_task = NULL;
	} |
	attr TOK_DPI_FUNCTION TOK_ID ':' TOK_ID '=' TOK_ID TOK_ID {
		current_function_or_task = new AstNode(AST_DPI_FUNCTION, AstNode::mkconst_str(*$7), AstNode::mkconst_str(*$3 + ":" + RTLIL::unescape_id(*$5)));
		current_function_or_task->str = *$8;
		append_attr(current_function_or_task, $1);
		ast_stack.back()->children.push_back(current_function_or_task);
		delete $3;
		delete $5;
		delete $7;
		delete $8;
	} opt_dpi_function_args ';' {
		current_function_or_task = NULL;
	} |
	attr TOK_TASK TOK_ID {
		current_function_or_task = new AstNode(AST_TASK);
		current_function_or_task->str = *$3;
		append_attr(current_function_or_task, $1);
		ast_stack.back()->children.push_back(current_function_or_task);
		ast_stack.push_back(current_function_or_task);
		current_function_or_task_port_id = 1;
		delete $3;
	} task_func_args_opt ';' task_func_body TOK_ENDTASK {
		current_function_or_task = NULL;
		ast_stack.pop_back();
	} |
	attr TOK_FUNCTION opt_signed range_or_signed_int TOK_ID {
		current_function_or_task = new AstNode(AST_FUNCTION);
		current_function_or_task->str = *$5;
		append_attr(current_function_or_task, $1);
		ast_stack.back()->children.push_back(current_function_or_task);
		ast_stack.push_back(current_function_or_task);
		AstNode *outreg = new AstNode(AST_WIRE);
		outreg->str = *$5;
		outreg->is_signed = $3;
		if ($4 != NULL) {
			outreg->children.push_back($4);
			outreg->is_signed = $3 || $4->is_signed;
			$4->is_signed = false;
		}
		current_function_or_task->children.push_back(outreg);
		current_function_or_task_port_id = 1;
		delete $5;
	} task_func_args_opt ';' task_func_body TOK_ENDFUNCTION {
		current_function_or_task = NULL;
		ast_stack.pop_back();
	};

dpi_function_arg:
	TOK_ID TOK_ID {
		current_function_or_task->children.push_back(AstNode::mkconst_str(*$1));
		delete $1;
		delete $2;
	} |
	TOK_ID {
		current_function_or_task->children.push_back(AstNode::mkconst_str(*$1));
		delete $1;
	};

opt_dpi_function_args:
	'(' dpi_function_args ')' |
	/* empty */;

dpi_function_args:
	dpi_function_args ',' dpi_function_arg |
	dpi_function_args ',' |
	dpi_function_arg |
	/* empty */;

opt_signed:
	TOK_SIGNED {
		$$ = true;
	} |
	/* empty */ {
		$$ = false;
	};

task_func_args_opt:
	'(' ')' | /* empty */ | '(' {
		albuf = nullptr;
		astbuf1 = nullptr;
		astbuf2 = nullptr;
	} task_func_args optional_comma {
		delete astbuf1;
		if (astbuf2 != NULL)
			delete astbuf2;
		free_attr(albuf);
	} ')';

task_func_args:
	task_func_port | task_func_args ',' task_func_port;

task_func_port:
	attr wire_type range {
		if (albuf) {
			delete astbuf1;
			if (astbuf2 != NULL)
				delete astbuf2;
			free_attr(albuf);
		}
		albuf = $1;
		astbuf1 = $2;
		astbuf2 = $3;
		if (astbuf1->range_left >= 0 && astbuf1->range_right >= 0) {
			if (astbuf2) {
				frontend_verilog_yyerror("Syntax error.");
			} else {
				astbuf2 = new AstNode(AST_RANGE);
				astbuf2->children.push_back(AstNode::mkconst_int(astbuf1->range_left, true));
				astbuf2->children.push_back(AstNode::mkconst_int(astbuf1->range_right, true));
			}
		}
		if (astbuf2 && astbuf2->children.size() != 2)
			frontend_verilog_yyerror("Syntax error.");
	} wire_name | wire_name;

task_func_body:
	task_func_body behavioral_stmt |
	/* empty */;

param_signed:
	TOK_SIGNED {
		astbuf1->is_signed = true;
	} | /* empty */;

param_integer:
	TOK_INTEGER {
		if (astbuf1->children.size() != 1)
			frontend_verilog_yyerror("Syntax error.");
		astbuf1->children.push_back(new AstNode(AST_RANGE));
		astbuf1->children.back()->children.push_back(AstNode::mkconst_int(31, true));
		astbuf1->children.back()->children.push_back(AstNode::mkconst_int(0, true));
		astbuf1->is_signed = true;
	} | /* empty */;

param_real:
	TOK_REAL {
		if (astbuf1->children.size() != 1)
			frontend_verilog_yyerror("Syntax error.");
		astbuf1->children.push_back(new AstNode(AST_REALVALUE));
	} | /* empty */;

param_range:
	range {
		if ($1 != NULL) {
			if (astbuf1->children.size() != 1)
				frontend_verilog_yyerror("Syntax error.");
			astbuf1->children.push_back($1);
		}
	};

param_decl:
	TOK_PARAMETER {
		astbuf1 = new AstNode(AST_PARAMETER);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
	} param_signed param_integer param_real param_range param_decl_list ';' {
		delete astbuf1;
	};

localparam_decl:
	TOK_LOCALPARAM {
		astbuf1 = new AstNode(AST_LOCALPARAM);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
	} param_signed param_integer param_real param_range param_decl_list ';' {
		delete astbuf1;
	};

param_decl_list:
	single_param_decl | param_decl_list ',' single_param_decl;

single_param_decl:
	TOK_ID '=' expr {
		if (astbuf1 == nullptr)
			frontend_verilog_yyerror("syntax error");
		AstNode *node = astbuf1->clone();
		node->str = *$1;
		delete node->children[0];
		node->children[0] = $3;
		ast_stack.back()->children.push_back(node);
		delete $1;
	};

defparam_decl:
	TOK_DEFPARAM defparam_decl_list ';';

defparam_decl_list:
	single_defparam_decl | defparam_decl_list ',' single_defparam_decl;

single_defparam_decl:
	range hierarchical_id '=' expr {
		AstNode *node = new AstNode(AST_DEFPARAM);
		node->str = *$2;
		node->children.push_back($4);
		if ($1 != NULL)
			node->children.push_back($1);
		ast_stack.back()->children.push_back(node);
		delete $2;
	};

wire_decl:
	attr wire_type range {
		albuf = $1;
		astbuf1 = $2;
		astbuf2 = $3;
		if (astbuf1->range_left >= 0 && astbuf1->range_right >= 0) {
			if (astbuf2) {
				frontend_verilog_yyerror("Syntax error.");
			} else {
				astbuf2 = new AstNode(AST_RANGE);
				astbuf2->children.push_back(AstNode::mkconst_int(astbuf1->range_left, true));
				astbuf2->children.push_back(AstNode::mkconst_int(astbuf1->range_right, true));
			}
		}
		if (astbuf2 && astbuf2->children.size() != 2)
			frontend_verilog_yyerror("Syntax error.");
	} wire_name_list {
		delete astbuf1;
		if (astbuf2 != NULL)
			delete astbuf2;
		free_attr(albuf);
	} ';' |
	attr TOK_SUPPLY0 TOK_ID {
		ast_stack.back()->children.push_back(new AstNode(AST_WIRE));
		ast_stack.back()->children.back()->str = *$3;
		append_attr(ast_stack.back()->children.back(), $1);
		ast_stack.back()->children.push_back(new AstNode(AST_ASSIGN, new AstNode(AST_IDENTIFIER), AstNode::mkconst_int(0, false, 1)));
		ast_stack.back()->children.back()->children[0]->str = *$3;
		delete $3;
	} opt_supply_wires ';' |
	attr TOK_SUPPLY1 TOK_ID {
		ast_stack.back()->children.push_back(new AstNode(AST_WIRE));
		ast_stack.back()->children.back()->str = *$3;
		append_attr(ast_stack.back()->children.back(), $1);
		ast_stack.back()->children.push_back(new AstNode(AST_ASSIGN, new AstNode(AST_IDENTIFIER), AstNode::mkconst_int(1, false, 1)));
		ast_stack.back()->children.back()->children[0]->str = *$3;
		delete $3;
	} opt_supply_wires ';';

opt_supply_wires:
	/* empty */ |
	opt_supply_wires ',' TOK_ID {
		AstNode *wire_node = ast_stack.back()->children.at(GetSize(ast_stack.back()->children)-2)->clone();
		AstNode *assign_node = ast_stack.back()->children.at(GetSize(ast_stack.back()->children)-1)->clone();
		wire_node->str = *$3;
		assign_node->children[0]->str = *$3;
		ast_stack.back()->children.push_back(wire_node);
		ast_stack.back()->children.push_back(assign_node);
		delete $3;
	};

wire_name_list:
	wire_name_and_opt_assign | wire_name_list ',' wire_name_and_opt_assign;

wire_name_and_opt_assign:
	wire_name |
	wire_name '=' expr {
		AstNode *wire = new AstNode(AST_IDENTIFIER);
		wire->str = ast_stack.back()->children.back()->str;
		if (astbuf1->is_reg)
			ast_stack.back()->children.push_back(new AstNode(AST_INITIAL, new AstNode(AST_BLOCK, new AstNode(AST_ASSIGN_LE, wire, $3))));
		else
			ast_stack.back()->children.push_back(new AstNode(AST_ASSIGN, wire, $3));
	};

wire_name:
	TOK_ID range_or_multirange {
		if (astbuf1 == nullptr)
			frontend_verilog_yyerror("Syntax error.");
		AstNode *node = astbuf1->clone();
		node->str = *$1;
		append_attr_clone(node, albuf);
		if (astbuf2 != NULL)
			node->children.push_back(astbuf2->clone());
		if ($2 != NULL) {
			if (node->is_input || node->is_output)
				frontend_verilog_yyerror("Syntax error.");
			if (!astbuf2) {
				AstNode *rng = new AstNode(AST_RANGE);
				rng->children.push_back(AstNode::mkconst_int(0, true));
				rng->children.push_back(AstNode::mkconst_int(0, true));
				node->children.push_back(rng);
			}
			node->type = AST_MEMORY;
			node->children.push_back($2);
		}
		if (current_function_or_task == NULL) {
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
		} else {
			if (node->is_input || node->is_output)
				node->port_id = current_function_or_task_port_id++;
		}
		ast_stack.back()->children.push_back(node);
		delete $1;
	};

assign_stmt:
	TOK_ASSIGN delay assign_expr_list ';';

assign_expr_list:
	assign_expr | assign_expr_list ',' assign_expr;

assign_expr:
	lvalue '=' expr {
		ast_stack.back()->children.push_back(new AstNode(AST_ASSIGN, $1, $3));
	};

cell_stmt:
	attr TOK_ID {
		astbuf1 = new AstNode(AST_CELL);
		append_attr(astbuf1, $1);
		astbuf1->children.push_back(new AstNode(AST_CELLTYPE));
		astbuf1->children[0]->str = *$2;
		delete $2;
	} cell_parameter_list_opt cell_list ';' {
		delete astbuf1;
	} |
	attr tok_prim_wrapper delay {
		astbuf1 = new AstNode(AST_PRIMITIVE);
		astbuf1->str = *$2;
		append_attr(astbuf1, $1);
		delete $2;
	} prim_list ';' {
		delete astbuf1;
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
	cell_list ',' single_cell;

single_cell:
	TOK_ID {
		astbuf2 = astbuf1->clone();
		if (astbuf2->type != AST_PRIMITIVE)
			astbuf2->str = *$1;
		delete $1;
		ast_stack.back()->children.push_back(astbuf2);
	} '(' cell_port_list ')' |
	TOK_ID non_opt_range {
		astbuf2 = astbuf1->clone();
		if (astbuf2->type != AST_PRIMITIVE)
			astbuf2->str = *$1;
		delete $1;
		ast_stack.back()->children.push_back(new AstNode(AST_CELLARRAY, $2, astbuf2));
	} '(' cell_port_list ')';

prim_list:
	single_prim |
	prim_list ',' single_prim;

single_prim:
	single_cell |
	/* no name */ {
		astbuf2 = astbuf1->clone();
		ast_stack.back()->children.push_back(astbuf2);
	} '(' cell_port_list ')';

cell_parameter_list_opt:
	'#' '(' cell_parameter_list ')' | /* empty */;

cell_parameter_list:
	cell_parameter | cell_parameter_list ',' cell_parameter;

cell_parameter:
	/* empty */ |
	expr {
		AstNode *node = new AstNode(AST_PARASET);
		astbuf1->children.push_back(node);
		node->children.push_back($1);
	} |
	'.' TOK_ID '(' expr ')' {
		AstNode *node = new AstNode(AST_PARASET);
		node->str = *$2;
		astbuf1->children.push_back(node);
		node->children.push_back($4);
		delete $2;
	};

cell_port_list:
	cell_port_list_rules {
		// remove empty args from end of list
		while (!astbuf2->children.empty()) {
			AstNode *node = astbuf2->children.back();
			if (node->type != AST_ARGUMENT) break;
			if (!node->children.empty()) break;
			if (!node->str.empty()) break;
			astbuf2->children.pop_back();
			delete node;
		}

		// check port types
		bool has_positional_args = false;
		bool has_named_args = false;
		for (auto node : astbuf2->children) {
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
	cell_port | cell_port_list_rules ',' cell_port;

cell_port:
	/* empty */ {
		AstNode *node = new AstNode(AST_ARGUMENT);
		astbuf2->children.push_back(node);
	} |
	expr {
		AstNode *node = new AstNode(AST_ARGUMENT);
		astbuf2->children.push_back(node);
		node->children.push_back($1);
	} |
	'.' TOK_ID '(' expr ')' {
		AstNode *node = new AstNode(AST_ARGUMENT);
		node->str = *$2;
		astbuf2->children.push_back(node);
		node->children.push_back($4);
		delete $2;
	} |
	'.' TOK_ID '(' ')' {
		AstNode *node = new AstNode(AST_ARGUMENT);
		node->str = *$2;
		astbuf2->children.push_back(node);
		delete $2;
	};

always_stmt:
	attr TOK_ALWAYS {
		AstNode *node = new AstNode(AST_ALWAYS);
		append_attr(node, $1);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
	} always_cond {
		AstNode *block = new AstNode(AST_BLOCK);
		ast_stack.back()->children.push_back(block);
		ast_stack.push_back(block);
	} behavioral_stmt {
		ast_stack.pop_back();
		ast_stack.pop_back();
	} |
	attr TOK_INITIAL {
		AstNode *node = new AstNode(AST_INITIAL);
		append_attr(node, $1);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		AstNode *block = new AstNode(AST_BLOCK);
		ast_stack.back()->children.push_back(block);
		ast_stack.push_back(block);
	} behavioral_stmt {
		ast_stack.pop_back();
		ast_stack.pop_back();
	};

always_cond:
	'@' '(' always_events ')' |
	'@' '(' '*' ')' |
	'@' ATTR_BEGIN ')' |
	'@' '(' ATTR_END |
	'@' '*' |
	/* empty */;

always_events:
	always_event |
	always_events TOK_OR always_event |
	always_events ',' always_event;

always_event:
	TOK_POSEDGE expr {
		AstNode *node = new AstNode(AST_POSEDGE);
		ast_stack.back()->children.push_back(node);
		node->children.push_back($2);
	} |
	TOK_NEGEDGE expr {
		AstNode *node = new AstNode(AST_NEGEDGE);
		ast_stack.back()->children.push_back(node);
		node->children.push_back($2);
	} |
	expr {
		AstNode *node = new AstNode(AST_EDGE);
		ast_stack.back()->children.push_back(node);
		node->children.push_back($1);
	};

opt_label:
	':' TOK_ID {
		$$ = $2;
	} |
	/* empty */ {
		$$ = NULL;
	};

assert:
	TOK_ASSERT '(' expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(assume_asserts_mode ? AST_ASSUME : AST_ASSERT, $3));
	} |
	TOK_ASSUME '(' expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(AST_ASSUME, $3));
	} |
	TOK_RESTRICT '(' expr ')' ';' {
		if (norestrict_mode)
			delete $3;
		else
			ast_stack.back()->children.push_back(new AstNode(AST_ASSUME, $3));
	};

assert_property:
	TOK_ASSERT TOK_PROPERTY '(' expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(assume_asserts_mode ? AST_ASSUME : AST_ASSERT, $4));
	} |
	TOK_ASSUME TOK_PROPERTY '(' expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(AST_ASSUME, $4));
	} |
	TOK_RESTRICT TOK_PROPERTY '(' expr ')' ';' {
		if (norestrict_mode)
			delete $4;
		else
			ast_stack.back()->children.push_back(new AstNode(AST_ASSUME, $4));
	};

simple_behavioral_stmt:
	lvalue '=' delay expr {
		AstNode *node = new AstNode(AST_ASSIGN_EQ, $1, $4);
		ast_stack.back()->children.push_back(node);
	} |
	lvalue OP_LE delay expr {
		AstNode *node = new AstNode(AST_ASSIGN_LE, $1, $4);
		ast_stack.back()->children.push_back(node);
	};

// this production creates the obligatory if-else shift/reduce conflict
behavioral_stmt:
	defattr | assert | wire_decl | param_decl | localparam_decl |
	non_opt_delay behavioral_stmt |
	simple_behavioral_stmt ';' | ';' |
	hierarchical_id attr {
		AstNode *node = new AstNode(AST_TCALL);
		node->str = *$1;
		delete $1;
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		append_attr(node, $2);
	} opt_arg_list ';'{
		ast_stack.pop_back();
	} |
	attr TOK_BEGIN opt_label {
		AstNode *node = new AstNode(AST_BLOCK);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		append_attr(node, $1);
		if ($3 != NULL)
			node->str = *$3;
	} behavioral_stmt_list TOK_END opt_label {
		if ($3 != NULL && $7 != NULL && *$3 != *$7)
			frontend_verilog_yyerror("Syntax error.");
		if ($3 != NULL)
			delete $3;
		if ($7 != NULL)
			delete $7;
		ast_stack.pop_back();
	} |
	attr TOK_FOR '(' {
		AstNode *node = new AstNode(AST_FOR);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		append_attr(node, $1);
	} simple_behavioral_stmt ';' expr {
		ast_stack.back()->children.push_back($7);
	} ';' simple_behavioral_stmt ')' {
		AstNode *block = new AstNode(AST_BLOCK);
		ast_stack.back()->children.push_back(block);
		ast_stack.push_back(block);
	} behavioral_stmt {
		ast_stack.pop_back();
		ast_stack.pop_back();
	} |
	attr TOK_WHILE '(' expr ')' {
		AstNode *node = new AstNode(AST_WHILE);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		append_attr(node, $1);
		AstNode *block = new AstNode(AST_BLOCK);
		ast_stack.back()->children.push_back($4);
		ast_stack.back()->children.push_back(block);
		ast_stack.push_back(block);
	} behavioral_stmt {
		ast_stack.pop_back();
		ast_stack.pop_back();
	} |
	attr TOK_REPEAT '(' expr ')' {
		AstNode *node = new AstNode(AST_REPEAT);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		append_attr(node, $1);
		AstNode *block = new AstNode(AST_BLOCK);
		ast_stack.back()->children.push_back($4);
		ast_stack.back()->children.push_back(block);
		ast_stack.push_back(block);
	} behavioral_stmt {
		ast_stack.pop_back();
		ast_stack.pop_back();
	} |
	attr TOK_IF '(' expr ')' {
		AstNode *node = new AstNode(AST_CASE);
		AstNode *block = new AstNode(AST_BLOCK);
		AstNode *cond = new AstNode(AST_COND, AstNode::mkconst_int(1, false, 1), block);
		ast_stack.back()->children.push_back(node);
		node->children.push_back(new AstNode(AST_REDUCE_BOOL, $4));
		node->children.push_back(cond);
		ast_stack.push_back(node);
		ast_stack.push_back(block);
		append_attr(node, $1);
	} behavioral_stmt optional_else {
		ast_stack.pop_back();
		ast_stack.pop_back();
	} |
	attr case_type '(' expr ')' {
		AstNode *node = new AstNode(AST_CASE, $4);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		append_attr(node, $1);
	} opt_synopsys_attr case_body TOK_ENDCASE {
		case_type_stack.pop_back();
		ast_stack.pop_back();
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
		if (ast_stack.back()->attributes.count("\\full_case") == 0)
			ast_stack.back()->attributes["\\full_case"] = AstNode::mkconst_int(1, false);
	} |
	opt_synopsys_attr TOK_SYNOPSYS_PARALLEL_CASE {
		if (ast_stack.back()->attributes.count("\\parallel_case") == 0)
			ast_stack.back()->attributes["\\parallel_case"] = AstNode::mkconst_int(1, false);
	} |
	/* empty */;

behavioral_stmt_list:
	behavioral_stmt_list behavioral_stmt |
	/* empty */;

optional_else:
	TOK_ELSE {
		AstNode *block = new AstNode(AST_BLOCK);
		AstNode *cond = new AstNode(AST_COND, new AstNode(AST_DEFAULT), block);
		ast_stack.pop_back();
		ast_stack.back()->children.push_back(cond);
		ast_stack.push_back(block);
	} behavioral_stmt |
	/* empty */;

case_body:
	case_body case_item |
	/* empty */;

case_item:
	{
		AstNode *node = new AstNode(
				case_type_stack.size() && case_type_stack.back() == 'x' ? AST_CONDX :
				case_type_stack.size() && case_type_stack.back() == 'z' ? AST_CONDZ : AST_COND);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
	} case_select {
		AstNode *block = new AstNode(AST_BLOCK);
		ast_stack.back()->children.push_back(block);
		ast_stack.push_back(block);
		case_type_stack.push_back(0);
	} behavioral_stmt {
		case_type_stack.pop_back();
		ast_stack.pop_back();
		ast_stack.pop_back();
	};

gen_case_body:
	gen_case_body gen_case_item |
	/* empty */;

gen_case_item:
	{
		AstNode *node = new AstNode(
				case_type_stack.size() && case_type_stack.back() == 'x' ? AST_CONDX :
				case_type_stack.size() && case_type_stack.back() == 'z' ? AST_CONDZ : AST_COND);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
	} case_select {
		case_type_stack.push_back(0);
	} gen_stmt_or_null {
		case_type_stack.pop_back();
		ast_stack.pop_back();
	};

case_select:
	case_expr_list ':' |
	TOK_DEFAULT;

case_expr_list:
	TOK_DEFAULT {
		ast_stack.back()->children.push_back(new AstNode(AST_DEFAULT));
	} |
	expr {
		ast_stack.back()->children.push_back($1);
	} |
	case_expr_list ',' expr {
		ast_stack.back()->children.push_back($3);
	};

rvalue:
	hierarchical_id '[' expr ']' '.' rvalue {
		$$ = new AstNode(AST_PREFIX, $3, $6);
		$$->str = *$1;
		delete $1;
	} |
	hierarchical_id range {
		$$ = new AstNode(AST_IDENTIFIER, $2);
		$$->str = *$1;
		delete $1;
		if ($2 == nullptr && formal_mode && ($$->str == "\\$initstate" || $$->str == "\\$anyconst" || $$->str == "\\$anyseq"))
			$$->type = AST_FCALL;
	} |
	hierarchical_id non_opt_multirange {
		$$ = new AstNode(AST_IDENTIFIER, $2);
		$$->str = *$1;
		delete $1;
	};

lvalue:
	rvalue {
		$$ = $1;
	} |
	'{' lvalue_concat_list '}' {
		$$ = $2;
	};

lvalue_concat_list:
	expr {
		$$ = new AstNode(AST_CONCAT);
		$$->children.push_back($1);
	} |
	expr ',' lvalue_concat_list {
		$$ = $3;
		$$->children.push_back($1);
	};

opt_arg_list:
	'(' arg_list optional_comma ')' |
	/* empty */;

arg_list:
	arg_list2 |
	/* empty */;

arg_list2:
	single_arg |
	arg_list ',' single_arg;

single_arg:
	expr {
		ast_stack.back()->children.push_back($1);
	};

module_gen_body:
	module_gen_body gen_stmt_or_module_body_stmt |
	/* empty */;

gen_stmt_or_module_body_stmt:
	gen_stmt | module_body_stmt;

// this production creates the obligatory if-else shift/reduce conflict
gen_stmt:
	TOK_FOR '(' {
		AstNode *node = new AstNode(AST_GENFOR);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
	} simple_behavioral_stmt ';' expr {
		ast_stack.back()->children.push_back($6);
	} ';' simple_behavioral_stmt ')' gen_stmt_block {
		ast_stack.pop_back();
	} |
	TOK_IF '(' expr ')' {
		AstNode *node = new AstNode(AST_GENIF);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		ast_stack.back()->children.push_back($3);
	} gen_stmt_block opt_gen_else {
		ast_stack.pop_back();
	} |
	case_type '(' expr ')' {
		AstNode *node = new AstNode(AST_GENCASE, $3);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
	} gen_case_body TOK_ENDCASE {
		case_type_stack.pop_back();
		ast_stack.pop_back();
	} |
	TOK_BEGIN opt_label {
		AstNode *node = new AstNode(AST_GENBLOCK);
		node->str = $2 ? *$2 : std::string();
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
	} module_gen_body TOK_END opt_label {
		if ($2 != NULL)
			delete $2;
		if ($6 != NULL)
			delete $6;
		ast_stack.pop_back();
	};

gen_stmt_block:
	{
		AstNode *node = new AstNode(AST_GENBLOCK);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
	} gen_stmt_or_module_body_stmt {
		ast_stack.pop_back();
	};

gen_stmt_or_null:
	gen_stmt_block | ';';

opt_gen_else:
	TOK_ELSE gen_stmt_or_null | /* empty */;

expr:
	basic_expr {
		$$ = $1;
	} |
	basic_expr '?' attr expr ':' expr {
		$$ = new AstNode(AST_TERNARY);
		$$->children.push_back($1);
		$$->children.push_back($4);
		$$->children.push_back($6);
		append_attr($$, $3);
	};

basic_expr:
	rvalue {
		$$ = $1;
	} |
	'(' expr ')' TOK_CONST {
		if ($4->substr(0, 1) != "'")
			frontend_verilog_yyerror("Syntax error.");
		AstNode *bits = $2;
		AstNode *val = const2ast(*$4, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		if (val == NULL)
			log_error("Value conversion failed: `%s'\n", $4->c_str());
		$$ = new AstNode(AST_TO_BITS, bits, val);
		delete $4;
	} |
	hierarchical_id TOK_CONST {
		if ($2->substr(0, 1) != "'")
			frontend_verilog_yyerror("Syntax error.");
		AstNode *bits = new AstNode(AST_IDENTIFIER);
		bits->str = *$1;
		AstNode *val = const2ast(*$2, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		if (val == NULL)
			log_error("Value conversion failed: `%s'\n", $2->c_str());
		$$ = new AstNode(AST_TO_BITS, bits, val);
		delete $1;
		delete $2;
	} |
	TOK_CONST TOK_CONST {
		$$ = const2ast(*$1 + *$2, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		if ($$ == NULL || (*$2)[0] != '\'')
			log_error("Value conversion failed: `%s%s'\n", $1->c_str(), $2->c_str());
		delete $1;
		delete $2;
	} |
	TOK_CONST {
		$$ = const2ast(*$1, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		if ($$ == NULL)
			log_error("Value conversion failed: `%s'\n", $1->c_str());
		delete $1;
	} |
	TOK_REALVAL {
		$$ = new AstNode(AST_REALVALUE);
		char *p = (char*)malloc(GetSize(*$1) + 1), *q;
		for (int i = 0, j = 0; j < GetSize(*$1); j++)
			if ((*$1)[j] != '_')
				p[i++] = (*$1)[j], p[i] = 0;
		$$->realvalue = strtod(p, &q);
		log_assert(*q == 0);
		delete $1;
		free(p);
	} |
	TOK_STRING {
		$$ = AstNode::mkconst_str(*$1);
		delete $1;
	} |
	hierarchical_id attr {
		AstNode *node = new AstNode(AST_FCALL);
		node->str = *$1;
		delete $1;
		ast_stack.push_back(node);
		append_attr(node, $2);
	} '(' arg_list optional_comma ')' {
		$$ = ast_stack.back();
		ast_stack.pop_back();
	} |
	TOK_TO_SIGNED attr '(' expr ')' {
		$$ = new AstNode(AST_TO_SIGNED, $4);
		append_attr($$, $2);
	} |
	TOK_TO_UNSIGNED attr '(' expr ')' {
		$$ = new AstNode(AST_TO_UNSIGNED, $4);
		append_attr($$, $2);
	} |
	'(' expr ')' {
		$$ = $2;
	} |
	'(' expr ':' expr ':' expr ')' {
		delete $2;
		$$ = $4;
		delete $6;
	} |
	'{' concat_list '}' {
		$$ = $2;
	} |
	'{' expr '{' concat_list '}' '}' {
		$$ = new AstNode(AST_REPLICATE, $2, $4);
	} |
	'~' attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_BIT_NOT, $3);
		append_attr($$, $2);
	} |
	basic_expr '&' attr basic_expr {
		$$ = new AstNode(AST_BIT_AND, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '|' attr basic_expr {
		$$ = new AstNode(AST_BIT_OR, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '^' attr basic_expr {
		$$ = new AstNode(AST_BIT_XOR, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_XNOR attr basic_expr {
		$$ = new AstNode(AST_BIT_XNOR, $1, $4);
		append_attr($$, $3);
	} |
	'&' attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_REDUCE_AND, $3);
		append_attr($$, $2);
	} |
	OP_NAND attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_REDUCE_AND, $3);
		append_attr($$, $2);
		$$ = new AstNode(AST_LOGIC_NOT, $$);
	} |
	'|' attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_REDUCE_OR, $3);
		append_attr($$, $2);
	} |
	OP_NOR attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_REDUCE_OR, $3);
		append_attr($$, $2);
		$$ = new AstNode(AST_LOGIC_NOT, $$);
	} |
	'^' attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_REDUCE_XOR, $3);
		append_attr($$, $2);
	} |
	OP_XNOR attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_REDUCE_XNOR, $3);
		append_attr($$, $2);
	} |
	basic_expr OP_SHL attr basic_expr {
		$$ = new AstNode(AST_SHIFT_LEFT, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_SHR attr basic_expr {
		$$ = new AstNode(AST_SHIFT_RIGHT, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_SSHL attr basic_expr {
		$$ = new AstNode(AST_SHIFT_SLEFT, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_SSHR attr basic_expr {
		$$ = new AstNode(AST_SHIFT_SRIGHT, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '<' attr basic_expr {
		$$ = new AstNode(AST_LT, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_LE attr basic_expr {
		$$ = new AstNode(AST_LE, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_EQ attr basic_expr {
		$$ = new AstNode(AST_EQ, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_NE attr basic_expr {
		$$ = new AstNode(AST_NE, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_EQX attr basic_expr {
		$$ = new AstNode(AST_EQX, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_NEX attr basic_expr {
		$$ = new AstNode(AST_NEX, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_GE attr basic_expr {
		$$ = new AstNode(AST_GE, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '>' attr basic_expr {
		$$ = new AstNode(AST_GT, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '+' attr basic_expr {
		$$ = new AstNode(AST_ADD, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '-' attr basic_expr {
		$$ = new AstNode(AST_SUB, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '*' attr basic_expr {
		$$ = new AstNode(AST_MUL, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '/' attr basic_expr {
		$$ = new AstNode(AST_DIV, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr '%' attr basic_expr {
		$$ = new AstNode(AST_MOD, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_POW attr basic_expr {
		$$ = new AstNode(AST_POW, $1, $4);
		append_attr($$, $3);
	} |
	'+' attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_POS, $3);
		append_attr($$, $2);
	} |
	'-' attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_NEG, $3);
		append_attr($$, $2);
	} |
	basic_expr OP_LAND attr basic_expr {
		$$ = new AstNode(AST_LOGIC_AND, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_LOR attr basic_expr {
		$$ = new AstNode(AST_LOGIC_OR, $1, $4);
		append_attr($$, $3);
	} |
	'!' attr basic_expr %prec UNARY_OPS {
		$$ = new AstNode(AST_LOGIC_NOT, $3);
		append_attr($$, $2);
	};

concat_list:
	expr {
		$$ = new AstNode(AST_CONCAT, $1);
	} |
	expr ',' concat_list {
		$$ = $3;
		$$->children.push_back($1);
	};

