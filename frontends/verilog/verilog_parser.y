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
#include <stack>
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
	std::map<std::string, AstNode*> *attr_list, default_attr_list;
	std::stack<std::map<std::string, AstNode*> *> attr_list_stack;
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
	bool noassert_mode, noassume_mode, norestrict_mode;
	bool assume_asserts_mode, assert_assumes_mode;
	bool current_wire_rand, current_wire_const;
	bool current_modport_input, current_modport_output;
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

%token <string> TOK_STRING TOK_ID TOK_CONSTVAL TOK_REALVAL TOK_PRIMITIVE TOK_SVA_LABEL
%token TOK_ASSERT TOK_ASSUME TOK_RESTRICT TOK_COVER
%token ATTR_BEGIN ATTR_END DEFATTR_BEGIN DEFATTR_END
%token TOK_MODULE TOK_ENDMODULE TOK_PARAMETER TOK_LOCALPARAM TOK_DEFPARAM
%token TOK_PACKAGE TOK_ENDPACKAGE TOK_PACKAGESEP
%token TOK_INTERFACE TOK_ENDINTERFACE TOK_MODPORT
%token TOK_INPUT TOK_OUTPUT TOK_INOUT TOK_WIRE TOK_REG TOK_LOGIC
%token TOK_INTEGER TOK_SIGNED TOK_ASSIGN TOK_ALWAYS TOK_INITIAL
%token TOK_BEGIN TOK_END TOK_IF TOK_ELSE TOK_FOR TOK_WHILE TOK_REPEAT
%token TOK_DPI_FUNCTION TOK_POSEDGE TOK_NEGEDGE TOK_OR TOK_AUTOMATIC
%token TOK_CASE TOK_CASEX TOK_CASEZ TOK_ENDCASE TOK_DEFAULT
%token TOK_FUNCTION TOK_ENDFUNCTION TOK_TASK TOK_ENDTASK TOK_SPECIFY TOK_ENDSPECIFY TOK_SPECPARAM
%token TOK_GENERATE TOK_ENDGENERATE TOK_GENVAR TOK_REAL
%token TOK_SYNOPSYS_FULL_CASE TOK_SYNOPSYS_PARALLEL_CASE
%token TOK_SUPPLY0 TOK_SUPPLY1 TOK_TO_SIGNED TOK_TO_UNSIGNED
%token TOK_POS_INDEXED TOK_NEG_INDEXED TOK_PROPERTY TOK_ENUM TOK_TYPEDEF
%token TOK_RAND TOK_CONST TOK_CHECKER TOK_ENDCHECKER TOK_EVENTUALLY
%token TOK_INCREMENT TOK_DECREMENT TOK_UNIQUE TOK_PRIORITY

%type <ast> range range_or_multirange  non_opt_range non_opt_multirange range_or_signed_int
%type <ast> wire_type expr basic_expr concat_list rvalue lvalue lvalue_concat_list
%type <string> opt_label opt_sva_label tok_prim_wrapper hierarchical_id
%type <boolean> opt_signed opt_property unique_case_attr
%type <al> attr case_attr

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

%nonassoc FAKE_THEN
%nonassoc TOK_ELSE

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
	interface design |
	/* empty */;

attr:
	{
		if (attr_list != nullptr)
			attr_list_stack.push(attr_list);
		attr_list = new std::map<std::string, AstNode*>;
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
	attr_opt ATTR_BEGIN opt_attr_list ATTR_END |
	/* empty */;

defattr:
	DEFATTR_BEGIN {
		if (attr_list != nullptr)
			attr_list_stack.push(attr_list);
		attr_list = new std::map<std::string, AstNode*>;
		for (auto &it : default_attr_list)
			delete it.second;
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
	attr_list | /* empty */;

attr_list:
	attr_assign |
	attr_list ',' attr_assign;

attr_assign:
	hierarchical_id {
		if (attr_list->count(*$1) != 0)
			delete (*attr_list)[*$1];
		(*attr_list)[*$1] = AstNode::mkconst_int(1, false);
		delete $1;
	} |
	hierarchical_id '=' expr {
		if (attr_list->count(*$1) != 0)
			delete (*attr_list)[*$1];
		(*attr_list)[*$1] = $3;
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
	} param_signed param_integer param_range single_param_decl |
	TOK_LOCALPARAM {
		if (astbuf1) delete astbuf1;
		astbuf1 = new AstNode(AST_LOCALPARAM);
		astbuf1->children.push_back(AstNode::mkconst_int(0, true));
	} param_signed param_integer param_range single_param_decl |
	single_param_decl;

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
			frontend_verilog_yyerror("SystemVerilog interface in module port list cannot have a default value.");
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
	TOK_ID {
		astbuf1 = new AstNode(AST_INTERFACEPORT);
		astbuf1->children.push_back(new AstNode(AST_INTERFACEPORTTYPE));
		astbuf1->children[0]->str = *$1;
		delete $1;
	} TOK_ID {  /* SV interfaces */
		if (!sv_mode)
			frontend_verilog_yyerror("Interface found in port list (%s). This is not supported unless read_verilog is called with -sv!", $3->c_str());
		astbuf2 = astbuf1->clone(); // really only needed if multiple instances of same type.
		astbuf2->str = *$3;
		delete $3;
		astbuf2->port_id = ++port_counter;
		ast_stack.back()->children.push_back(astbuf2);
		delete astbuf1; // really only needed if multiple instances of same type.
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

interface:
	TOK_INTERFACE TOK_ID {
		do_not_require_port_stubs = false;
		AstNode *intf = new AstNode(AST_INTERFACE);
		ast_stack.back()->children.push_back(intf);
		ast_stack.push_back(intf);
		current_ast_mod = intf;
		port_stubs.clear();
		port_counter = 0;
		intf->str = *$2;
		delete $2;
	} module_para_opt module_args_opt ';' interface_body TOK_ENDINTERFACE {
		if (port_stubs.size() != 0)
			frontend_verilog_yyerror("Missing details for module port `%s'.",
				port_stubs.begin()->first.c_str());
		ast_stack.pop_back();
		log_assert(ast_stack.size() == 1);
		current_ast_mod = NULL;
	};

interface_body:
	interface_body interface_body_stmt |;

interface_body_stmt:
	param_decl | localparam_decl | defparam_decl | wire_decl | always_stmt | assign_stmt |
	modport_stmt;

non_opt_delay:
	'#' TOK_ID { delete $2; } |
	'#' TOK_CONSTVAL { delete $2; } |
	'#' TOK_REALVAL { delete $2; } |
	'#' '(' expr ')' { delete $3; } |
	'#' '(' expr ':' expr ':' expr ')' { delete $3; delete $5; delete $7; };

delay:
	non_opt_delay | /* empty */;

wire_type:
	{
		astbuf3 = new AstNode(AST_WIRE);
		current_wire_rand = false;
		current_wire_const = false;
	} wire_type_token_list delay {
		$$ = astbuf3;
	};

wire_type_token_list:
	wire_type_token | wire_type_token_list wire_type_token |
	wire_type_token_io ;

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

wire_type_token:
	TOK_WIRE {
	} |
	TOK_REG {
		astbuf3->is_reg = true;
	} |
	TOK_LOGIC {
		astbuf3->is_logic = true;
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
	} |
	TOK_RAND {
		current_wire_rand = true;
	} |
	TOK_CONST {
		current_wire_const = true;
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
	task_func_decl | specify_block |param_decl | localparam_decl | defparam_decl | specparam_declaration | wire_decl | assign_stmt | cell_stmt |
	always_stmt | TOK_GENERATE module_gen_body TOK_ENDGENERATE | defattr | assert_property | checker_decl;

checker_decl:
	TOK_CHECKER TOK_ID ';' {
		AstNode *node = new AstNode(AST_GENBLOCK);
		node->str = *$2;
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
	} module_body TOK_ENDCHECKER {
		delete $2;
		ast_stack.pop_back();
	};

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
	attr TOK_TASK opt_automatic TOK_ID {
		current_function_or_task = new AstNode(AST_TASK);
		current_function_or_task->str = *$4;
		append_attr(current_function_or_task, $1);
		ast_stack.back()->children.push_back(current_function_or_task);
		ast_stack.push_back(current_function_or_task);
		current_function_or_task_port_id = 1;
		delete $4;
	} task_func_args_opt ';' task_func_body TOK_ENDTASK {
		current_function_or_task = NULL;
		ast_stack.pop_back();
	} |
	attr TOK_FUNCTION opt_automatic opt_signed range_or_signed_int TOK_ID {
		current_function_or_task = new AstNode(AST_FUNCTION);
		current_function_or_task->str = *$6;
		append_attr(current_function_or_task, $1);
		ast_stack.back()->children.push_back(current_function_or_task);
		ast_stack.push_back(current_function_or_task);
		AstNode *outreg = new AstNode(AST_WIRE);
		outreg->str = *$6;
		outreg->is_signed = $4;
		outreg->is_reg = true;
		if ($5 != NULL) {
			outreg->children.push_back($5);
			outreg->is_signed = $4 || $5->is_signed;
			$5->is_signed = false;
		}
		current_function_or_task->children.push_back(outreg);
		current_function_or_task_port_id = 1;
		delete $6;
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

opt_automatic:
	TOK_AUTOMATIC |
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
				frontend_verilog_yyerror("integer/genvar types cannot have packed dimensions (task/function arguments)");
			} else {
				astbuf2 = new AstNode(AST_RANGE);
				astbuf2->children.push_back(AstNode::mkconst_int(astbuf1->range_left, true));
				astbuf2->children.push_back(AstNode::mkconst_int(astbuf1->range_right, true));
			}
		}
		if (astbuf2 && astbuf2->children.size() != 2)
			frontend_verilog_yyerror("task/function argument range must be of the form: [<expr>:<expr>], [<expr>+:<expr>], or [<expr>-:<expr>]");
	} wire_name | wire_name;

task_func_body:
	task_func_body behavioral_stmt |
	/* empty */;

specify_block:
	TOK_SPECIFY specify_item_opt TOK_ENDSPECIFY |
	TOK_SPECIFY TOK_ENDSPECIFY ;

specify_item_opt:
	specify_item_opt specify_item |
	specify_item ;

specify_item:
	specparam_declaration
	// | pulsestyle_declaration
	// | showcancelled_declaration
	| path_declaration
	| system_timing_declaration
	;

specparam_declaration:
	TOK_SPECPARAM list_of_specparam_assignments ';' |
	TOK_SPECPARAM specparam_range list_of_specparam_assignments ';' ;

// IEEE 1364-2005 calls this sinmply 'range' but the current 'range' rule allows empty match
// and the 'non_opt_range' rule allows index ranges not allowed by 1364-2005
// exxxxtending this for SV specparam would change this anyhow
specparam_range:
	'[' constant_expression ':' constant_expression ']' ;

list_of_specparam_assignments:
	specparam_assignment | list_of_specparam_assignments ',' specparam_assignment;

specparam_assignment:
	TOK_ID '=' constant_mintypmax_expression ;

/*
pulsestyle_declaration :
	;

showcancelled_declaration :
	;
*/

path_declaration :
	simple_path_declaration ';'
	// | edge_sensitive_path_declaration
	// | state_dependent_path_declaration
	;

simple_path_declaration :
	parallel_path_description '=' path_delay_value |
	full_path_description '=' path_delay_value
	;

path_delay_value :
	'(' path_delay_expression list_of_path_delay_extra_expressions ')'
	|     path_delay_expression
	|     path_delay_expression list_of_path_delay_extra_expressions
	;

list_of_path_delay_extra_expressions :
/*
	t_path_delay_expression
	| trise_path_delay_expression ',' tfall_path_delay_expression
	| trise_path_delay_expression ',' tfall_path_delay_expression ',' tz_path_delay_expression
	| t01_path_delay_expression ',' t10_path_delay_expression ',' t0z_path_delay_expression ','
	  tz1_path_delay_expression ',' t1z_path_delay_expression ',' tz0_path_delay_expression
	| t01_path_delay_expression ',' t10_path_delay_expression ',' t0z_path_delay_expression ','
	  tz1_path_delay_expression ',' t1z_path_delay_expression ',' tz0_path_delay_expression ','
	  t0x_path_delay_expression ',' tx1_path_delay_expression ',' t1x_path_delay_expression ','
	  tx0_path_delay_expression ',' txz_path_delay_expression ',' tzx_path_delay_expression
*/
	',' path_delay_expression
	|  ',' path_delay_expression ',' path_delay_expression
	|  ',' path_delay_expression ',' path_delay_expression ','
	  path_delay_expression ',' path_delay_expression ',' path_delay_expression
	|  ',' path_delay_expression ',' path_delay_expression ','
	  path_delay_expression ',' path_delay_expression ',' path_delay_expression ','
	  path_delay_expression ',' path_delay_expression ',' path_delay_expression ','
	  path_delay_expression ',' path_delay_expression ',' path_delay_expression
	;

parallel_path_description :
	'(' specify_input_terminal_descriptor opt_polarity_operator '=' '>' specify_output_terminal_descriptor ')' ;

full_path_description :
	'(' list_of_path_inputs '*' '>' list_of_path_outputs ')' ;

// This was broken into 2 rules to solve shift/reduce conflicts
list_of_path_inputs :
	specify_input_terminal_descriptor                  opt_polarity_operator  |
	specify_input_terminal_descriptor more_path_inputs opt_polarity_operator ;

more_path_inputs :
    ',' specify_input_terminal_descriptor |
    more_path_inputs ',' specify_input_terminal_descriptor ;

list_of_path_outputs :
	specify_output_terminal_descriptor |
	list_of_path_outputs ',' specify_output_terminal_descriptor ;

opt_polarity_operator :
	'+'
	| '-'
	| ;

// Good enough for the time being
specify_input_terminal_descriptor :
	TOK_ID ;

// Good enough for the time being
specify_output_terminal_descriptor :
	TOK_ID ;

system_timing_declaration :
	TOK_ID '(' system_timing_args ')' ';' ;

system_timing_arg :
	TOK_POSEDGE TOK_ID |
	TOK_NEGEDGE TOK_ID |
	expr ;

system_timing_args :
	system_timing_arg |
	system_timing_args ',' system_timing_arg ;

/*
t_path_delay_expression :
	path_delay_expression;

trise_path_delay_expression :
	path_delay_expression;

tfall_path_delay_expression :
	path_delay_expression;

tz_path_delay_expression :
	path_delay_expression;

t01_path_delay_expression :
	path_delay_expression;

t10_path_delay_expression :
	path_delay_expression;

t0z_path_delay_expression :
	path_delay_expression;

tz1_path_delay_expression :
	path_delay_expression;

t1z_path_delay_expression :
	path_delay_expression;

tz0_path_delay_expression :
	path_delay_expression;

t0x_path_delay_expression :
	path_delay_expression;

tx1_path_delay_expression :
	path_delay_expression;

t1x_path_delay_expression :
	path_delay_expression;

tx0_path_delay_expression :
	path_delay_expression;

txz_path_delay_expression :
	path_delay_expression;

tzx_path_delay_expression :
	path_delay_expression;
*/

path_delay_expression :
	constant_expression;

constant_mintypmax_expression :
	constant_expression
	| constant_expression ':' constant_expression ':' constant_expression
	;

// for the time being this is OK, but we may write our own expr here.
// as I'm not sure it is legal to use a full expr here (probably not)
// On the other hand, other rules requiring constant expressions also use 'expr'
// (such as param assignment), so we may leave this as-is, perhaps adding runtime checks for constant-ness
constant_expression:
	expr ;

param_signed:
	TOK_SIGNED {
		astbuf1->is_signed = true;
	} | /* empty */;

param_integer:
	TOK_INTEGER {
		if (astbuf1->children.size() != 1)
			frontend_verilog_yyerror("Internal error in param_integer - should not happen?");
		astbuf1->children.push_back(new AstNode(AST_RANGE));
		astbuf1->children.back()->children.push_back(AstNode::mkconst_int(31, true));
		astbuf1->children.back()->children.push_back(AstNode::mkconst_int(0, true));
		astbuf1->is_signed = true;
	} | /* empty */;

param_real:
	TOK_REAL {
		if (astbuf1->children.size() != 1)
			frontend_verilog_yyerror("Parameter already declared as integer, cannot set to real.");
		astbuf1->children.push_back(new AstNode(AST_REALVALUE));
	} | /* empty */;

param_range:
	range {
		if ($1 != NULL) {
			if (astbuf1->children.size() != 1)
				frontend_verilog_yyerror("integer/real parameters should not have a range.");
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
		AstNode *node;
		if (astbuf1 == nullptr) {
			if (!sv_mode)
				frontend_verilog_yyerror("In pure Verilog (not SystemVerilog), parameter/localparam with an initializer must use the parameter/localparam keyword");
			node = new AstNode(AST_PARAMETER);
			node->children.push_back(AstNode::mkconst_int(0, true));
		} else {
			node = astbuf1->clone();
		}
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
	range rvalue '=' expr {
		AstNode *node = new AstNode(AST_DEFPARAM);
		node->children.push_back($2);
		node->children.push_back($4);
		if ($1 != NULL)
			node->children.push_back($1);
		ast_stack.back()->children.push_back(node);
	};

wire_decl:
	attr wire_type range {
		albuf = $1;
		astbuf1 = $2;
		astbuf2 = $3;
		if (astbuf1->range_left >= 0 && astbuf1->range_right >= 0) {
			if (astbuf2) {
				frontend_verilog_yyerror("integer/genvar types cannot have packed dimensions.");
			} else {
				astbuf2 = new AstNode(AST_RANGE);
				astbuf2->children.push_back(AstNode::mkconst_int(astbuf1->range_left, true));
				astbuf2->children.push_back(AstNode::mkconst_int(astbuf1->range_right, true));
			}
		}
		if (astbuf2 && astbuf2->children.size() != 2)
			frontend_verilog_yyerror("wire/reg/logic packed dimension must be of the form: [<expr>:<expr>], [<expr>+:<expr>], or [<expr>-:<expr>]");
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
	wire_name {
		bool attr_anyconst = false;
		bool attr_anyseq = false;
		bool attr_allconst = false;
		bool attr_allseq = false;
		if (ast_stack.back()->children.back()->get_bool_attribute("\\anyconst")) {
			delete ast_stack.back()->children.back()->attributes.at("\\anyconst");
			ast_stack.back()->children.back()->attributes.erase("\\anyconst");
			attr_anyconst = true;
		}
		if (ast_stack.back()->children.back()->get_bool_attribute("\\anyseq")) {
			delete ast_stack.back()->children.back()->attributes.at("\\anyseq");
			ast_stack.back()->children.back()->attributes.erase("\\anyseq");
			attr_anyseq = true;
		}
		if (ast_stack.back()->children.back()->get_bool_attribute("\\allconst")) {
			delete ast_stack.back()->children.back()->attributes.at("\\allconst");
			ast_stack.back()->children.back()->attributes.erase("\\allconst");
			attr_allconst = true;
		}
		if (ast_stack.back()->children.back()->get_bool_attribute("\\allseq")) {
			delete ast_stack.back()->children.back()->attributes.at("\\allseq");
			ast_stack.back()->children.back()->attributes.erase("\\allseq");
			attr_allseq = true;
		}
		if (current_wire_rand || attr_anyconst || attr_anyseq || attr_allconst || attr_allseq) {
			AstNode *wire = new AstNode(AST_IDENTIFIER);
			AstNode *fcall = new AstNode(AST_FCALL);
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
			fcall->attributes["\\reg"] = AstNode::mkconst_str(RTLIL::unescape_id(wire->str));
			ast_stack.back()->children.push_back(new AstNode(AST_ASSIGN, wire, fcall));
		}
	} |
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
			frontend_verilog_yyerror("Internal error - should not happen - no AST_WIRE node.");
		AstNode *node = astbuf1->clone();
		node->str = *$1;
		append_attr_clone(node, albuf);
		if (astbuf2 != NULL)
			node->children.push_back(astbuf2->clone());
		if ($2 != NULL) {
			if (node->is_input || node->is_output)
				frontend_verilog_yyerror("input/output/inout ports cannot have unpacked dimensions.");
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

opt_sva_label:
	TOK_SVA_LABEL ':' {
		$$ = $1;
	} |
	/* empty */ {
		$$ = NULL;
	};

opt_property:
	TOK_PROPERTY {
		$$ = true;
	} |
	/* empty */ {
		$$ = false;
	};

modport_stmt:
    TOK_MODPORT TOK_ID {
        AstNode *modport = new AstNode(AST_MODPORT);
        ast_stack.back()->children.push_back(modport);
        ast_stack.push_back(modport);
        modport->str = *$2;
        delete $2;
    }  modport_args_opt {
        ast_stack.pop_back();
        log_assert(ast_stack.size() == 2);
    } ';'

modport_args_opt:
    '(' ')' | '(' modport_args optional_comma ')';

modport_args:
    modport_arg | modport_args ',' modport_arg;

modport_arg:
    modport_type_token modport_member |
    modport_member

modport_member:
    TOK_ID {
        AstNode *modport_member = new AstNode(AST_MODPORTMEMBER);
        ast_stack.back()->children.push_back(modport_member);
        modport_member->str = *$1;
        modport_member->is_input = current_modport_input;
        modport_member->is_output = current_modport_output;
        delete $1;
    }

modport_type_token:
    TOK_INPUT {current_modport_input = 1; current_modport_output = 0;} | TOK_OUTPUT {current_modport_input = 0; current_modport_output = 1;}

assert:
	opt_sva_label TOK_ASSERT opt_property '(' expr ')' ';' {
		if (noassert_mode) {
			delete $5;
		} else {
			AstNode *node = new AstNode(assume_asserts_mode ? AST_ASSUME : AST_ASSERT, $5);
			if ($1 != nullptr)
				node->str = *$1;
			ast_stack.back()->children.push_back(node);
		}
		if ($1 != nullptr)
			delete $1;
	} |
	opt_sva_label TOK_ASSUME opt_property '(' expr ')' ';' {
		if (noassume_mode) {
			delete $5;
		} else {
			AstNode *node = new AstNode(assert_assumes_mode ? AST_ASSERT : AST_ASSUME, $5);
			if ($1 != nullptr)
				node->str = *$1;
			ast_stack.back()->children.push_back(node);
		}
		if ($1 != nullptr)
			delete $1;
	} |
	opt_sva_label TOK_ASSERT opt_property '(' TOK_EVENTUALLY expr ')' ';' {
		if (noassert_mode) {
			delete $6;
		} else {
			AstNode *node = new AstNode(assume_asserts_mode ? AST_FAIR : AST_LIVE, $6);
			if ($1 != nullptr)
				node->str = *$1;
			ast_stack.back()->children.push_back(node);
		}
		if ($1 != nullptr)
			delete $1;
	} |
	opt_sva_label TOK_ASSUME opt_property '(' TOK_EVENTUALLY expr ')' ';' {
		if (noassume_mode) {
			delete $6;
		} else {
			AstNode *node = new AstNode(assert_assumes_mode ? AST_LIVE : AST_FAIR, $6);
			if ($1 != nullptr)
				node->str = *$1;
			ast_stack.back()->children.push_back(node);
		}
		if ($1 != nullptr)
			delete $1;
	} |
	opt_sva_label TOK_COVER opt_property '(' expr ')' ';' {
		AstNode *node = new AstNode(AST_COVER, $5);
		if ($1 != nullptr) {
			node->str = *$1;
			delete $1;
		}
		ast_stack.back()->children.push_back(node);
	} |
	opt_sva_label TOK_COVER opt_property '(' ')' ';' {
		AstNode *node = new AstNode(AST_COVER, AstNode::mkconst_int(1, false));
		if ($1 != nullptr) {
			node->str = *$1;
			delete $1;
		}
		ast_stack.back()->children.push_back(node);
	} |
	opt_sva_label TOK_COVER ';' {
		AstNode *node = new AstNode(AST_COVER, AstNode::mkconst_int(1, false));
		if ($1 != nullptr) {
			node->str = *$1;
			delete $1;
		}
		ast_stack.back()->children.push_back(node);
	} |
	opt_sva_label TOK_RESTRICT opt_property '(' expr ')' ';' {
		if (norestrict_mode) {
			delete $5;
		} else {
			AstNode *node = new AstNode(AST_ASSUME, $5);
			if ($1 != nullptr)
				node->str = *$1;
			ast_stack.back()->children.push_back(node);
		}
		if (!$3)
			log_file_warning(current_filename, get_line_num(), "SystemVerilog does not allow \"restrict\" without \"property\".\n");
		if ($1 != nullptr)
			delete $1;
	} |
	opt_sva_label TOK_RESTRICT opt_property '(' TOK_EVENTUALLY expr ')' ';' {
		if (norestrict_mode) {
			delete $6;
		} else {
			AstNode *node = new AstNode(AST_FAIR, $6);
			if ($1 != nullptr)
				node->str = *$1;
			ast_stack.back()->children.push_back(node);
		}
		if (!$3)
			log_file_warning(current_filename, get_line_num(), "SystemVerilog does not allow \"restrict\" without \"property\".\n");
		if ($1 != nullptr)
			delete $1;
	};

assert_property:
	opt_sva_label TOK_ASSERT TOK_PROPERTY '(' expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(assume_asserts_mode ? AST_ASSUME : AST_ASSERT, $5));
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
			delete $1;
		}
	} |
	opt_sva_label TOK_ASSUME TOK_PROPERTY '(' expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(AST_ASSUME, $5));
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
			delete $1;
		}
	} |
	opt_sva_label TOK_ASSERT TOK_PROPERTY '(' TOK_EVENTUALLY expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(assume_asserts_mode ? AST_FAIR : AST_LIVE, $6));
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
			delete $1;
		}
	} |
	opt_sva_label TOK_ASSUME TOK_PROPERTY '(' TOK_EVENTUALLY expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(AST_FAIR, $6));
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
			delete $1;
		}
	} |
	opt_sva_label TOK_COVER TOK_PROPERTY '(' expr ')' ';' {
		ast_stack.back()->children.push_back(new AstNode(AST_COVER, $5));
		if ($1 != nullptr) {
			ast_stack.back()->children.back()->str = *$1;
			delete $1;
		}
	} |
	opt_sva_label TOK_RESTRICT TOK_PROPERTY '(' expr ')' ';' {
		if (norestrict_mode) {
			delete $5;
		} else {
			ast_stack.back()->children.push_back(new AstNode(AST_ASSUME, $5));
			if ($1 != nullptr) {
				ast_stack.back()->children.back()->str = *$1;
				delete $1;
			}
		}
	} |
	opt_sva_label TOK_RESTRICT TOK_PROPERTY '(' TOK_EVENTUALLY expr ')' ';' {
		if (norestrict_mode) {
			delete $6;
		} else {
			ast_stack.back()->children.push_back(new AstNode(AST_FAIR, $6));
			if ($1 != nullptr) {
				ast_stack.back()->children.back()->str = *$1;
				delete $1;
			}
		}
	};

simple_behavioral_stmt:
	lvalue '=' delay expr {
		AstNode *node = new AstNode(AST_ASSIGN_EQ, $1, $4);
		ast_stack.back()->children.push_back(node);
	} |
	lvalue TOK_INCREMENT {
		AstNode *node = new AstNode(AST_ASSIGN_EQ, $1, new AstNode(AST_ADD, $1->clone(), AstNode::mkconst_int(1, true)));
		ast_stack.back()->children.push_back(node);
	} |
	lvalue TOK_DECREMENT {
		AstNode *node = new AstNode(AST_ASSIGN_EQ, $1, new AstNode(AST_SUB, $1->clone(), AstNode::mkconst_int(1, true)));
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
			frontend_verilog_yyerror("Begin label (%s) and end label (%s) don't match.", $3->c_str()+1, $7->c_str()+1);
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
	case_attr case_type '(' expr ')' {
		AstNode *node = new AstNode(AST_CASE, $4);
		ast_stack.back()->children.push_back(node);
		ast_stack.push_back(node);
		append_attr(node, $1);
	} opt_synopsys_attr case_body TOK_ENDCASE {
		case_type_stack.pop_back();
		ast_stack.pop_back();
	};

unique_case_attr:
	/* empty */ {
		$$ = false;
	} |
	TOK_PRIORITY case_attr {
		$$ = $2;
	} |
	TOK_UNIQUE case_attr {
		$$ = true;
	};

case_attr:
	attr unique_case_attr {
		if ($2) (*$1)["\\parallel_case"] = AstNode::mkconst_int(1, false);
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
	/* empty */ %prec FAKE_THEN;

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
	TOK_SVA_LABEL {
		ast_stack.back()->children.push_back(new AstNode(AST_IDENTIFIER));
		ast_stack.back()->children.back()->str = *$1;
		delete $1;
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
		if ($2 == nullptr && ($$->str == "\\$initstate" ||
				$$->str == "\\$anyconst" || $$->str == "\\$anyseq" ||
				$$->str == "\\$allconst" || $$->str == "\\$allseq"))
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
	TOK_ELSE gen_stmt_or_null | /* empty */ %prec FAKE_THEN;

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
	'(' expr ')' TOK_CONSTVAL {
		if ($4->substr(0, 1) != "'")
			frontend_verilog_yyerror("Cast operation must be applied on sized constants e.g. (<expr>)<constval> , while %s is not a sized constant.", $4->c_str());
		AstNode *bits = $2;
		AstNode *val = const2ast(*$4, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		if (val == NULL)
			log_error("Value conversion failed: `%s'\n", $4->c_str());
		$$ = new AstNode(AST_TO_BITS, bits, val);
		delete $4;
	} |
	hierarchical_id TOK_CONSTVAL {
		if ($2->substr(0, 1) != "'")
			frontend_verilog_yyerror("Cast operation must be applied on sized constants, e.g. <ID>\'d0, while %s is not a sized constant.", $2->c_str());
		AstNode *bits = new AstNode(AST_IDENTIFIER);
		bits->str = *$1;
		AstNode *val = const2ast(*$2, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		if (val == NULL)
			log_error("Value conversion failed: `%s'\n", $2->c_str());
		$$ = new AstNode(AST_TO_BITS, bits, val);
		delete $1;
		delete $2;
	} |
	TOK_CONSTVAL TOK_CONSTVAL {
		$$ = const2ast(*$1 + *$2, case_type_stack.size() == 0 ? 0 : case_type_stack.back(), !lib_mode);
		if ($$ == NULL || (*$2)[0] != '\'')
			log_error("Value conversion failed: `%s%s'\n", $1->c_str(), $2->c_str());
		delete $1;
		delete $2;
	} |
	TOK_CONSTVAL {
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
	basic_expr OP_NAND attr basic_expr {
		$$ = new AstNode(AST_BIT_NOT, new AstNode(AST_BIT_AND, $1, $4));
		append_attr($$, $3);
	} |
	basic_expr '|' attr basic_expr {
		$$ = new AstNode(AST_BIT_OR, $1, $4);
		append_attr($$, $3);
	} |
	basic_expr OP_NOR attr basic_expr {
		$$ = new AstNode(AST_BIT_NOT, new AstNode(AST_BIT_OR, $1, $4));
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

