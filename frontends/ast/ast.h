/* -*- c++ -*-
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

#ifndef AST_H
#define AST_H

#include "kernel/rtlil.h"
#include <stdint.h>
#include <set>

YOSYS_NAMESPACE_BEGIN

namespace AST
{
	// all node types, type2str() must be extended
	// whenever a new node type is added here
	enum AstNodeType
	{
		AST_NONE,
		AST_DESIGN,
		AST_MODULE,
		AST_TASK,
		AST_FUNCTION,
		AST_DPI_FUNCTION,

		AST_WIRE,
		AST_MEMORY,
		AST_AUTOWIRE,
		AST_PARAMETER,
		AST_LOCALPARAM,
		AST_DEFPARAM,
		AST_PARASET,
		AST_ARGUMENT,
		AST_RANGE,
		AST_MULTIRANGE,
		AST_CONSTANT,
		AST_REALVALUE,
		AST_CELLTYPE,
		AST_IDENTIFIER,
		AST_PREFIX,
		AST_ASSERT,
		AST_ASSUME,
		AST_LIVE,
		AST_FAIR,
		AST_COVER,
		AST_ENUM,
		AST_ENUM_ITEM,

		AST_FCALL,
		AST_TO_BITS,
		AST_TO_SIGNED,
		AST_TO_UNSIGNED,
		AST_SELFSZ,
		AST_CAST_SIZE,
		AST_CONCAT,
		AST_REPLICATE,
		AST_BIT_NOT,
		AST_BIT_AND,
		AST_BIT_OR,
		AST_BIT_XOR,
		AST_BIT_XNOR,
		AST_REDUCE_AND,
		AST_REDUCE_OR,
		AST_REDUCE_XOR,
		AST_REDUCE_XNOR,
		AST_REDUCE_BOOL,
		AST_SHIFT_LEFT,
		AST_SHIFT_RIGHT,
		AST_SHIFT_SLEFT,
		AST_SHIFT_SRIGHT,
		AST_SHIFTX,
		AST_SHIFT,
		AST_LT,
		AST_LE,
		AST_EQ,
		AST_NE,
		AST_EQX,
		AST_NEX,
		AST_GE,
		AST_GT,
		AST_ADD,
		AST_SUB,
		AST_MUL,
		AST_DIV,
		AST_MOD,
		AST_POW,
		AST_POS,
		AST_NEG,
		AST_LOGIC_AND,
		AST_LOGIC_OR,
		AST_LOGIC_NOT,
		AST_TERNARY,
		AST_MEMRD,
		AST_MEMWR,
		AST_MEMINIT,

		AST_TCALL,
		AST_ASSIGN,
		AST_CELL,
		AST_PRIMITIVE,
		AST_CELLARRAY,
		AST_ALWAYS,
		AST_INITIAL,
		AST_BLOCK,
		AST_ASSIGN_EQ,
		AST_ASSIGN_LE,
		AST_CASE,
		AST_COND,
		AST_CONDX,
		AST_CONDZ,
		AST_DEFAULT,
		AST_FOR,
		AST_WHILE,
		AST_REPEAT,

		AST_GENVAR,
		AST_GENFOR,
		AST_GENIF,
		AST_GENCASE,
		AST_GENBLOCK,
		AST_TECALL,

		AST_POSEDGE,
		AST_NEGEDGE,
		AST_EDGE,

		AST_INTERFACE,
		AST_INTERFACEPORT,
		AST_INTERFACEPORTTYPE,
		AST_MODPORT,
		AST_MODPORTMEMBER,
		AST_PACKAGE,

		AST_WIRETYPE,
		AST_TYPEDEF,
		AST_STRUCT,
		AST_UNION,
		AST_STRUCT_ITEM
	};

	struct AstSrcLocType {
		unsigned int first_line, last_line;
		unsigned int first_column, last_column;
		AstSrcLocType() : first_line(0), last_line(0), first_column(0), last_column(0) {}
		AstSrcLocType(int _first_line, int _first_column, int _last_line, int _last_column) : first_line(_first_line), last_line(_last_line), first_column(_first_column), last_column(_last_column) {}
	};

	// convert an node type to a string (e.g. for debug output)
	std::string type2str(AstNodeType type);

	// The AST is built using instances of this struct
	struct AstNode
	{
		// for dict<> and pool<>
		unsigned int hashidx_;
		unsigned int hash() const { return hashidx_; }

		// this nodes type
		AstNodeType type;

		// the list of child nodes for this node
		std::vector<AstNode*> children;

		// the list of attributes assigned to this node
		std::map<RTLIL::IdString, AstNode*> attributes;
		bool get_bool_attribute(RTLIL::IdString id);

		// node content - most of it is unused in most node types
		std::string str;
		std::vector<RTLIL::State> bits;
		bool is_input, is_output, is_reg, is_logic, is_signed, is_string, is_wand, is_wor, range_valid, range_swapped, was_checked, is_unsized, is_custom_type;
		int port_id, range_left, range_right;
		uint32_t integer;
		double realvalue;
		// set for IDs typed to an enumeration, not used
		bool is_enum;

		// if this is a multirange memory then this vector contains offset and length of each dimension
		std::vector<int> multirange_dimensions;
		std::vector<bool> multirange_swapped; // true if range is swapped, not used for structs

		// this is set by simplify and used during RTLIL generation
		AstNode *id2ast;

		// this is used by simplify to detect if basic analysis has been performed already on the node
		bool basic_prep;

		// this is used for ID references in RHS expressions that should use the "new" value for non-blocking assignments
		bool lookahead;

		// this is the original sourcecode location that resulted in this AST node
		// it is automatically set by the constructor using AST::current_filename and
		// the AST::get_line_num() callback function.
		std::string filename;
		AstSrcLocType location;

		// creating and deleting nodes
		AstNode(AstNodeType type = AST_NONE, AstNode *child1 = NULL, AstNode *child2 = NULL, AstNode *child3 = NULL);
		AstNode *clone() const;
		void cloneInto(AstNode *other) const;
		void delete_children();
		~AstNode();

		enum mem2reg_flags
		{
			/* status flags */
			MEM2REG_FL_ALL       = 0x00000001,
			MEM2REG_FL_ASYNC     = 0x00000002,
			MEM2REG_FL_INIT      = 0x00000004,

			/* candidate flags */
			MEM2REG_FL_FORCED    = 0x00000100,
			MEM2REG_FL_SET_INIT  = 0x00000200,
			MEM2REG_FL_SET_ELSE  = 0x00000400,
			MEM2REG_FL_SET_ASYNC = 0x00000800,
			MEM2REG_FL_EQ2       = 0x00001000,
			MEM2REG_FL_CMPLX_LHS = 0x00002000,
			MEM2REG_FL_CONST_LHS = 0x00004000,
			MEM2REG_FL_VAR_LHS   = 0x00008000,

			/* proc flags */
			MEM2REG_FL_EQ1       = 0x01000000,
		};

		// simplify() creates a simpler AST by unrolling for-loops, expanding generate blocks, etc.
		// it also sets the id2ast pointers so that identifier lookups are fast in genRTLIL()
		bool simplify(bool const_fold, bool at_zero, bool in_lvalue, int stage, int width_hint, bool sign_hint, bool in_param);
		void replace_result_wire_name_in_function(const std::string &from, const std::string &to);
		AstNode *readmem(bool is_readmemh, std::string mem_filename, AstNode *memory, int start_addr, int finish_addr, bool unconditional_init);
		void expand_genblock(const std::string &prefix);
		void label_genblks(std::set<std::string>& existing, int &counter);
		void mem2reg_as_needed_pass1(dict<AstNode*, pool<std::string>> &mem2reg_places,
				dict<AstNode*, uint32_t> &mem2reg_flags, dict<AstNode*, uint32_t> &proc_flags, uint32_t &status_flags);
		bool mem2reg_as_needed_pass2(pool<AstNode*> &mem2reg_set, AstNode *mod, AstNode *block, AstNode *&async_block);
		bool mem2reg_check(pool<AstNode*> &mem2reg_set);
		void mem2reg_remove(pool<AstNode*> &mem2reg_set, vector<AstNode*> &delnodes);
		void meminfo(int &mem_width, int &mem_size, int &addr_bits);
		bool detect_latch(const std::string &var);

		// additional functionality for evaluating constant functions
		struct varinfo_t {
			RTLIL::Const val;
			int offset;
			bool is_signed;
			AstNode *arg = nullptr;
			bool explicitly_sized;
		};
		bool has_const_only_constructs();
		bool replace_variables(std::map<std::string, varinfo_t> &variables, AstNode *fcall, bool must_succeed);
		AstNode *eval_const_function(AstNode *fcall, bool must_succeed);
		bool is_simple_const_expr();
		std::string process_format_str(const std::string &sformat, int next_arg, int stage, int width_hint, bool sign_hint);

		bool is_recursive_function() const;
		std::pair<AstNode*, AstNode*> get_tern_choice();

		// create a human-readable text representation of the AST (for debugging)
		void dumpAst(FILE *f, std::string indent) const;
		void dumpVlog(FILE *f, std::string indent) const;

		// used by genRTLIL() for detecting expression width and sign
		void detectSignWidthWorker(int &width_hint, bool &sign_hint, bool *found_real = NULL);
		void detectSignWidth(int &width_hint, bool &sign_hint, bool *found_real = NULL);

		// create RTLIL code for this AST node
		// for expressions the resulting signal vector is returned
		// all generated cell instances, etc. are written to the RTLIL::Module pointed to by AST_INTERNAL::current_module
		RTLIL::SigSpec genRTLIL(int width_hint = -1, bool sign_hint = false);
		RTLIL::SigSpec genWidthRTLIL(int width, const dict<RTLIL::SigBit, RTLIL::SigBit> *new_subst_ptr = NULL);

		// compare AST nodes
		bool operator==(const AstNode &other) const;
		bool operator!=(const AstNode &other) const;
		bool contains(const AstNode *other) const;

		// helper functions for creating AST nodes for constants
		static AstNode *mkconst_int(uint32_t v, bool is_signed, int width = 32);
		static AstNode *mkconst_bits(const std::vector<RTLIL::State> &v, bool is_signed, bool is_unsized);
		static AstNode *mkconst_bits(const std::vector<RTLIL::State> &v, bool is_signed);
		static AstNode *mkconst_str(const std::vector<RTLIL::State> &v);
		static AstNode *mkconst_str(const std::string &str);

		// helper function for creating sign-extended const objects
		RTLIL::Const bitsAsConst(int width, bool is_signed);
		RTLIL::Const bitsAsConst(int width = -1);
		RTLIL::Const bitsAsUnsizedConst(int width);
		RTLIL::Const asAttrConst();
		RTLIL::Const asParaConst();
		uint64_t asInt(bool is_signed);
		bool bits_only_01() const;
		bool asBool() const;

		// helper functions for real valued const eval
		int isConst() const; // return '1' for AST_CONSTANT and '2' for AST_REALVALUE
		double asReal(bool is_signed);
		RTLIL::Const realAsConst(int width);

		// helpers for enum
		void allocateDefaultEnumValues();
		void annotateTypedEnums(AstNode *template_node);

		// helpers for locations
		std::string loc_string() const;
	};

	// process an AST tree (ast must point to an AST_DESIGN node) and generate RTLIL code
	void process(RTLIL::Design *design, AstNode *ast, bool dump_ast1, bool dump_ast2, bool no_dump_ptr, bool dump_vlog1, bool dump_vlog2, bool dump_rtlil, bool nolatches, bool nomeminit,
			bool nomem2reg, bool mem2reg, bool noblackbox, bool lib, bool nowb, bool noopt, bool icells, bool pwires, bool nooverwrite, bool overwrite, bool defer, bool autowire);

	// parametric modules are supported directly by the AST library
	// therefore we need our own derivate of RTLIL::Module with overloaded virtual functions
	struct AstModule : RTLIL::Module {
		AstNode *ast;
		bool nolatches, nomeminit, nomem2reg, mem2reg, noblackbox, lib, nowb, noopt, icells, pwires, autowire;
		~AstModule() override;
		RTLIL::IdString derive(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, bool mayfail) override;
		RTLIL::IdString derive(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, const dict<RTLIL::IdString, RTLIL::Module*> &interfaces, const dict<RTLIL::IdString, RTLIL::IdString> &modports, bool mayfail) override;
		std::string derive_common(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Const> &parameters, AstNode **new_ast_out, bool quiet = false);
		void reprocess_module(RTLIL::Design *design, const dict<RTLIL::IdString, RTLIL::Module *> &local_interfaces) override;
		RTLIL::Module *clone() const override;
		void loadconfig() const;
	};

	// this must be set by the language frontend before parsing the sources
	// the AstNode constructor then uses current_filename and get_line_num()
	// to initialize the filename and linenum properties of new nodes
	extern std::string current_filename;
	extern void (*set_line_num)(int);
	extern int (*get_line_num)();

	// set set_line_num and get_line_num to internal dummy functions (done by simplify() and AstModule::derive
	// to control the filename and linenum properties of new nodes not generated by a frontend parser)
	void use_internal_line_num();

	// call a DPI function
	AstNode *dpi_call(const std::string &rtype, const std::string &fname, const std::vector<std::string> &argtypes, const std::vector<AstNode*> &args);

	// Helper functions related to handling SystemVerilog interfaces
	std::pair<std::string,std::string> split_modport_from_type(std::string name_type);
	AstNode * find_modport(AstNode *intf, std::string name);
	void explode_interface_port(AstNode *module_ast, RTLIL::Module * intfmodule, std::string intfname, AstNode *modport);

	// Helper for setting the src attribute.
	void set_src_attr(RTLIL::AttrObject *obj, const AstNode *ast);
}

namespace AST_INTERNAL
{
	// internal state variables
	extern bool flag_dump_ast1, flag_dump_ast2, flag_no_dump_ptr, flag_dump_rtlil, flag_nolatches, flag_nomeminit;
	extern bool flag_nomem2reg, flag_mem2reg, flag_lib, flag_noopt, flag_icells, flag_pwires, flag_autowire;
	extern AST::AstNode *current_ast, *current_ast_mod;
	extern std::map<std::string, AST::AstNode*> current_scope;
	extern const dict<RTLIL::SigBit, RTLIL::SigBit> *genRTLIL_subst_ptr;
	extern RTLIL::SigSpec ignoreThisSignalsInInitial;
	extern AST::AstNode *current_always, *current_top_block, *current_block, *current_block_child;
	extern RTLIL::Module *current_module;
	extern bool current_always_clocked;
	extern dict<std::string, int> current_memwr_count;
	extern dict<std::string, pool<int>> current_memwr_visible;
	struct LookaheadRewriter;
	struct ProcessGenerator;
}

YOSYS_NAMESPACE_END

#endif
