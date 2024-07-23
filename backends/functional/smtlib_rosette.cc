/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
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

#include "kernel/functionalir.h"
#include "kernel/yosys.h"
#include "kernel/sexpr.h"
#include <ctype.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using SExprUtil::list;

const char *reserved_keywords[] = {
	// reserved keywords from the racket spec
	"struct", "lambda", "values", "extract", "concat", "bv", "let", "define", "cons", "list", "read", "write",
	"stream", "error", "raise", "exit", "for", "for/list", "begin", "when", "unless", "module", "require",
	"provide", "apply", "if", "cond", "even", "odd", "any", "and", "or", "match", "match-define", "values",

	// reserved for our own purposes
	"inputs", "state", "name",
	nullptr
};

struct SmtrScope : public FunctionalTools::Scope<int> {
	SmtrScope() {
		for(const char **p = reserved_keywords; *p != nullptr; p++)
			reserve(*p);
	}
	bool is_character_legal(char c) override {
		return isascii(c) && (isalnum(c) || strchr("~!@$%^&*_-+=<>.?/", c));
	}
};

struct SmtrSort {
	FunctionalIR::Sort sort;
	SmtrSort(FunctionalIR::Sort sort) : sort(sort) {}
	SExpr to_sexpr() const {
		if(sort.is_memory()) {
			log_error("Memory not supported in Rosette printer");
		} else if(sort.is_signal()) {
			return list("bitvector", sort.width());
		} else {
			log_error("unknown sort");
		}
	}
};

class SmtrStruct {
	struct Field {
		SmtrSort sort;
		std::string accessor;
		std::string name;
	};
	idict<IdString> field_names;
	vector<Field> fields;
	SmtrScope &scope;
public:
	std::string name;
	// Not sure if this is actually necessary or not, so make it optional I guess?
	bool guarded = true;
	SmtrStruct(std::string name, SmtrScope &scope) : scope(scope), name(name) {}
	void insert(IdString field_name, SmtrSort sort) {
		field_names(field_name);
		auto base_name = RTLIL::unescape_id(field_name);
		auto accessor = name + "-" + base_name;
		fields.emplace_back(Field{sort, accessor, base_name});
	}
	void write_definition(SExprWriter &w) {
		std::vector<SExpr> field_list;
		for(const auto &field : fields) {
			field_list.emplace_back(field.name);
		}
		w.push();
		w.open(list("struct", name, field_list));
		if (guarded && field_names.size()) {
			w << SExpr("#:guard");
			field_list.emplace_back("name");
			w.open(list("lambda", field_list));
			w.open(list("values"));
			for (const auto &field : fields) {
				auto s = field.sort.sort.width();
				w << list("extract", s-1, 0, list("concat", list("bv", 0, s), field.name));
			}
		}
		w.pop();
	}
	template<typename Fn> void write_value(SExprWriter &w, Fn fn) {
		w.open(list(name));
		for(auto field_name : field_names) {
			w << fn(field_name);
			w.comment(RTLIL::unescape_id(field_name), true);
		}
		w.close();
	}
	SExpr access(SExpr record, IdString name) {
		size_t i = field_names.at(name);
		return list(fields[i].accessor, std::move(record));
	}
};

struct SmtrPrintVisitor : public FunctionalIR::AbstractVisitor<SExpr> {
	using Node = FunctionalIR::Node;
	std::function<SExpr(Node)> n;
	SmtrStruct &input_struct;
	SmtrStruct &state_struct;

	SmtrPrintVisitor(SmtrStruct &input_struct, SmtrStruct &state_struct) : input_struct(input_struct), state_struct(state_struct) {}

	SExpr from_bool(SExpr &&arg) {
		return list("bool->bitvector", std::move(arg));
	}
	SExpr to_bool(SExpr &&arg) {
		return list("bitvector->bool", std::move(arg));
	}
	SExpr to_list(SExpr &&arg) {
		return list("bitvector->bits", std::move(arg));
	}

	SExpr buf(Node, Node a) override { return n(a); }
	SExpr slice(Node, Node a, int offset, int out_width) override { return list("extract", offset + out_width - 1, offset, n(a)); }
	SExpr zero_extend(Node, Node a, int out_width) override { return list("zero-extend", n(a), list("bitvector", out_width)); }
	SExpr sign_extend(Node, Node a, int out_width) override { return list("sign-extend", n(a), list("bitvector", out_width)); }
	SExpr concat(Node, Node a, Node b) override { return list("concat", n(b), n(a)); }
	SExpr add(Node, Node a, Node b) override { return list("bvadd", n(a), n(b)); }
	SExpr sub(Node, Node a, Node b) override { return list("bvsub", n(a), n(b)); }
	SExpr mul(Node, Node a, Node b) override { return list("bvmul", n(a), n(b)); }
	SExpr unsigned_div(Node, Node a, Node b) override { return list("bvudiv", n(a), n(b)); }
	SExpr unsigned_mod(Node, Node a, Node b) override { return list("bvurem", n(a), n(b)); }
	SExpr bitwise_and(Node, Node a, Node b) override { return list("bvand", n(a), n(b)); }
	SExpr bitwise_or(Node, Node a, Node b) override { return list("bvor", n(a), n(b)); }
	SExpr bitwise_xor(Node, Node a, Node b) override { return list("bvxor", n(a), n(b)); }
	SExpr bitwise_not(Node, Node a) override { return list("bvnot", n(a)); }
	SExpr unary_minus(Node, Node a) override { return list("bvneg", n(a)); }
	SExpr reduce_and(Node, Node a) override { return list("apply", "bvand", to_list(n(a))); }
	SExpr reduce_or(Node, Node a) override { return list("apply", "bvor", to_list(n(a))); }
	SExpr reduce_xor(Node, Node a) override { return list("apply", "bvxor", to_list(n(a))); }
	SExpr equal(Node, Node a, Node b) override { return from_bool(list("bveq", n(a), n(b))); }
	SExpr not_equal(Node, Node a, Node b) override { return from_bool(list("not", list("bveq", n(a), n(b)))); }
	SExpr signed_greater_than(Node, Node a, Node b) override { return from_bool(list("bvsgt", n(a), n(b))); }
	SExpr signed_greater_equal(Node, Node a, Node b) override { return from_bool(list("bvsge", n(a), n(b))); }
	SExpr unsigned_greater_than(Node, Node a, Node b) override { return from_bool(list("bvugt", n(a), n(b))); }
	SExpr unsigned_greater_equal(Node, Node a, Node b) override { return from_bool(list("bvuge", n(a), n(b))); }

	SExpr extend(SExpr &&a, int in_width, int out_width) {
		if(in_width < out_width)
			return list("zero-extend", std::move(a), list("bitvector", out_width));
		else
			return std::move(a);
	}
	SExpr logical_shift_left(Node, Node a, Node b) override { return list("bvshl", n(a), extend(n(b), b.width(), a.width())); }
	SExpr logical_shift_right(Node, Node a, Node b) override { return list("bvlshr", n(a), extend(n(b), b.width(), a.width())); }
	SExpr arithmetic_shift_right(Node, Node a, Node b) override { return list("bvashr", n(a), extend(n(b), b.width(), a.width())); }
	SExpr mux(Node, Node a, Node b, Node s) override { return list("if", to_bool(n(s)), n(b), n(a)); }
	SExpr constant(Node, RTLIL::Const value) override { return list("bv", value.as_string(), value.size()); }
	SExpr memory_read(Node, Node mem, Node addr) override { log_error("memory_read not supported in Rosette printer"); }
	SExpr memory_write(Node, Node mem, Node addr, Node data) override { log_error("memory_write not supported in Rosette printer"); }

	SExpr input(Node, IdString name) override { return input_struct.access("inputs", name); }
	SExpr state(Node, IdString name) override { return state_struct.access("state", name); }
};

struct SmtrModule {
	FunctionalIR ir;
	SmtrScope scope;
	std::string name;
	
	SmtrStruct input_struct;
	SmtrStruct output_struct;
	SmtrStruct state_struct;

	SmtrModule(Module *module)
		: ir(FunctionalIR::from_module(module))
		, scope()
		, name(scope.unique_name(module->name))
		, input_struct(scope.unique_name(module->name.str() + "_Inputs"), scope)
		, output_struct(scope.unique_name(module->name.str() + "_Outputs"), scope)
		, state_struct(scope.unique_name(module->name.str() + "_State"), scope)
	{
		for (const auto &input : ir.inputs())
			input_struct.insert(input.first, input.second);
		for (const auto &output : ir.outputs())
			output_struct.insert(output.first, output.second);
		for (const auto &state : ir.state())
			state_struct.insert(state.first, state.second);
	}

	void write(std::ostream &out)
	{    
		SExprWriter w(out);

		w << SExpr("#lang rosette\n");

		input_struct.write_definition(w);
		output_struct.write_definition(w);
		state_struct.write_definition(w);

		w.push();
		w.open(list("define", list(name, "inputs", "state")));
		auto inlined = [&](FunctionalIR::Node n) {
			return n.fn() == FunctionalIR::Fn::constant;
		};
		SmtrPrintVisitor visitor(input_struct, state_struct);
		auto node_to_sexpr = [&](FunctionalIR::Node n) -> SExpr {
			if(inlined(n))
				return n.visit(visitor);
			else
				return scope(n.id(), n.name());
		};
		visitor.n = node_to_sexpr;
		for(auto n : ir)
			if(!inlined(n)) {
				w.open(list("let", list(list(node_to_sexpr(n), n.visit(visitor)))), false);
				w.comment(SmtrSort(n.sort()).to_sexpr().to_string(), true);
			}
		w.open(list("cons"));
		output_struct.write_value(w, [&](IdString name) { return node_to_sexpr(ir.get_output_node(name)); });
		state_struct.write_value(w, [&](IdString name) { return node_to_sexpr(ir.get_state_next_node(name)); });
		w.pop();
	}
};

struct FunctionalSmtrBackend : public Backend {
	FunctionalSmtrBackend() : Backend("functional_rosette", "Generate Rosette compatible Racket from Functional IR") {}

	void help() override { log("\nFunctional Rosette Backend.\n\n"); }

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing Functional Rosette Backend.\n");

		size_t argidx = 1;
		extra_args(f, filename, args, argidx, design);

		for (auto module : design->selected_modules()) {
			log("Processing module `%s`.\n", module->name.c_str());
			SmtrModule smtr(module);
			smtr.write(*f);
		}
	}
} FunctionalSmtrBackend;

PRIVATE_NAMESPACE_END
