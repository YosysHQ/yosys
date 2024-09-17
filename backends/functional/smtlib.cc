/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
 *  Copyright (C) 2024 National Technology and Engineering Solutions of Sandia, LLC
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

#include "kernel/functional.h"
#include "kernel/yosys.h"
#include "kernel/sexpr.h"
#include <ctype.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using SExprUtil::list;

const char *reserved_keywords[] = {
	// reserved keywords from the smtlib spec
	"BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "_", "!", "as", "let", "exists", "forall", "match", "par",
	"assert", "check-sat", "check-sat-assuming", "declare-const", "declare-datatype", "declare-datatypes",
	"declare-fun", "declare-sort", "define-fun", "define-fun-rec", "define-funs-rec", "define-sort",
	"exit", "get-assertions", "symbol", "sort", "get-assignment", "get-info", "get-model",
	"get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core", "get-value",
	"pop", "push", "reset", "reset-assertions", "set-info", "set-logic", "set-option",

	// reserved for our own purposes
	"pair", "Pair", "first", "second",
	"inputs", "state",
	nullptr
};

struct SmtScope : public Functional::Scope<int> {
	SmtScope() {
		for(const char **p = reserved_keywords; *p != nullptr; p++)
			reserve(*p);
	}
	bool is_character_legal(char c, int index) override {
		return isascii(c) && (isalpha(c) || (isdigit(c) && index > 0) || strchr("~!@$%^&*_-+=<>.?/", c));
	}
};

struct SmtSort {
	Functional::Sort sort;
	SmtSort(Functional::Sort sort) : sort(sort) {}
	SExpr to_sexpr() const {
		if(sort.is_memory()) {
			return list("Array", list("_", "BitVec", sort.addr_width()), list("_", "BitVec", sort.data_width()));
		} else if(sort.is_signal()) {
			return list("_", "BitVec", sort.width());
		} else {
			log_error("unknown sort");
		}
	}
};

class SmtStruct {
	struct Field {
		SmtSort sort;
		std::string accessor;
	};
	idict<IdString> field_names;
	vector<Field> fields;
	SmtScope &scope;
public:
	std::string name;
	SmtStruct(std::string name, SmtScope &scope) : scope(scope), name(name) {}
	void insert(IdString field_name, SmtSort sort) {
		field_names(field_name);
		auto accessor = scope.unique_name("\\" + name + "_" + RTLIL::unescape_id(field_name));
		fields.emplace_back(Field{sort, accessor});
	}
	void write_definition(SExprWriter &w) {
		w.open(list("declare-datatype", name));
		w.open(list());
		w.open(list(name));
		for(const auto &field : fields)
			w << list(field.accessor, field.sort.to_sexpr());
		w.close(3);
	}
	template<typename Fn> void write_value(SExprWriter &w, Fn fn) {
		if(field_names.empty()) {
			// Zero-argument constructors in SMTLIB must not be called as functions.
			w << name;
		} else {
			w.open(list(name));
			for(auto field_name : field_names) {
				w << fn(field_name);
				w.comment(RTLIL::unescape_id(field_name), true);
			}
			w.close();
		}
	}
	SExpr access(SExpr record, IdString name) {
		size_t i = field_names.at(name);
		return list(fields[i].accessor, std::move(record));
	}
};

std::string smt_const(RTLIL::Const const &c) {
	std::string s = "#b";
	for(int i = c.size(); i-- > 0; )
		s += c[i] == State::S1 ? '1' : '0';
	return s;
}

struct SmtPrintVisitor : public Functional::AbstractVisitor<SExpr> {
	using Node = Functional::Node;
	std::function<SExpr(Node)> n;
	SmtStruct &input_struct;
	SmtStruct &state_struct;

	SmtPrintVisitor(SmtStruct &input_struct, SmtStruct &state_struct) : input_struct(input_struct), state_struct(state_struct) {}

	SExpr from_bool(SExpr &&arg) {
		return list("ite", std::move(arg), "#b1", "#b0");
	}
	SExpr to_bool(SExpr &&arg) {
		return list("=", std::move(arg), "#b1");
	}
	SExpr extract(SExpr &&arg, int offset, int out_width = 1) {
		return list(list("_", "extract", offset + out_width - 1, offset), std::move(arg));
	}

	SExpr buf(Node, Node a) override { return n(a); }
	SExpr slice(Node, Node a, int offset, int out_width) override { return extract(n(a), offset, out_width); }
	SExpr zero_extend(Node, Node a, int out_width) override { return list(list("_", "zero_extend", out_width - a.width()), n(a)); }
	SExpr sign_extend(Node, Node a, int out_width) override { return list(list("_", "sign_extend", out_width - a.width()), n(a)); }
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
	SExpr reduce_and(Node, Node a) override { return from_bool(list("=", n(a), smt_const(RTLIL::Const(State::S1, a.width())))); }
	SExpr reduce_or(Node, Node a) override { return from_bool(list("distinct", n(a), smt_const(RTLIL::Const(State::S0, a.width())))); }
	SExpr reduce_xor(Node, Node a) override {
		vector<SExpr> s { "bvxor" };
		for(int i = 0; i < a.width(); i++)
			s.push_back(extract(n(a), i));
		return s;
	}
	SExpr equal(Node, Node a, Node b) override { return from_bool(list("=", n(a), n(b))); }
	SExpr not_equal(Node, Node a, Node b) override { return from_bool(list("distinct", n(a), n(b))); }
	SExpr signed_greater_than(Node, Node a, Node b) override { return from_bool(list("bvsgt", n(a), n(b))); }
	SExpr signed_greater_equal(Node, Node a, Node b) override { return from_bool(list("bvsge", n(a), n(b))); }
	SExpr unsigned_greater_than(Node, Node a, Node b) override { return from_bool(list("bvugt", n(a), n(b))); }
	SExpr unsigned_greater_equal(Node, Node a, Node b) override { return from_bool(list("bvuge", n(a), n(b))); }

	SExpr extend(SExpr &&a, int in_width, int out_width) {
		if(in_width < out_width)
			return list(list("_", "zero_extend", out_width - in_width), std::move(a));
		else
			return std::move(a);
	}
	SExpr logical_shift_left(Node, Node a, Node b) override { return list("bvshl", n(a), extend(n(b), b.width(), a.width())); }
	SExpr logical_shift_right(Node, Node a, Node b) override { return list("bvlshr", n(a), extend(n(b), b.width(), a.width())); }
	SExpr arithmetic_shift_right(Node, Node a, Node b) override { return list("bvashr", n(a), extend(n(b), b.width(), a.width())); }
	SExpr mux(Node, Node a, Node b, Node s) override { return list("ite", to_bool(n(s)), n(b), n(a)); }
	SExpr constant(Node, RTLIL::Const const &value) override { return smt_const(value); }
	SExpr memory_read(Node, Node mem, Node addr) override { return list("select", n(mem), n(addr)); }
	SExpr memory_write(Node, Node mem, Node addr, Node data) override { return list("store", n(mem), n(addr), n(data)); }

	SExpr input(Node, IdString name, IdString kind) override { log_assert(kind == ID($input)); return input_struct.access("inputs", name); }
	SExpr state(Node, IdString name, IdString kind) override { log_assert(kind == ID($state)); return state_struct.access("state", name); }
};

struct SmtModule {
	Functional::IR ir;
	SmtScope scope;
	std::string name;
	
	SmtStruct input_struct;
	SmtStruct output_struct;
	SmtStruct state_struct;

	SmtModule(Module *module)
		: ir(Functional::IR::from_module(module))
		, scope()
		, name(scope.unique_name(module->name))
		, input_struct(scope.unique_name(module->name.str() + "_Inputs"), scope)
		, output_struct(scope.unique_name(module->name.str() + "_Outputs"), scope)
		, state_struct(scope.unique_name(module->name.str() + "_State"), scope)
	{
		scope.reserve(name + "-initial");
		for (auto input : ir.inputs())
			input_struct.insert(input->name, input->sort);
		for (auto output : ir.outputs())
			output_struct.insert(output->name, output->sort);
		for (auto state : ir.states())
			state_struct.insert(state->name, state->sort);
	}

	void write_eval(SExprWriter &w)
	{
		w.push();
		w.open(list("define-fun", name,
			list(list("inputs", input_struct.name),
			     list("state", state_struct.name)),
			list("Pair", output_struct.name, state_struct.name)));
		auto inlined = [&](Functional::Node n) {
			return n.fn() == Functional::Fn::constant;
		};
		SmtPrintVisitor visitor(input_struct, state_struct);
		auto node_to_sexpr = [&](Functional::Node n) -> SExpr {
			if(inlined(n))
				return n.visit(visitor);
			else
				return scope(n.id(), n.name());
		};
		visitor.n = node_to_sexpr;
		for(auto n : ir)
			if(!inlined(n)) {
				w.open(list("let", list(list(node_to_sexpr(n), n.visit(visitor)))), false);
				w.comment(SmtSort(n.sort()).to_sexpr().to_string(), true);
			}
		w.open(list("pair"));
		output_struct.write_value(w, [&](IdString name) { return node_to_sexpr(ir.output(name).value()); });
		state_struct.write_value(w, [&](IdString name) { return node_to_sexpr(ir.state(name).next_value()); });
		w.pop();
	}

	void write_initial(SExprWriter &w)
	{
		std::string initial = name + "-initial";
		w << list("declare-const", initial, state_struct.name);
		for (auto state : ir.states()) {
			if(state->sort.is_signal())
				w << list("assert", list("=", state_struct.access(initial, state->name), smt_const(state->initial_value_signal())));
			else if(state->sort.is_memory()) {
				const auto &contents = state->initial_value_memory();
				for(int i = 0; i < 1<<state->sort.addr_width(); i++) {
					auto addr = smt_const(RTLIL::Const(i, state->sort.addr_width()));
					w << list("assert", list("=", list("select", state_struct.access(initial, state->name), addr), smt_const(contents[i])));
				}
			}
		}
	}

	void write(std::ostream &out)
	{    
		SExprWriter w(out);

		input_struct.write_definition(w);
		output_struct.write_definition(w);
		state_struct.write_definition(w);

		w << list("declare-datatypes",
			list(list("Pair", 2)),
			list(list("par", list("X", "Y"), list(list("pair", list("first", "X"), list("second", "Y"))))));
		
		write_eval(w);
		write_initial(w);
	}
};

struct FunctionalSmtBackend : public Backend {
	FunctionalSmtBackend() : Backend("functional_smt2", "Generate SMT-LIB from Functional IR") {}

	void help() override { log("\nFunctional SMT Backend.\n\n"); }

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing Functional SMT Backend.\n");

		size_t argidx = 1;
		extra_args(f, filename, args, argidx, design);

		for (auto module : design->selected_modules()) {
			log("Processing module `%s`.\n", module->name.c_str());
			SmtModule smt(module);
			smt.write(*f);
		}
	}
} FunctionalSmtBackend;

PRIVATE_NAMESPACE_END
