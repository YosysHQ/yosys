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
	// reserved keywords from the racket spec
	"struct", "lambda", "values", "extract", "concat", "bv", "let", "define", "cons", "list", "read", "write",
	"stream", "error", "raise", "exit", "for", "begin", "when", "unless", "module", "require", "provide", "apply",
	"if", "cond", "even", "odd", "any", "and", "or", "match", "command-line", "ffi-lib", "thread", "kill", "sync",
	"future", "touch", "subprocess", "make-custodian", "custodian-shutdown-all", "current-custodian", "make", "tcp",
	"connect", "prepare", "malloc", "free", "_fun", "_cprocedure", "build", "path", "file", "peek", "bytes",
	"flush", "with", "lexer", "parser", "syntax", "interface", "send", "make-object", "new", "instantiate",
	"define-generics", "set",

	// reserved for our own purposes
	"inputs", "state", "name",
	nullptr
};

struct SmtrScope : public Functional::Scope<int> {
	SmtrScope() {
		for(const char **p = reserved_keywords; *p != nullptr; p++)
			reserve(*p);
	}
	bool is_character_legal(char c, int index) override {
		return isascii(c) && (isalpha(c) || (isdigit(c) && index > 0) || strchr("@$%^&_+=.", c));
	}
};

struct SmtrSort {
	Functional::Sort sort;
	SmtrSort(Functional::Sort sort) : sort(sort) {}
	SExpr to_sexpr() const {
		if(sort.is_memory()) {
			return list("list", list("bitvector", sort.addr_width()), list("bitvector", sort.data_width()));
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
	SmtrScope &global_scope;
	SmtrScope local_scope;
public:
	std::string name;
	SmtrStruct(std::string name, SmtrScope &scope) : global_scope(scope), local_scope(), name(name) {}
	void insert(IdString field_name, SmtrSort sort) {
		field_names(field_name);
		auto base_name = local_scope.unique_name(field_name);
		auto accessor = name + "-" + base_name;
		global_scope.reserve(accessor);
		fields.emplace_back(Field{sort, accessor, base_name});
	}
	void write_definition(SExprWriter &w) {
		vector<SExpr> field_list;
		for(const auto &field : fields) {
			field_list.emplace_back(field.name);
		}
		w.push();
		w.open(list("struct", name, field_list, "#:transparent"));
		if (field_names.size()) {
			for (const auto &field : fields) {
				auto bv_type = field.sort.to_sexpr();
				w.comment(field.name + " " + bv_type.to_string());
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

std::string smt_const(RTLIL::Const const &c) {
	std::string s = "#b";
	for(int i = c.size(); i-- > 0; )
		s += c[i] == State::S1 ? '1' : '0';
	return s;
}

struct SmtrPrintVisitor : public Functional::AbstractVisitor<SExpr> {
	using Node = Functional::Node;
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
	SExpr constant(Node, RTLIL::Const const& value) override { return list("bv", smt_const(value), value.size()); }
	SExpr memory_read(Node, Node mem, Node addr) override { return list("list-ref-bv", n(mem), n(addr)); }
	SExpr memory_write(Node, Node mem, Node addr, Node data) override { return list("list-set-bv", n(mem), n(addr), n(data)); }

	SExpr input(Node, IdString name, IdString kind) override { log_assert(kind == ID($input)); return input_struct.access("inputs", name); }
	SExpr state(Node, IdString name, IdString kind) override { log_assert(kind == ID($state)); return state_struct.access("state", name); }
};

struct SmtrModule {
	Functional::IR ir;
	SmtrScope scope;
	std::string name;
	
	SmtrStruct input_struct;
	SmtrStruct output_struct;
	SmtrStruct state_struct;

	SmtrModule(Module *module)
		: ir(Functional::IR::from_module(module))
		, scope()
		, name(scope.unique_name(module->name))
		, input_struct(scope.unique_name(module->name.str() + "_Inputs"), scope)
		, output_struct(scope.unique_name(module->name.str() + "_Outputs"), scope)
		, state_struct(scope.unique_name(module->name.str() + "_State"), scope)
	{
		scope.reserve(name + "_initial");
		for (auto input : ir.inputs())
			input_struct.insert(input->name, input->sort);
		for (auto output : ir.outputs())
			output_struct.insert(output->name, output->sort);
		for (auto state : ir.states())
			state_struct.insert(state->name, state->sort);
	}

	void write(std::ostream &out)
	{    
		SExprWriter w(out);

		input_struct.write_definition(w);
		output_struct.write_definition(w);
		state_struct.write_definition(w);

		w.push();
		w.open(list("define", list(name, "inputs", "state")));
		auto inlined = [&](Functional::Node n) {
			return n.fn() == Functional::Fn::constant;
		};
		SmtrPrintVisitor visitor(input_struct, state_struct);
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
				w.comment(SmtrSort(n.sort()).to_sexpr().to_string(), true);
			}
		w.open(list("cons"));
		output_struct.write_value(w, [&](IdString name) { return node_to_sexpr(ir.output(name).value()); });
		state_struct.write_value(w, [&](IdString name) { return node_to_sexpr(ir.state(name).next_value()); });
		w.pop();

		w.push();
		auto initial = name + "_initial";
		w.open(list("define", initial));
		w.open(list(state_struct.name));
		for (auto state : ir.states()) {
			if (state->sort.is_signal())
				w << list("bv", smt_const(state->initial_value_signal()), state->sort.width());
			else if (state->sort.is_memory()) {
				const auto &contents = state->initial_value_memory();
				w.open(list("list"));
				for(int i = 0; i < 1<<state->sort.addr_width(); i++) {
					w << list("bv", smt_const(contents[i]), state->sort.data_width());
				}
				w.close();
			}
		}
		w.pop();
	}
};

struct FunctionalSmtrBackend : public Backend {
	FunctionalSmtrBackend() : Backend("functional_rosette", "Generate Rosette compatible Racket from Functional IR") {}

    	void help() override {
        	//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_functional_rosette [options] [selection] [filename]\n");
		log("\n");
		log("Functional Rosette Backend.\n");
		log("\n");
		log("    -provides\n");
		log("        include 'provide' statement(s) for loading output as a module\n");
		log("\n");
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		auto provides = false;

		log_header(design, "Executing Functional Rosette Backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-provides")
				provides = true;
			else
				break;
		}
		extra_args(f, filename, args, argidx);

		*f << "#lang rosette/safe\n";
		if (provides) {
			*f << "(provide (all-defined-out))\n";
		}

		for (auto module : design->selected_modules()) {
			log("Processing module `%s`.\n", module->name.c_str());
			SmtrModule smtr(module);
			smtr.write(*f);
		}
	}
} FunctionalSmtrBackend;

PRIVATE_NAMESPACE_END
