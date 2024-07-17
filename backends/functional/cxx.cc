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

#include "kernel/yosys.h"
#include "kernel/functionalir.h"
#include <ctype.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

const char *reserved_keywords[] = {
	"alignas","alignof","and","and_eq","asm","atomic_cancel","atomic_commit",
	"atomic_noexcept","auto","bitand","bitor","bool","break","case",
	"catch","char","char16_t","char32_t","char8_t","class","co_await",
	"co_return","co_yield","compl","concept","const","const_cast","consteval",
	"constexpr","constinit","continue","decltype","default","delete",
	"do","double","dynamic_cast","else","enum","explicit","export",
	"extern","false","float","for","friend","goto","if","inline",
	"int","long","mutable","namespace","new","noexcept","not","not_eq",
	"nullptr","operator","or","or_eq","private","protected","public",
	"reflexpr","register","reinterpret_cast","requires","return","short",
	"signed","sizeof","static","static_log_assert","static_cast","struct",
	"switch","synchronized","template","this","thread_local","throw",
	"true","try","typedef","typeid","typename","union","unsigned",
	"using","virtual","void","volatile","wchar_t","while","xor","xor_eq",
	nullptr
};

template<typename Id> struct CxxScope : public FunctionalTools::Scope<Id> {
	CxxScope() {
		for(const char **p = reserved_keywords; *p != nullptr; p++)
			this->reserve(*p);
	}
	bool is_character_legal(char c) override {
		return isascii(c) && (isalnum(c) || c == '_' || c == '$');
	}
};

struct CxxType {
	FunctionalIR::Sort sort;
	CxxType(FunctionalIR::Sort sort) : sort(sort) {}
	std::string to_string() const {
		if(sort.is_memory()) {
			return stringf("Memory<%d, %d>", sort.addr_width(), sort.data_width());
		} else if(sort.is_signal()) {
			return stringf("Signal<%d>", sort.width());
		} else {
			log_error("unknown sort");
		}
	}
};

using CxxWriter = FunctionalTools::Writer;

struct CxxStruct {
  std::string name;
  dict<IdString, CxxType> types;
  CxxScope<IdString> scope;
  CxxStruct(std::string name)
    : name(name) {
    scope.reserve("fn");
    scope.reserve("visit");
  }
  void insert(IdString name, CxxType type) {
    scope(name, name);
    types.insert({name, type});
  }
  void print(CxxWriter &f) {
    f.print("\tstruct {} {{\n", name);
    for (auto p : types) {
      f.print("\t\t{} {};\n", p.second.to_string(), scope(p.first, p.first));
    }
    f.print("\n\t\ttemplate <typename T> void visit(T &&fn) {{\n");
    for (auto p : types) {
      f.print("\t\t\tfn(\"{}\", {});\n", RTLIL::unescape_id(p.first), scope(p.first, p.first));
    }
    f.print("\t\t}}\n");
    f.print("\t}};\n\n");
  };
  std::string operator[](IdString field) {
    return scope(field, field);
  }
};

template<class NodePrinter> struct CxxPrintVisitor : public FunctionalIR::AbstractVisitor<void> {
	using Node = FunctionalIR::Node;
	CxxWriter &f;
	NodePrinter np;
	CxxStruct &input_struct;
	CxxStruct &state_struct;
	CxxPrintVisitor(CxxWriter &f, NodePrinter np, CxxStruct &input_struct, CxxStruct &state_struct) : f(f), np(np), input_struct(input_struct), state_struct(state_struct) { }
	template<typename... Args> void print(const char *fmt, Args&&... args) {
		f.print_with(np, fmt, std::forward<Args>(args)...);
	}
	void buf(Node, Node n) override { print("{}", n); }
	void slice(Node, Node a, int offset, int out_width) override { print("{0}.slice<{2}>({1})", a, offset, out_width); }
	void zero_extend(Node, Node a, int out_width) override { print("{}.zero_extend<{}>()", a, out_width); }
	void sign_extend(Node, Node a, int out_width) override { print("{}.sign_extend<{}>()", a, out_width); }
	void concat(Node, Node a, Node b) override { print("{}.concat({})", a, b); }
	void add(Node, Node a, Node b) override { print("{} + {}", a, b); }
	void sub(Node, Node a, Node b) override { print("{} - {}", a, b); }
	void mul(Node, Node a, Node b) override { print("{} * {}", a, b); }
	void unsigned_div(Node, Node a, Node b) override { print("{} / {}", a, b); }
	void unsigned_mod(Node, Node a, Node b) override { print("{} % {}", a, b); }
	void bitwise_and(Node, Node a, Node b) override { print("{} & {}", a, b); }
	void bitwise_or(Node, Node a, Node b) override { print("{} | {}", a, b); }
	void bitwise_xor(Node, Node a, Node b) override { print("{} ^ {}", a, b); }
	void bitwise_not(Node, Node a) override { print("~{}", a); }
	void unary_minus(Node, Node a) override { print("-{}", a); }
	void reduce_and(Node, Node a) override { print("{}.all()", a); }
	void reduce_or(Node, Node a) override { print("{}.any()", a); }
	void reduce_xor(Node, Node a) override { print("{}.parity()", a); }
	void equal(Node, Node a, Node b) override { print("{} == {}", a, b); }
	void not_equal(Node, Node a, Node b) override { print("{} != {}", a, b); }
	void signed_greater_than(Node, Node a, Node b) override { print("{}.signed_greater_than({})", a, b); }
	void signed_greater_equal(Node, Node a, Node b) override { print("{}.signed_greater_equal({})", a, b); }
	void unsigned_greater_than(Node, Node a, Node b) override { print("{} > {}", a, b); }
	void unsigned_greater_equal(Node, Node a, Node b) override { print("{} >= {}", a, b); }
	void logical_shift_left(Node, Node a, Node b) override { print("{} << {}", a, b); }
	void logical_shift_right(Node, Node a, Node b) override { print("{} >> {}", a, b); }
	void arithmetic_shift_right(Node, Node a, Node b) override { print("{}.arithmetic_shift_right({})", a, b); }
	void mux(Node, Node a, Node b, Node s) override { print("{2}.any() ? {1} : {0}", a, b, s); }
	void pmux(Node, Node a, Node b, Node s) override { print("{0}.pmux({1}, {2})", a, b, s); }
	void constant(Node, RTLIL::Const value) override {
		std::stringstream ss;
		bool multiple = value.size() > 32;
		ss << "Signal<" << value.size() << ">(" << std::hex << std::showbase;
		if(multiple) ss << "{";
		while(value.size() > 32) {
			ss << value.as_int() << ", ";
			value = value.extract(32, value.size() - 32);
		}
		ss << value.as_int();
		if(multiple) ss << "}";
		ss << ")";
		print("{}", ss.str());
	}
	void input(Node, IdString name) override { print("input.{}", input_struct[name]); }
	void state(Node, IdString name) override { print("current_state.{}", state_struct[name]); }
	void memory_read(Node, Node mem, Node addr) override { print("{}.read({})", mem, addr); }
	void memory_write(Node, Node mem, Node addr, Node data) override { print("{}.write({}, {})", mem, addr, data); }
	void undriven(Node, int width) override { print("Signal<{}>(0)", width); }
};

struct CxxModule {
	FunctionalIR ir;
	CxxStruct input_struct, output_struct, state_struct;
	std::string module_name;

	explicit CxxModule(Module *module) :
		ir(FunctionalIR::from_module(module)),
		input_struct("Inputs"),
		output_struct("Outputs"),
		state_struct("State")
	{
		for (auto [name, sort] : ir.inputs())
			input_struct.insert(name, sort);
		for (auto [name, sort] : ir.outputs())
			output_struct.insert(name, sort);
		for (auto [name, sort] : ir.state())
			state_struct.insert(name, sort);
		module_name = CxxScope<int>().unique_name(module->name);
	}
	void write_header(CxxWriter &f) {
		f.print("#include \"sim.h\"\n\n");
	}
	void write_struct_def(CxxWriter &f) {
		f.print("struct {} {{\n", module_name);
		input_struct.print(f);
		output_struct.print(f);
		state_struct.print(f);
		f.print("\tstatic void eval(Inputs const &, Outputs &, State const &, State &);\n");
		f.print("}};\n\n");
	}
	void write_eval_def(CxxWriter &f) {
		f.print("void {0}::eval({0}::Inputs const &input, {0}::Outputs &output, {0}::State const &current_state, {0}::State &next_state)\n{{\n", module_name);
		CxxScope<int> locals;
		locals.reserve("input");
		locals.reserve("output");
		locals.reserve("current_state");
		locals.reserve("next_state");
		auto node_name = [&](FunctionalIR::Node n) { return locals(n.id(), n.name()); };
		CxxPrintVisitor printVisitor(f, node_name, input_struct, state_struct);
		for (auto node : ir) {
			f.print("\t{} {} = ", CxxType(node.sort()).to_string(), node_name(node));
			node.visit(printVisitor);
			f.print(";\n");
		}
		for (auto [name, sort] : ir.state())
			f.print("\tnext_state.{} = {};\n", state_struct[name], node_name(ir.get_state_next_node(name)));
		for (auto [name, sort] : ir.outputs())
			f.print("\toutput.{} = {};\n", output_struct[name], node_name(ir.get_output_node(name)));
		f.print("}}\n");
	}
};

struct FunctionalCxxBackend : public Backend
{
	FunctionalCxxBackend() : Backend("functional_cxx", "convert design to C++ using the functional backend") {}

    void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
    }

	void printCxx(std::ostream &stream, std::string, Module *module)
	{
		CxxWriter f(stream);
		CxxModule mod(module);
		mod.write_header(f);
		mod.write_struct_def(f);
		mod.write_eval_def(f);
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
        log_header(design, "Executing Functional C++ backend.\n");

		size_t argidx = 1;
		extra_args(f, filename, args, argidx, design);

		for (auto module : design->selected_modules()) {
            log("Dumping module `%s'.\n", module->name.c_str());
			printCxx(*f, filename, module);
		}
	}
} FunctionalCxxBackend;

PRIVATE_NAMESPACE_END
