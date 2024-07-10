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
#include <ctype.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

const char *reserved_keywords[] = {
	"BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "_", "!", "as", "let", "exists", "forall", "match", "par",
	"assert", "check-sat", "check-sat-assuming", "declare-const", "declare-datatype", "declare-datatypes",
	"declare-fun", "declare-sort", "define-fun", "define-fun-rec", "define-funs-rec", "define-sort",
	"exit", "get-assertions", "symbol", "sort", "get-assignment", "get-info", "get-model",
	"get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core", "get-value",
	"pop", "push", "reset", "reset-assertions", "set-info", "set-logic", "set-option",

	"pair", "Pair", "first", "second",
	"inputs", "state",
	nullptr
};

struct SmtScope : public FunctionalTools::Scope<int> {
	SmtScope() {
		for(const char **p = reserved_keywords; *p != nullptr; p++)
			reserve(*p);
	}
	bool is_character_legal(char c) override {
		return isascii(c) && (isalnum(c) || strchr("~!@$%^&*_-+=<>.?/", c));
	}
};

class SExpr {
public:
	std::variant<std::vector<SExpr>, std::string> _v;
public:
	SExpr(std::string a) : _v(std::move(a)) {}
    SExpr(const char *a) : _v(a) {}
	SExpr(int n) : _v(std::to_string(n)) {}
	SExpr(std::vector<SExpr> const &l) : _v(l) {}
	SExpr(std::vector<SExpr> &&l) : _v(std::move(l)) {}
    bool is_atom() const { return std::holds_alternative<std::string>(_v); }
    std::string const &atom() const { return std::get<std::string>(_v); }
    bool is_list() const { return std::holds_alternative<std::vector<SExpr>>(_v); }
    std::vector<SExpr> const &list() const { return std::get<std::vector<SExpr>>(_v); }
	friend std::ostream &operator<<(std::ostream &os, SExpr const &sexpr) {
		if(sexpr.is_atom())
			os << sexpr.atom();
		else if(sexpr.is_list()){
			os << "(";
			auto l = sexpr.list();
			for(size_t i = 0; i < l.size(); i++) {
				if(i > 0) os << " ";
				os << l[i];
			}
			os << ")";
		}else
			os << "<invalid>";
		return os;
	}
	std::string to_string() const {
		std::stringstream ss;
		ss << *this;
		return ss.str();
	}
};
template<typename... Args> SExpr list(Args&&... args) {
	return SExpr(std::vector<SExpr>{std::forward<Args>(args)...});
}

class SExprWriter {
    std::ostream &os;
    int _max_line_width;
    int _indent = 0;
    int _pos = 0;
    bool _pending_nl = false;
	vector<bool> _unclosed;
	vector<size_t> _unclosed_stack;
	void nl_if_pending() {
		if(_pending_nl) {
            os << '\n';
            _pos = 0;
            _pending_nl = false;
		}
	}
    void puts(std::string const &s) {
        if(s.empty()) return;
		nl_if_pending();
        for(auto c : s) {
            if(c == '\n') {
                os << c;
                _pos = 0;
            } else {
                if(_pos == 0) {
                    for(int i = 0; i < _indent; i++)
                        os << "  ";
                    _pos = 2 * _indent;
                }
                os << c;
                _pos++;
            }
        }
    }
    int width(SExpr const &sexpr) {
        if(sexpr.is_atom())
            return sexpr.atom().size();
        else if(sexpr.is_list()) {
            int w = 2;
            for(auto arg : sexpr.list())
                w += width(arg);
            if(sexpr.list().size() > 1)
                w += sexpr.list().size() - 1;
            return w;
        } else
            return 0;
    }
    void print(SExpr const &sexpr, bool close = true, bool indent_rest = true) {
        if(sexpr.is_atom())
            puts(sexpr.atom());
        else if(sexpr.is_list()) {
            auto args = sexpr.list();
			puts("(");
			bool vertical = args.size() > 1 && _pos + width(sexpr) > _max_line_width;
			if(vertical) _indent++;
			for(size_t i = 0; i < args.size(); i++) {
				if(i > 0) puts(vertical ? "\n" : " ");
				print(args[i]);
			}
			_indent += (!close && indent_rest) - vertical;
			if(close)
				puts(")");
			else {
				_unclosed.push_back(indent_rest);
				_pending_nl = true;
			}
        }else
            log_error("shouldn't happen in SExprWriter::print");
    }
public:
    SExprWriter(std::ostream &os, int max_line_width = 80)
        : os(os)
        , _max_line_width(max_line_width)
    {}
    void open(SExpr const &sexpr, bool indent_rest = true) {
        log_assert(sexpr.is_list());
        print(sexpr, false, indent_rest);
    }
    void close(size_t n = 1) {
		log_assert(_unclosed.size() - (_unclosed_stack.empty() ? 0 : _unclosed_stack.back()) >= n);
		while(n-- > 0) {
			bool indented = _unclosed[_unclosed.size() - 1];
			_unclosed.pop_back();
			_pending_nl = _pos >= _max_line_width;
			if(indented)
				_indent--;
			puts(")");
			_pending_nl = true;
		}
    }
	void push() {
		_unclosed_stack.push_back(_unclosed.size());
	}
	void pop() {
		auto t = _unclosed_stack.back();
		log_assert(_unclosed.size() >= t);
		close(_unclosed.size() - t);
		_unclosed_stack.pop_back();
	}
    SExprWriter &operator <<(SExpr const &sexpr) {
        print(sexpr);
        _pending_nl = true;
        return *this;
    }
	void comment(std::string const &str, bool hanging = false) {
		if(hanging) {
			if(_pending_nl) {
				_pending_nl = false;
				puts(" ");
			}
		}
		puts("; ");
		puts(str);
		puts("\n");
	}
    ~SExprWriter() {
		while(!_unclosed_stack.empty())
			pop();
		close(_unclosed.size());
		nl_if_pending();
    }
};

struct SmtSort {
	FunctionalIR::Sort sort;
	SmtSort(FunctionalIR::Sort sort) : sort(sort) {}
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

struct SmtPrintVisitor {
	using Node = FunctionalIR::Node;
	std::function<SExpr(Node)> n;
	SmtStruct &input_struct;
	SmtStruct &state_struct;

	SmtPrintVisitor(SmtStruct &input_struct, SmtStruct &state_struct) : input_struct(input_struct), state_struct(state_struct) {}

	std::string literal(RTLIL::Const c) {
		std::string s = "#b";
		for(int i = c.size(); i-- > 0; )
			s += c[i] == State::S1 ? '1' : '0';
		return s;
	}

	SExpr from_bool(SExpr &&arg) {
		return list("ite", std::move(arg), "#b1", "#b0");
	}
	SExpr to_bool(SExpr &&arg) {
		return list("=", std::move(arg), "#b1");
	}
	SExpr extract(SExpr &&arg, int offset, int out_width = 1) {
		return list(list("_", "extract", offset + out_width - 1, offset), std::move(arg));
	}

	SExpr buf(Node, Node a) { return n(a); }
	SExpr slice(Node, Node a, int, int offset, int out_width) { return extract(n(a), offset, out_width); }
	SExpr zero_extend(Node, Node a, int, int out_width) { return list(list("_", "zero_extend", out_width - a.width()), n(a)); }
	SExpr sign_extend(Node, Node a, int, int out_width) { return list(list("_", "sign_extend", out_width - a.width()), n(a)); }
	SExpr concat(Node, Node a, int, Node b, int) { return list("concat", n(a), n(b)); }
	SExpr add(Node, Node a, Node b, int) { return list("bvadd", n(a), n(b)); }
	SExpr sub(Node, Node a, Node b, int) { return list("bvsub", n(a), n(b)); }
	SExpr mul(Node, Node a, Node b, int) { return list("bvmul", n(a), n(b)); }
	SExpr unsigned_div(Node, Node a, Node b, int) { return list("bvudiv", n(a), n(b)); }
	SExpr unsigned_mod(Node, Node a, Node b, int) { return list("bvurem", n(a), n(b)); }
	SExpr bitwise_and(Node, Node a, Node b, int) { return list("bvand", n(a), n(b)); }
	SExpr bitwise_or(Node, Node a, Node b, int) { return list("bvor", n(a), n(b)); }
	SExpr bitwise_xor(Node, Node a, Node b, int) { return list("bvxor", n(a), n(b)); }
	SExpr bitwise_not(Node, Node a, int) { return list("bvnot", n(a)); }
	SExpr unary_minus(Node, Node a, int) { return list("bvneg", n(a)); }
	SExpr reduce_and(Node, Node a, int) { return from_bool(list("=", n(a), literal(RTLIL::Const(State::S1, a.width())))); }
	SExpr reduce_or(Node, Node a, int) { return from_bool(list("=", n(a), literal(RTLIL::Const(State::S0, a.width())))); }
	SExpr reduce_xor(Node, Node a, int) {
		vector<SExpr> s { "bvxor" };
		for(int i = 0; i < a.width(); i++)
			s.push_back(extract(n(a), i));
		return s;
	}
	SExpr equal(Node, Node a, Node b, int) { return from_bool(list("=", n(a), n(b))); }
	SExpr not_equal(Node, Node a, Node b, int) { return from_bool(list("distinct", n(a), n(b))); }
	SExpr signed_greater_than(Node, Node a, Node b, int) { return from_bool(list("bvsgt", n(a), n(b))); }
	SExpr signed_greater_equal(Node, Node a, Node b, int) { return from_bool(list("bvsge", n(a), n(b))); }
	SExpr unsigned_greater_than(Node, Node a, Node b, int) { return from_bool(list("bvugt", n(a), n(b))); }
	SExpr unsigned_greater_equal(Node, Node a, Node b, int) { return from_bool(list("bvuge", n(a), n(b))); }

	SExpr extend(SExpr &&a, int in_width, int out_width) {
		if(in_width < out_width)
			return list(list("_", "zero_extend", out_width - in_width), std::move(a));
		else
			return std::move(a);
	}
	SExpr logical_shift_left(Node, Node a, Node b, int, int) { return list("bvshl", n(a), extend(n(b), b.width(), a.width())); }
	SExpr logical_shift_right(Node, Node a, Node b, int, int) { return list("bvshr", n(a), extend(n(b), b.width(), a.width())); }
	SExpr arithmetic_shift_right(Node, Node a, Node b, int, int) { return list("bvasr", n(a), extend(n(b), b.width(), a.width())); }
	SExpr mux(Node, Node a, Node b, Node s, int) { return list("ite", to_bool(n(s)), n(a), n(b)); }
	SExpr pmux(Node, Node a, Node b, Node s, int, int) {
		SExpr rv = n(a);
		for(int i = 0; i < s.width(); i++)
			rv = list("ite", to_bool(extract(n(s), i)), extract(n(b), a.width() * i, a.width()), rv);
		return rv;
	}
	SExpr constant(Node, RTLIL::Const value) { return literal(value); }
	SExpr memory_read(Node, Node mem, Node addr, int, int) { return list("select", n(mem), n(addr)); }
	SExpr memory_write(Node, Node mem, Node addr, Node data, int, int) { return list("store", n(mem), n(addr), n(data)); }

	SExpr input(Node, IdString name) { return input_struct.access("inputs", name); }
	SExpr state(Node, IdString name) { return state_struct.access("state", name); }

	SExpr undriven(Node, int width) { return literal(RTLIL::Const(State::S0, width)); }
};

struct SmtModule {
	FunctionalIR ir;
	SmtScope scope;
	std::string name;
	
	SmtStruct input_struct;
	SmtStruct output_struct;
	SmtStruct state_struct;

	SmtModule(Module *module)
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

		input_struct.write_definition(w);
		output_struct.write_definition(w);
		state_struct.write_definition(w);

		w << list("declare-datatypes",
			list(list("Pair", 2)),
			list(list("par", list("X", "Y"), list(list("pair", list("first", "X"), list("second", "Y"))))));

		w.push();
		w.open(list("define-fun", name,
			list(list("inputs", input_struct.name),
			     list("state", state_struct.name)),
			list("Pair", output_struct.name, state_struct.name)));
		auto inlined = [&](FunctionalIR::Node n) {
			return n.fn() == FunctionalIR::Fn::constant ||
				   n.fn() == FunctionalIR::Fn::undriven;
		};
		SmtPrintVisitor visitor(input_struct, state_struct);
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
				w.comment(SmtSort(n.sort()).to_sexpr().to_string(), true);
			}
		w.open(list("pair"));
		output_struct.write_value(w, [&](IdString name) { return node_to_sexpr(ir.get_output_node(name)); });
		state_struct.write_value(w, [&](IdString name) { return node_to_sexpr(ir.get_state_next_node(name)); });
		w.pop();
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
