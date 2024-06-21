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

struct CxxScope {
	pool<std::string> used_names;
	dict<IdString, std::string> name_map;

	CxxScope() {
		for(const char **p = reserved_keywords; *p != nullptr; p++)
			reserve(*p);
	}
	void reserve(std::string name) {
		used_names.insert(name);
	}
	std::string insert(IdString id) {
		std::string str = RTLIL::unescape_id(id);
		for(size_t i = 0; i < str.size(); i++)
			if(strchr("!\"#%&'()*+,-./:;<=>?@[]\\^`{|}~ ", str[i]))
				str[i] = '_';
		if(used_names.count(str) == 0){
			used_names.insert(str);
			name_map.insert({id, str});
			return str;
		}
		for (int idx = 0 ; ; idx++){
			std::string suffixed = str + "_" + std::to_string(idx);
			if (used_names.count(suffixed) == 0) {
				used_names.insert(suffixed);
				if(name_map.count(id) == 0)
					name_map.insert({id, suffixed});
				return suffixed;
			}
		}
	}
	std::string operator[](IdString id) {
		if(name_map.count(id) > 0)
			return name_map[id];
		else
			return insert(id);
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

struct CxxWriter {
	std::ostream &f;
	CxxWriter(std::ostream &out) : f(out) {}
	void printf(const char *fmt, ...)
	{
		va_list va;
		va_start(va, fmt);
		f << vstringf(fmt, va);
		va_end(va);
	}
};

struct CxxStruct {
  std::string name;
  dict<IdString, CxxType> types;
  CxxScope scope;
  bool generate_methods;
  CxxStruct(std::string name, bool generate_methods = false)
    : name(name), generate_methods(generate_methods) {
    scope.reserve("out");
    scope.reserve("dump");
  }
  void insert(IdString name, CxxType type) {
    scope.insert(name);
    types.insert({name, type});
  }
  void print(CxxWriter &f) {
    f.printf("struct %s {\n", name.c_str());
    for (auto p : types) {
      f.printf("\t%s %s;\n", p.second.to_string().c_str(), scope[p.first].c_str());
    }
    f.printf("\n\ttemplate <typename T> void dump(T &out) const {\n");
    for (auto p : types) {
      f.printf("\t\tout(\"%s\", %s);\n", RTLIL::unescape_id(p.first).c_str(), scope[p.first].c_str());
    }
    f.printf("\t}\n\n");

    if (generate_methods) {
      // Add size method
      f.printf("\tint size() const {\n");
      f.printf("\t\treturn %d;\n", types.size());
      f.printf("\t}\n\n");

      // Add get_input method
      f.printf("\tstd::variant<%s> get_input(const int index) {\n", generate_variant_types().c_str());
      f.printf("\t\tswitch (index) {\n");
      int idx = 0;
      for (auto p : types) {
	f.printf("\t\t\tcase %d: return std::ref(%s);\n", idx, scope[p.first].c_str());
	idx++;
      }
      f.printf("\t\t\tdefault: throw std::out_of_range(\"Invalid input index\");\n");
      f.printf("\t\t}\n");
      f.printf("\t}\n");
    }
    
    f.printf("};\n\n");
  };
  std::string operator[](IdString field) {
    return scope[field];
  }
  private:
  std::string generate_variant_types() const {
        std::set<std::string> unique_types;
        for (const auto& p : types) {
            unique_types.insert("std::reference_wrapper<" + p.second.to_string() + ">");
        }
        std::ostringstream oss;
        for (auto it = unique_types.begin(); it != unique_types.end(); ++it) {
            if (it != unique_types.begin()) {
                oss << ", ";
            }
            oss << *it;
        }
        return oss.str();
  }
};

struct CxxTemplate {
	vector<std::variant<std::string, int>> _v;
public:
	CxxTemplate(std::string fmt) {
		std::string buf;
		for(auto it = fmt.begin(); it != fmt.end(); it++){
			if(*it == '%'){
				it++;
				log_assert(it != fmt.end());
				if(*it == '%')
					buf += *it;
				else {
					log_assert(*it >= '0' && *it <= '9');
					_v.emplace_back(std::move(buf));
					_v.emplace_back((int)(*it - '0'));
				}
			}else
				buf += *it;
		}
		if(!buf.empty())
			_v.emplace_back(std::move(buf));
	}
	template<typename... Args> static std::string format(CxxTemplate fmt, Args&&... args) {
		vector<std::string> strs = {args...};
		std::string result;
		for(auto &v : fmt._v){
			if(std::string *s = std::get_if<std::string>(&v))
				result += *s;
			else if(int *i = std::get_if<int>(&v))
				result += strs[*i];
			else
				log_error("missing case");
		}
		return result;
	}
};

template<class NodeNames> struct CxxPrintVisitor {
	using Node = FunctionalIR::Node;
	NodeNames np;
	CxxStruct &input_struct;
	CxxStruct &state_struct;
	CxxPrintVisitor(NodeNames np, CxxStruct &input_struct, CxxStruct &state_struct) : np(np), input_struct(input_struct), state_struct(state_struct) { }
	template<class T> std::string arg_to_string(T n) { return std::to_string(n); }
	std::string arg_to_string(std::string n) { return n; }
	std::string arg_to_string(Node n) { return np(n); }
	template<typename... Args> std::string format(std::string fmt, Args&&... args) {
		return CxxTemplate::format(fmt, arg_to_string(args)...);
	}
	std::string buf(Node, Node n) { return np(n); }
	std::string slice(Node, Node a, int, int offset, int out_width) { return format("slice<%2>(%0, %1)", a, offset, out_width); }
	std::string zero_extend(Node, Node a, int, int out_width) { return format("$zero_extend<%1>(%0)", a, out_width); }
	std::string sign_extend(Node, Node a, int, int out_width) { return format("$sign_extend<%1>(%0)", a, out_width); }
	std::string concat(Node, Node a, int, Node b, int) { return format("concat(%0, %1)", a, b); }
	std::string add(Node, Node a, Node b, int) { return format("$add(%0, %1)", a, b); }
	std::string sub(Node, Node a, Node b, int) { return format("$sub(%0, %1)", a, b); }
	std::string bitwise_and(Node, Node a, Node b, int) { return format("$and(%0, %1)", a, b); }
	std::string bitwise_or(Node, Node a, Node b, int) { return format("$or(%0, %1)", a, b); }
	std::string bitwise_xor(Node, Node a, Node b, int) { return format("$xor(%0, %1)", a, b); }
	std::string bitwise_not(Node, Node a, int) { return format("$not(%0)", a); }
	std::string unary_minus(Node, Node a, int) { return format("$neg(%0)", a); }
	std::string reduce_and(Node, Node a, int) { return format("$reduce_and(%0)", a); }
	std::string reduce_or(Node, Node a, int) { return format("$reduce_or(%0)", a); }
	std::string reduce_xor(Node, Node a, int) { return format("$reduce_xor(%0)", a); }
	std::string equal(Node, Node a, Node b, int) { return format("$eq(%0, %1)", a, b); }
	std::string not_equal(Node, Node a, Node b, int) { return format("$ne(%0, %1)", a, b); }
	std::string signed_greater_than(Node, Node a, Node b, int) { return format("$gt(%0, %1)", a, b); }
	std::string signed_greater_equal(Node, Node a, Node b, int) { return format("$ge(%0, %1)", a, b); }
	std::string unsigned_greater_than(Node, Node a, Node b, int) { return format("$ugt(%0, %1)", a, b); }
	std::string unsigned_greater_equal(Node, Node a, Node b, int) { return format("$uge(%0, %1)", a, b); }
	std::string logical_shift_left(Node, Node a, Node b, int, int) { return format("$shl<%2>(%0, %1)", a, b, a.width()); }
	std::string logical_shift_right(Node, Node a, Node b, int, int) { return format("$shr<%2>(%0, %1)", a, b, a.width()); }
	std::string arithmetic_shift_right(Node, Node a, Node b, int, int) { return format("$asr<%2>(%0, %1)", a, b, a.width()); }
	std::string mux(Node, Node a, Node b, Node s, int) { return format("$mux(%0, %1, %2)", a, b, s); }
	std::string pmux(Node, Node a, Node b, Node s, int, int) { return format("$pmux(%0, %1, %2)", a, b, s); }
	std::string constant(Node, RTLIL::Const value) { return format("$const<%0>(%1)", value.size(), value.as_int()); }
	std::string input(Node, IdString name) { return format("input.%0", input_struct[name]); }
	std::string state(Node, IdString name) { return format("current_state.%0", state_struct[name]); }
	std::string memory_read(Node, Node mem, Node addr, int, int) { return format("$memory_read(%0, %1)", mem, addr); }
	std::string memory_write(Node, Node mem, Node addr, Node data, int, int) { return format("$memory_write(%0, %1, %2)", mem, addr, data); }
	std::string undriven(Node, int width) { return format("$const<%0>(0)", width); }
};

struct FunctionalCxxBackend : public Backend
{
	FunctionalCxxBackend() : Backend("functional_cxx", "convert design to C++ using the functional backend") {}

    void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
    }

	void printCxx(std::ostream &stream, std::string, std::string const & name, Module *module)
	{
		auto ir = FunctionalIR::from_module(module);
		CxxWriter f(stream);

		f.printf("#include \"sim.h\"\n");
		f.printf("#include <variant>\n");
		CxxStruct input_struct(name + "_Inputs", true);
		for (auto [name, sort] : ir.inputs())
			input_struct.insert(name, sort);
		CxxStruct output_struct(name + "_Outputs");
		for (auto [name, sort] : ir.outputs())
			output_struct.insert(name, sort);
		CxxStruct state_struct(name + "_State");
		for (auto [name, sort] : ir.state())
			state_struct.insert(name, sort);

		dict<int, std::string> node_names;
		CxxScope locals;

		input_struct.print(f);
		output_struct.print(f);
		state_struct.print(f);

		f.printf("void %s(%s_Inputs const &input, %s_Outputs &output, %s_State const &current_state, %s_State &next_state)\n{\n", name.c_str(), name.c_str(), name.c_str(), name.c_str(), name.c_str());
		locals.reserve("input");
		locals.reserve("output");
		locals.reserve("current_state");
		locals.reserve("next_state");
		auto node_to_string = [&](FunctionalIR::Node n) { return node_names.at(n.id()); };
		for (auto node : ir)
		{
			std::string name = locals.insert(node.name());
			node_names.emplace(node.id(), name);
			f.printf("\t%s %s = %s;\n", CxxType(node.sort()).to_string().c_str(), name.c_str(), node.visit(CxxPrintVisitor(node_to_string, input_struct, state_struct)).c_str());
		}
		for (auto [name, sort] : ir.state())
			f.printf("\tnext_state.%s = %s;\n", state_struct[name].c_str(), node_to_string(ir.get_state_next_node(name)).c_str());
		for (auto [name, sort] : ir.outputs())
			f.printf("\toutput.%s = %s;\n", output_struct[name].c_str(), node_to_string(ir.get_output_node(name)).c_str());
		f.printf("}\n");
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
        log_header(design, "Executing Functional C++ backend.\n");

		size_t argidx = 1;
		extra_args(f, filename, args, argidx, design);

		for (auto module : design->selected_modules()) {
            log("Dumping module `%s'.\n", module->name.c_str());
			printCxx(*f, filename, RTLIL::unescape_id(module->name), module);
		}
	}
} FunctionalCxxBackend;

PRIVATE_NAMESPACE_END
