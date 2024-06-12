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
#include "kernel/drivertools.h"
#include "kernel/topo_scc.h"
#include "kernel/functional.h"
#include "kernel/graphtools.h"

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
	bool _is_memory;
	int _width;
	int _addr_width;
public:
	CxxType() : _is_memory(false), _width(0), _addr_width(0) { }
	CxxType(int width) : _is_memory(false), _width(width), _addr_width(0) { }
	CxxType(int addr_width, int data_width) : _is_memory(true), _width(data_width), _addr_width(addr_width) { }
	static CxxType signal(int width) { return CxxType(width); }
	static CxxType memory(int addr_width, int data_width) { return CxxType(addr_width, data_width); }
	bool is_signal() const { return !_is_memory; }
	bool is_memory() const { return _is_memory; }
	int width() const { log_assert(is_signal()); return _width; }
	int addr_width() const { log_assert(is_memory()); return _addr_width; }
	int data_width() const { log_assert(is_memory()); return _width; }
	std::string to_string() const {
		if(_is_memory) {
			return stringf("Memory<%d, %d>", addr_width(), data_width());
		} else {
			return stringf("Signal<%d>", width());
		}
	}
	bool operator ==(CxxType const& other) const {
		if(_is_memory != other._is_memory) return false;
		if(_is_memory && _addr_width != other._addr_width) return false;
		return _width == other._width;
	}
	unsigned int hash() const {
		if(_is_memory)
			return mkhash(1, mkhash(_width, _addr_width));
		else
			return mkhash(0, _width);
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
  int count;
  CxxStruct(std::string name, bool generate_methods = false, int count = 0) 
    : name(name), generate_methods(generate_methods), count(count) {
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
      f.printf("\t\treturn %d;\n", count);
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

struct CxxFunction {
	IdString name;
	CxxType type;
	dict<IdString, Const> parameters;

	CxxFunction(IdString name, CxxType type) : name(name), type(type) {}
	CxxFunction(IdString name, CxxType type, dict<IdString, Const> parameters) : name(name), type(type), parameters(parameters) {}

	bool operator==(CxxFunction const &other) const {
		return name == other.name && parameters == other.parameters && type == other.type;
	}

	unsigned int hash() const {
		return mkhash(name.hash(), mkhash(type.hash(), parameters.hash()));
	}
};

typedef ComputeGraph<CxxFunction, int, IdString, IdString> CxxComputeGraph;

class CxxComputeGraphFactory {
	CxxComputeGraph &graph;
	using T = CxxComputeGraph::Ref;
	static bool is_single_output(IdString type)
	{
		auto it = yosys_celltypes.cell_types.find(type);
		return it != yosys_celltypes.cell_types.end() && it->second.outputs.size() <= 1;
	}
public:
	CxxComputeGraphFactory(CxxComputeGraph &g) : graph(g) {}
	T slice(T a, int in_width, int offset, int out_width) {
		log_assert(offset + out_width <= in_width);
		return graph.add(CxxFunction(ID($$slice), out_width, {{ID(offset), offset}}), 0, std::array<T, 1>{a});
	}
	T extend(T a, int in_width, int out_width, bool is_signed) {
		log_assert(in_width < out_width);
		if(is_signed)
			return graph.add(CxxFunction(ID($sign_extend), out_width, {{ID(WIDTH), out_width}}), 0, std::array<T, 1>{a});
		else
			return graph.add(CxxFunction(ID($zero_extend), out_width, {{ID(WIDTH), out_width}}), 0, std::array<T, 1>{a});
	}
	T concat(T a, int a_width, T b, int b_width) {
		return graph.add(CxxFunction(ID($$concat), a_width + b_width), 0, std::array<T, 2>{a, b});
	}
	T add(T a, T b, int width) { return graph.add(CxxFunction(ID($add), width), 0, std::array<T, 2>{a, b}); }
	T sub(T a, T b, int width) { return graph.add(CxxFunction(ID($sub), width), 0, std::array<T, 2>{a, b}); }
	T bitwise_and(T a, T b, int width) { return graph.add(CxxFunction(ID($and), width), 0, std::array<T, 2>{a, b}); }
	T bitwise_or(T a, T b, int width) { return graph.add(CxxFunction(ID($or), width), 0, std::array<T, 2>{a, b}); }
	T bitwise_xor(T a, T b, int width) { return graph.add(CxxFunction(ID($xor), width), 0, std::array<T, 2>{a, b}); }
	T bitwise_not(T a, int width) { return graph.add(CxxFunction(ID($not), width), 0, std::array<T, 1>{a}); }
	T neg(T a, int width) { return graph.add(CxxFunction(ID($neg), width), 0, std::array<T, 1>{a}); }
	T mux(T a, T b, T s, int width) { return graph.add(CxxFunction(ID($mux), width), 0, std::array<T, 3>{a, b, s}); }
	T pmux(T a, T b, T s, int width, int) { return graph.add(CxxFunction(ID($pmux), width), 0, std::array<T, 3>{a, b, s}); }
	T reduce_and(T a, int) { return graph.add(CxxFunction(ID($reduce_and), 1), 0, std::array<T, 1>{a}); }
	T reduce_or(T a, int) { return graph.add(CxxFunction(ID($reduce_or), 1), 0, std::array<T, 1>{a}); }
	T reduce_xor(T a, int) { return graph.add(CxxFunction(ID($reduce_xor), 1), 0, std::array<T, 1>{a}); }
	T eq(T a, T b, int) { return graph.add(CxxFunction(ID($eq), 1), 0, std::array<T, 2>{a, b}); }
	T ne(T a, T b, int) { return graph.add(CxxFunction(ID($ne), 1), 0, std::array<T, 2>{a, b}); }
	T gt(T a, T b, int) { return graph.add(CxxFunction(ID($gt), 1), 0, std::array<T, 2>{a, b}); }
	T ge(T a, T b, int) { return graph.add(CxxFunction(ID($ge), 1), 0, std::array<T, 2>{a, b}); }
	T ugt(T a, T b, int) { return graph.add(CxxFunction(ID($ugt), 1), 0, std::array<T, 2>{a, b}); }
	T uge(T a, T b, int) { return graph.add(CxxFunction(ID($uge), 1), 0, std::array<T, 2>{a, b}); }
	T logical_shift_left(T a, T b, int y_width, int) { return graph.add(CxxFunction(ID($shl), y_width, {{ID(WIDTH), y_width}}), 0, std::array<T, 2>{a, b}); }
	T logical_shift_right(T a, T b, int y_width, int) { return graph.add(CxxFunction(ID($shr), y_width, {{ID(WIDTH), y_width}}), 0, std::array<T, 2>{a, b}); }
	T arithmetic_shift_right(T a, T b, int y_width, int) { return graph.add(CxxFunction(ID($asr), y_width, {{ID(WIDTH), y_width}}), 0, std::array<T, 2>{a, b}); }

	T constant(RTLIL::Const value) {
		return graph.add(CxxFunction(ID($$const), value.size(), {{ID(value), value}}), 0);
	}
	T input(IdString name, int width) { return graph.add(CxxFunction(ID($$input), width, {{name, {}}}), 0); }
	T state(IdString name, int width) { return graph.add(CxxFunction(ID($$state), width, {{name, {}}}), 0); }
	T state_memory(IdString name, int addr_width, int data_width) {
		return graph.add(CxxFunction(ID($$state), CxxType::memory(addr_width, data_width), {{name, {}}}), 0);
	}
	T cell_output(T cell, IdString type, IdString name, int width) {
		if (is_single_output(type))
			return cell;
		else
			return graph.add(CxxFunction(ID($$cell_output), width, {{name, {}}}), 0, std::array<T, 1>{cell});
	}
	T multiple(vector<T> args, int width) {
		return graph.add(CxxFunction(ID($$multiple), width), 0, args);
	}
	T undriven(int width) {
		return graph.add(CxxFunction(ID($$undriven), width), 0);
	}

	T memory_read(T mem, T addr, int addr_width, int data_width) {
		return graph.add(CxxFunction(ID($memory_read), data_width), 0, std::array<T, 2>{mem, addr});
	}
	T memory_write(T mem, T addr, T data, int addr_width, int data_width) {
		return graph.add(CxxFunction(ID($memory_write), CxxType::memory(addr_width, data_width)), 0, std::array<T, 3>{mem, addr, data});
	}

	T create_pending(int width) {
		return graph.add(CxxFunction(ID($$pending), width), 0);
	}
	void update_pending(T pending, T node) {
		log_assert(pending.function().name == ID($$pending));
		pending.set_function(CxxFunction(ID($$buf), pending.function().type));
		pending.append_arg(node);
	}
	void declare_output(T node, IdString name, int) {
		node.assign_key(name);
	}
	void declare_state(T node, IdString name, int) {
		node.assign_key(name);
	}
	void declare_state_memory(T node, IdString name, int, int) {
		node.assign_key(name);
	}
	void suggest_name(T node, IdString name) {
		node.sparse_attr() = name;
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

	CxxComputeGraph calculate_compute_graph(RTLIL::Module *module)
	{
		CxxComputeGraph compute_graph;
		CxxComputeGraphFactory factory(compute_graph);
		ComputeGraphConstruction<CxxComputeGraph::Ref, CxxComputeGraphFactory> construction(factory);
		construction.add_module(module);
		construction.process_queue();

		// Perform topo sort and detect SCCs
		CxxComputeGraph::SccAdaptor compute_graph_scc(compute_graph);

		bool scc = false;
		std::vector<int> perm;
		topo_sorted_sccs(compute_graph_scc, [&](int *begin, int *end) {
			perm.insert(perm.end(), begin, end);
			if (end > begin + 1)
			{
				log_warning("SCC:");
				for (int *i = begin; i != end; ++i)
					log(" %d(%s)(%s)", *i, compute_graph[*i].function().name.c_str(), compute_graph[*i].has_sparse_attr() ? compute_graph[*i].sparse_attr().c_str() : "");
				log("\n");
				scc = true;
			}
		}, /* sources_first */ true);
		compute_graph.permute(perm);
		if(scc) log_error("combinational loops, aborting\n");

		// Forward $$buf
		std::vector<int> alias;
		perm.clear();

		for (int i = 0; i < compute_graph.size(); ++i)
		{
			auto node = compute_graph[i];
			if (node.function().name == ID($$buf) && node.arg(0).index() < i)
			{
				int target_index = alias[node.arg(0).index()];
				auto target_node = compute_graph[perm[target_index]];
				if(!target_node.has_sparse_attr() && node.has_sparse_attr()){
					IdString id = node.sparse_attr();
					target_node.sparse_attr() = id;
				}
				alias.push_back(target_index);
			}
			else
			{
				alias.push_back(GetSize(perm));
				perm.push_back(i);
			}
		}
		compute_graph.permute(perm, alias);
		return compute_graph;
	}

	void printCxx(std::ostream &stream, std::string, std::string const & name, CxxComputeGraph &compute_graph)
	{
		dict<IdString, CxxType> inputs, state;
		CxxWriter f(stream);

		// Dump the compute graph
		for (int i = 0; i < compute_graph.size(); ++i)
		{
			auto ref = compute_graph[i];
			if(ref.function().name == ID($$input))
				inputs[ref.function().parameters.begin()->first] = ref.function().type;
			if(ref.function().name == ID($$state))
				state[ref.function().parameters.begin()->first] = ref.function().type;
		}
		f.printf("#include \"sim.h\"\n");
		f.printf("#include <variant>\n");
		CxxStruct input_struct(name + "_Inputs", true, inputs.size());
		for (auto const &input : inputs)
			input_struct.insert(input.first, input.second);
		CxxStruct output_struct(name + "_Outputs");
		for (auto const &key : compute_graph.keys())
			if(state.count(key.first) == 0)
				output_struct.insert(key.first, compute_graph[key.second].function().type);
		CxxStruct state_struct(name + "_State");
		for (auto const &state_var : state)
			state_struct.insert(state_var.first, state_var.second);

		idict<std::string> node_names;
		CxxScope locals;

		input_struct.print(f);
		output_struct.print(f);
		state_struct.print(f);

		f.printf("void %s(%s_Inputs const &input, %s_Outputs &output, %s_State const &current_state, %s_State &next_state)\n{\n", name.c_str(), name.c_str(), name.c_str(), name.c_str(), name.c_str());
		locals.reserve("input");
		locals.reserve("output");
		locals.reserve("current_state");
		locals.reserve("next_state");
		for (int i = 0; i < compute_graph.size(); ++i)
		{
			auto ref = compute_graph[i];
			auto type = ref.function().type;
			std::string name;
			if(ref.has_sparse_attr())
				name = locals.insert(ref.sparse_attr());
			else
				name = locals.insert("\\n" + std::to_string(i));
			node_names(name);
			if(ref.function().name == ID($$input))
				f.printf("\t%s %s = input.%s;\n", type.to_string().c_str(), name.c_str(), input_struct[ref.function().parameters.begin()->first].c_str());
			else if(ref.function().name == ID($$state))
				f.printf("\t%s %s = current_state.%s;\n", type.to_string().c_str(), name.c_str(), state_struct[ref.function().parameters.begin()->first].c_str());
			else if(ref.function().name == ID($$buf))
				f.printf("\t%s %s = %s;\n", type.to_string().c_str(), name.c_str(), node_names[ref.arg(0).index()].c_str());
			else if(ref.function().name == ID($$cell_output))
				f.printf("\t%s %s = %s.%s;\n", type.to_string().c_str(), name.c_str(), node_names[ref.arg(0).index()].c_str(), RTLIL::unescape_id(ref.function().parameters.begin()->first).c_str());
			else if(ref.function().name == ID($$const)){
				auto c = ref.function().parameters.begin()->second;
				if(c.size() <= 32){
					f.printf("\t%s %s = $const<%d>(%#x);\n", type.to_string().c_str(), name.c_str(), type.width(), (uint32_t) c.as_int());
				}else{
					f.printf("\t%s %s = $const<%d>({%#x", type.to_string().c_str(), name.c_str(), type.width(), (uint32_t) c.as_int());
					while(c.size() > 32){
						c = c.extract(32, c.size() - 32);
						f.printf(", %#x", c.as_int());
					}
					f.printf("});\n");
				}
			}else if(ref.function().name == ID($$undriven))
				f.printf("\t%s %s; //undriven\n", type.to_string().c_str(), name.c_str());
			else if(ref.function().name == ID($$slice))
				f.printf("\t%s %s = slice<%d>(%s, %d);\n", type.to_string().c_str(), name.c_str(), type.width(), node_names[ref.arg(0).index()].c_str(), ref.function().parameters.at(ID(offset)).as_int());
			else if(ref.function().name == ID($$concat)){
				f.printf("\tauto %s = concat(", name.c_str());
				for (int i = 0, end = ref.size(); i != end; ++i){
					if(i > 0)
						f.printf(", ");
					f.printf("%s", node_names[ref.arg(i).index()].c_str());
				}
				f.printf(");\n");
			}else{
				f.printf("\t");
				f.printf("%s %s = %s", type.to_string().c_str(), name.c_str(), log_id(ref.function().name));
				if(ref.function().parameters.count(ID(WIDTH))){
					f.printf("<%d>", ref.function().parameters.at(ID(WIDTH)).as_int());
				}
				f.printf("(");
				for (int i = 0, end = ref.size(); i != end; ++i)
					f.printf("%s%s", i>0?", ":"", node_names[ref.arg(i).index()].c_str());
				f.printf("); //");
				for (auto const &param : ref.function().parameters)
				{
					if (param.second.empty())
						f.printf("[%s]", log_id(param.first));
					else
						f.printf("[%s=%s]", log_id(param.first), log_const(param.second));
				}
				f.printf("\n");
			}
		}

		for (auto const &key : compute_graph.keys())
		{
			f.printf("\t%s.%s = %s;\n", state.count(key.first) > 0 ? "next_state" : "output", state_struct[key.first].c_str(), node_names[key.second].c_str());
		}
		f.printf("}\n");
	}

	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
        log_header(design, "Executing Functional C++ backend.\n");

		size_t argidx = 1;
		extra_args(f, filename, args, argidx, design);

		for (auto module : design->selected_modules()) {
            log("Dumping module `%s'.\n", module->name.c_str());
			auto compute_graph = calculate_compute_graph(module);
			printCxx(*f, filename, RTLIL::unescape_id(module->name), compute_graph);
		}
	}
} FunctionalCxxBackend;

PRIVATE_NAMESPACE_END
