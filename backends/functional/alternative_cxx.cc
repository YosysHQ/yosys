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

#include <cassert>
#include <array>
#include "kernel/yosys.h"
#include "kernel/drivertools.h"
#include "kernel/topo_scc.h"
#include "kernel/functional.h"
#include "kernel/alternative_graphtools.h"

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
  "signed","sizeof","static","static_assert","static_cast","struct",
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
  dict<IdString, std::string> types;
  CxxScope scope;
  CxxStruct(std::string name) : name(name) {
    scope.reserve("out");
    scope.reserve("dump");
  }
  void insert(IdString name, std::string type) {
    scope.insert(name);
    types.insert({name, type});
  }
  void print(CxxWriter &f) {
    f.printf("struct %s {\n", name.c_str());
    for (auto p : types) {
      f.printf("\t%s %s;\n", p.second.c_str(), scope[p.first].c_str());
    }
    f.printf("\n\ttemplate <typename T> void dump(T &out) {\n");
    for (auto p : types) {
      f.printf("\t\tout(\"%s\", %s);\n", RTLIL::unescape_id(p.first).c_str(), scope[p.first].c_str());
    }
    f.printf("\t}\n};\n\n");
  }
  std::string operator[](IdString field) {
    return scope[field];
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

  void printCxx(std::ostream &stream, std::string, std::string const & name, CompleteComputeGraph &compute_graph)
  {
    dict<IdString, int> inputs, state;
    CxxWriter f(stream);

    // Dump the compute graph
    for (int i = 0; i < compute_graph.size(); ++i)
      {
	auto ref = compute_graph[i];
	if(ref.function().name == ID($$input))
	  inputs[ref.function().parameters.begin()->first] = ref.function().width;
	if(ref.function().name == ID($$state))
	  state[ref.function().parameters.begin()->first] = ref.function().width;
      }
    f.printf("#include \"sim.h\"\n");
    CxxStruct input_struct(name + "_Inputs");
    for (auto const &input : inputs)
      input_struct.insert(input.first, "Signal<" + std::to_string(input.second) + ">");
    CxxStruct output_struct(name + "_Outputs");
    for (auto const &key : compute_graph.keys())
      if(state.count(key.first) == 0)
	output_struct.insert(key.first, "Signal<" + std::to_string(compute_graph[key.second].function().width) + ">");
    CxxStruct state_struct(name + "_State");
    for (auto const &state_var : state)
      state_struct.insert(state_var.first, "Signal<" + std::to_string(state_var.second) + ">");

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
	int width = ref.function().width;
	std::string name;
	if(ref.has_sparse_attr())
	  name = locals.insert(ref.sparse_attr());
	else
	  name = locals.insert("\\n" + std::to_string(i));
	node_names(name);
	if(ref.function().name == ID($$input))
	  f.printf("\tSignal<%d> %s = input.%s;\n", width, name.c_str(), input_struct[ref.function().parameters.begin()->first].c_str());
	else if(ref.function().name == ID($$state))
	  f.printf("\tSignal<%d> %s = current_state.%s;\n", width, name.c_str(), state_struct[ref.function().parameters.begin()->first].c_str());
	else if(ref.function().name == ID($$buf))
	  f.printf("\tSignal<%d> %s = %s;\n", width, name.c_str(), node_names[ref.arg(0).index()].c_str());
	else if(ref.function().name == ID($$cell_output))
	  f.printf("\tSignal<%d> %s = %s.%s;\n", width, name.c_str(), node_names[ref.arg(0).index()].c_str(), RTLIL::unescape_id(ref.function().parameters.begin()->first).c_str());
	else if(ref.function().name == ID($$const)){
	  auto c = ref.function().parameters.begin()->second;
	  if(c.size() <= 32){
	    f.printf("\tSignal<%d> %s = $const<%d>(%#x);\n", width, name.c_str(), width, (uint32_t) c.as_int());
	  }else{
	    f.printf("\tSignal<%d> %s = $const<%d>({%#x", width, name.c_str(), width, (uint32_t) c.as_int());
	    while(c.size() > 32){
	      c = c.extract(32, c.size() - 32);
	      f.printf(", %#x", c.as_int());
	    }
	    f.printf("});\n");
	  }
	}else if(ref.function().name == ID($$undriven))
	  f.printf("\tSignal<%d> %s; //undriven\n", width, name.c_str());
	else if(ref.function().name == ID($$slice))
	  f.printf("\tSignal<%d> %s = slice<%d>(%s, %d);\n", width, name.c_str(), width, node_names[ref.arg(0).index()].c_str(), ref.function().parameters.at(ID(offset)).as_int());
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
	  if(ref.function().width > 0)
	    f.printf("Signal<%d>", ref.function().width);
	  else
	    f.printf("%s_Outputs", log_id(ref.function().name));
	  f.printf(" %s = %s", name.c_str(), log_id(ref.function().name));
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
