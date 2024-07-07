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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

const char illegal_characters[] = "#:\\";
const char *reserved_keywords[] = {};

struct SmtScope {
  pool<std::string> used_names;
  dict<IdString, std::string> name_map;
  FunctionalTools::Scope scope;
  SmtScope() : scope(illegal_characters, reserved_keywords) {}

  void reserve(const std::string &name) { used_names.insert(name); }

  std::string insert(IdString id)
  {

    std::string name = scope(id);
    if (used_names.count(name) == 0) {
      used_names.insert(name);
      name_map[id] = name;
      return name;
    }
    for (int idx = 0;; ++idx) {
      std::string new_name = name + "_" + std::to_string(idx);
      if (used_names.count(new_name) == 0) {
	used_names.insert(new_name);
	name_map[id] = new_name;
	return new_name;
      }
    }
  }

  std::string operator[](IdString id)
  {
    if (name_map.count(id)) {
      return name_map[id];
    } else {
      return insert(id);
    }
  }
};

struct SmtWriter {
  std::ostream &stream;

  SmtWriter(std::ostream &out) : stream(out) {}

  void print(const char *fmt, ...)
  {
    va_list args;
    va_start(args, fmt);
    stream << vstringf(fmt, args);
    va_end(args);
  }
};

template <class NodeNames> struct SmtPrintVisitor {
  using Node = FunctionalIR::Node;
  NodeNames np;
  SmtScope &scope;

  SmtPrintVisitor(NodeNames np, SmtScope &scope) : np(np), scope(scope) {}

  template <class T> std::string arg_to_string(T n) { return std::to_string(n); }

  std::string arg_to_string(std::string n) { return n; }

  std::string arg_to_string(Node n) { return np(n); }

  template <typename... Args> std::string format(std::string fmt, Args &&...args)
  {
    std::vector<std::string> arg_strings = {arg_to_string(std::forward<Args>(args))...};
    for (size_t i = 0; i < arg_strings.size(); ++i) {
      std::string placeholder = "%" + std::to_string(i);
      size_t pos = 0;
      while ((pos = fmt.find(placeholder, pos)) != std::string::npos) {
	fmt.replace(pos, placeholder.length(), arg_strings[i]);
	pos += arg_strings[i].length();
      }
    }
    return fmt;
  }
  std::string buf(Node, Node n) { return np(n); }

  std::string slice(Node, Node a, int, int offset, int out_width)
  {
    return format("((_ extract %2 %1) %0)", np(a), offset, offset + out_width - 1);
  }

  std::string zero_extend(Node, Node a, int, int out_width) { return format("((_ zero_extend %1) %0)", np(a), out_width - a.width()); }

  std::string sign_extend(Node, Node a, int, int out_width) { return format("((_ sign_extend %1) %0)", np(a), out_width - a.width()); }

  std::string concat(Node, Node a, int, Node b, int) { return format("(concat %0 %1)", np(a), np(b)); }

  std::string add(Node, Node a, Node b, int) { return format("(bvadd %0 %1)", np(a), np(b)); }

  std::string sub(Node, Node a, Node b, int) { return format("(bvsub %0 %1)", np(a), np(b)); }

  std::string mul(Node, Node a, Node b, int) { return format("(bvmul %0 %1)", np(a), np(b)); }

  std::string unsigned_div(Node, Node a, Node b, int) { return format("(bvudiv %0 %1)", np(a), np(b)); }

  std::string unsigned_mod(Node, Node a, Node b, int) { return format("(bvurem %0 %1)", np(a), np(b)); }

  std::string bitwise_and(Node, Node a, Node b, int) { return format("(bvand %0 %1)", np(a), np(b)); }

  std::string bitwise_or(Node, Node a, Node b, int) { return format("(bvor %0 %1)", np(a), np(b)); }

  std::string bitwise_xor(Node, Node a, Node b, int) { return format("(bvxor %0 %1)", np(a), np(b)); }

  std::string bitwise_not(Node, Node a, int) { return format("(bvnot %0)", np(a)); }

  std::string unary_minus(Node, Node a, int) { return format("(bvneg %0)", np(a)); }

  std::string reduce_and(Node, Node a, int) {
    std::stringstream ss;
    // We use ite to set the result to bit vector, to ensure appropriate type
    ss << "(ite (= " << np(a) << " #b" << std::string(a.width(), '1') << ") #b1 #b0)";
    return ss.str();
  }
 
  std::string reduce_or(Node, Node a, int)
  {
    std::stringstream ss;
    // We use ite to set the result to bit vector, to ensure appropriate type
    ss << "(ite (= " << np(a) << " #b" << std::string(a.width(), '0') << ") #b0 #b1)";
    return ss.str();
  }

  std::string reduce_xor(Node, Node a, int) {
    std::stringstream ss;
    ss << "(bvxor ";
    for (int i = 0; i < a.width(); ++i) {
      if (i > 0) ss << " ";
      ss << "((_ extract " << i << " " << i << ") " << np(a) << ")";
    }
    ss << ")";
    return ss.str();
  }
 
  std::string equal(Node, Node a, Node b, int) {
    return format("(ite (= %0 %1) #b1 #b0)", np(a), np(b));
  }

  std::string not_equal(Node, Node a, Node b, int) {
    return format("(ite (distinct %0 %1) #b1 #b0)", np(a), np(b));
  }

  std::string signed_greater_than(Node, Node a, Node b, int) { 
    return format("(ite (bvsgt %0 %1) #b1 #b0)", np(a), np(b)); 
  }

  std::string signed_greater_equal(Node, Node a, Node b, int) {
    return format("(ite (bvsge %0 %1) #b1 #b0)", np(a), np(b));
  }

  std::string unsigned_greater_than(Node, Node a, Node b, int) { 
    return format("(ite (bvugt %0 %1) #b1 #b0)", np(a), np(b)); 
  }

  std::string unsigned_greater_equal(Node, Node a, Node b, int) { 
    return format("(ite (bvuge %0 %1) #b1 #b0)", np(a), np(b)); 
  }

  std::string logical_shift_left(Node, Node a, Node b, int, int) {
    // Get the bit-widths of a and b
    int bit_width_a = a.width();
    int bit_width_b = b.width();

    // Extend b to match the bit-width of a if necessary
    std::ostringstream oss;
    if (bit_width_a > bit_width_b) {
      oss << "((_ zero_extend " << (bit_width_a - bit_width_b) << ") " << np(b) << ")";
    } else {
      oss << np(b);  // No extension needed if b's width is already sufficient
    }
    std::string b_extended = oss.str();

    // Format the bvshl operation with the extended b
    oss.str(""); // Clear the stringstream
    oss << "(bvshl " << np(a) << " " << b_extended << ")";
    return oss.str();
  }

  std::string logical_shift_right(Node, Node a, Node b, int, int) {
    // Get the bit-widths of a and b
    int bit_width_a = a.width();
    int bit_width_b = b.width();

    // Extend b to match the bit-width of a if necessary
    std::ostringstream oss;
    if (bit_width_a > bit_width_b) {
      oss << "((_ zero_extend " << (bit_width_a - bit_width_b) << ") " << np(b) << ")";
    } else {
      oss << np(b);  // No extension needed if b's width is already sufficient
    }
    std::string b_extended = oss.str();

    // Format the bvlshr operation with the extended b
    oss.str(""); // Clear the stringstream
    oss << "(bvlshr " << np(a) << " " << b_extended << ")";
    return oss.str();
  }

  std::string arithmetic_shift_right(Node, Node a, Node b, int, int) {
    // Get the bit-widths of a and b
    int bit_width_a = a.width();
    int bit_width_b = b.width();

    // Extend b to match the bit-width of a if necessary
    std::ostringstream oss;
    if (bit_width_a > bit_width_b) {
      oss << "((_ zero_extend " << (bit_width_a - bit_width_b) << ") " << np(b) << ")";
    } else {
      oss << np(b);  // No extension needed if b's width is already sufficient
    }
    std::string b_extended = oss.str();

    // Format the bvashr operation with the extended b
    oss.str(""); // Clear the stringstream
    oss << "(bvashr " << np(a) << " " << b_extended << ")";
    return oss.str();
  }
 
  std::string mux(Node, Node a, Node b, Node s, int) {
    return format("(ite (= %2 #b1) %0 %1)", np(a), np(b), np(s));
  }

  std::string pmux(Node, Node a, Node b, Node s, int, int)
  {
    // Assume s is a bit vector, combine a and b based on the selection bits
    return format("(pmux %0 %1 %2)", np(a), np(b), np(s));
  }

  std::string constant(Node, RTLIL::Const value) { return format("#b%0", value.as_string()); }

  std::string input(Node, IdString name) { return format("%0", scope[name]); }

  std::string state(Node, IdString name) { return format("(%0 current_state)", scope[name]); }

  std::string memory_read(Node, Node mem, Node addr, int, int) { return format("(select %0 %1)", np(mem), np(addr)); }

  std::string memory_write(Node, Node mem, Node addr, Node data, int, int) { return format("(store %0 %1 %2)", np(mem), np(addr), np(data)); }

  std::string undriven(Node, int width) { return format("#b%0", std::string(width, '0')); }
};

struct SmtModule {
  std::string name;
  SmtScope scope;
  FunctionalIR ir;

  SmtModule(const std::string &module_name, FunctionalIR ir) : name(module_name), ir(std::move(ir)) {}

  void write(std::ostream &out)
  {
    const bool stateful = ir.state().size() != 0;
    SmtWriter writer(out);

    writer.print("(declare-fun %s () Bool)\n\n", name.c_str());

    writer.print("(declare-datatypes ()  ((Inputs    (mk_inputs");
    for (const auto &input : ir.inputs()) {
      std::string input_name = scope[input.first];
      writer.print(" (%s (_ BitVec %d))", input_name.c_str(), input.second.width());
    }
    writer.print("))))\n\n");

    writer.print("(declare-datatypes () ((Outputs    (mk_outputs");
    for (const auto &output : ir.outputs()) {
      std::string output_name = scope[output.first];
      writer.print(" (%s (_ BitVec %d))", output_name.c_str(), output.second.width());
    }
    writer.print("))))\n");

    if (stateful) {
      writer.print("(declare-datatypes ()  ((State   (mk_state");
      for (const auto &state : ir.state()) {
	std::string state_name = scope[state.first];
	writer.print(" (%s (_ BitVec %d))", state_name.c_str(), state.second.width());
      }
      writer.print("))))\n");

      writer.print("(declare-datatypes ()  ((Pair   (mk-pair (outputs Outputs) (next_state State)))))\n");
    }

    if (stateful)
      writer.print("(define-fun %s_step ((current_state State) (inputs Inputs)) Pair", name.c_str());
    else
      writer.print("(define-fun %s_step ((inputs Inputs)) Outputs", name.c_str());

    writer.print(" (let (");
    for (const auto &input : ir.inputs()) {
      std::string input_name = scope[input.first];
      writer.print(" (%s (%s inputs))", input_name.c_str(), input_name.c_str());
    }
    writer.print(" )");

    auto node_to_string = [&](FunctionalIR::Node n) { return scope[n.name()]; };
    SmtPrintVisitor<decltype(node_to_string)> visitor(node_to_string, scope);

    for (auto it = ir.begin(); it != ir.end(); ++it) {
      const FunctionalIR::Node &node = *it;

      if (ir.inputs().count(node.name()) > 0)
	continue;

      std::string node_name = scope[node.name()];
      std::string node_expr = node.visit(visitor);

      writer.print(" (let ( (%s %s))", node_name.c_str(), node_expr.c_str());
    }

    if (stateful) {
      writer.print(" (let ( (next_state (mk_state ");
      for (const auto &state : ir.state()) {
	std::string state_name = scope[state.first];
	const std::string state_assignment = ir.get_state_next_node(state.first).name().c_str();
	writer.print(" %s", state_assignment.substr(1).c_str());
      }
      writer.print(" )))");
    }

    if (stateful) {
      writer.print(" (let ( (outputs (mk_outputs ");
      for (const auto &output : ir.outputs()) {
	std::string output_name = scope[output.first];
	writer.print(" %s", output_name.c_str());
      }
      writer.print(" )))");

      writer.print("(mk-pair outputs next_state)");
    }
    else {
      writer.print(" (mk_outputs ");
      for (const auto &output : ir.outputs()) {
	std::string output_name = scope[output.first];
	writer.print(" %s", output_name.c_str());
      }
      writer.print(" )"); // Closing mk_outputs 
    }
    if (stateful) {
      writer.print(" )"); // Closing outputs let statement
      writer.print(" )"); // Closing next_state let statement
    }
    // Close the nested lets
    for (size_t i = 0; i < ir.size() - ir.inputs().size(); ++i) {
      writer.print(" )"); // Closing each node
    }

    writer.print(" )"); // Closing inputs let statement
    writer.print(")\n"); // Closing step function
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
      auto ir = FunctionalIR::from_module(module);
      SmtModule smt(RTLIL::unescape_id(module->name), ir);
      smt.write(*f);
    }
  }
} FunctionalSmtBackend;

PRIVATE_NAMESPACE_END
