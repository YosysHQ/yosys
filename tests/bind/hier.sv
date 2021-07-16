// An example of a bind construct at top-level using a hierarchical reference
// starting with $root
//

module foo (input logic a, input logic b, output logic c);
  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module act (input u, input v, output w);
  foo foo_i (.a (u), .b (v), .c (w));
endmodule

bind $root.act.foo_i bar bound_i (.*);

module ref (input u, input v, output w);
  assign w = u ^ v;
endmodule
