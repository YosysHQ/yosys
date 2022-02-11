// An example of the bind construct using a hierarchical reference starting with $root

module foo (input logic a, input logic b, output logic c);
  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module top ();
  logic u, v, w;
  foo foo_i (.a (u), .b (v), .c (w));

  always_comb begin
    assert(w == u ^ v);
  end
endmodule

bind $root.top.foo_i bar bound_i (.*);
