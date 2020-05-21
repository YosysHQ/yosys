// The bind construct occurring at top-level in the script

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

bind top.foo_i bar bound_i (.*);
