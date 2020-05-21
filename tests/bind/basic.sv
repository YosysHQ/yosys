// A basic example of the bind construct

module foo (input logic a, input logic b, output logic c);
  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module top ();
  logic u, v, w;
  foo foo_i (.a (u), .b (v), .c (w));

  bind foo bar bound_i (.*);

  always_comb begin
    assert(w == u ^ v);
  end
endmodule
