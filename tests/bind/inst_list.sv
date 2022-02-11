// An example of specifying multiple bind targets with an instance list

module foo (input logic a, input logic b, output logic c);
  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module top ();
  logic u0, v0, w0;
  logic u1, v1, w1;

  foo foo0 (.a (u0), .b (v0), .c (w0));
  foo foo1 (.a (u1), .b (v1), .c (w1));

  bind foo : foo0, foo1 bar bound_i (.*);

  always_comb begin
    assert(w0 == u0 ^ v0);
    assert(w1 == u1 ^ v1);
  end
endmodule
