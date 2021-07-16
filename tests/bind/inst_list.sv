// An example of specifying multiple bind targets with an instance list

module foo (input logic a, input logic b, output logic c);
  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module act (input u0, input v0, output w0,
            input u1, input v1, output w1);
  foo foo0 (.a (u0), .b (v0), .c (w0));
  foo foo1 (.a (u1), .b (v1), .c (w1));

  bind foo : foo0, foo1 bar bound_i (.*);
endmodule

module gold (input u0, input v0, output w0,
             input u1, input v1, output w1);
  assign w0 = u0 ^ v0;
  assign w1 = u1 ^ v1;
endmodule
