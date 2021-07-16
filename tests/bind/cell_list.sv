// An example of specifying multiple bind instances in a single directive. This
// also uses explicit bound names.

module foo (input logic a0, input logic b0, output logic c0,
            input logic a1, input logic b1, output logic c1);
  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module act (input u0, input v0, output w0,
            input u1, input v1, output w1);
  foo foo0 (.a0 (u0), .b0 (v0), .c0 (w0),
            .a1 (u1), .b1 (v1), .c1 (w1));

  bind foo bar bar0 (.a(a0), .b(b0), .c(c0)), bar1 (.a(a1), .b(b1), .c(c1));
endmodule

module gold (input u0, input v0, output w0,
             input u1, input v1, output w1);
  assign w0 = u0 ^ v0;
  assign w1 = u1 ^ v1;
endmodule
