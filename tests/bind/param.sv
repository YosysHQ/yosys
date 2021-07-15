// An example showing how parameters get inferred when binding

module foo (input logic a, input logic b, output logic c);
  parameter doit = 1;

  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  parameter doit = 1;

  assign c = doit ? a ^ b : 0;
endmodule

module act (input u0, input v0, output w0,
            input u1, input v1, output w1);
  foo #(.doit (0)) foo0 (.a (u0), .b (v0), .c (w0));
  foo #(.doit (1)) foo1 (.a (u1), .b (v1), .c (w1));

  bind foo bar #(.doit (doit)) bound_i (.*);
endmodule

module ref (input u0, input v0, output w0,
            input u1, input v1, output w1);
  assign w0 = 0;
  assign w1 = u1 ^ v1;
endmodule
