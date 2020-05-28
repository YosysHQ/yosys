// The bind construct occurring at top-level in the script

module foo (input logic a, input logic b, output logic c);
  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module act (input u, input v, output w);
  foo foo_i (.a (u), .b (v), .c (w));
endmodule

bind act.foo_i bar bound_i (.*);

module ref (input u, input v, output w);
  assign w = u ^ v;
endmodule
