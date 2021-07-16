// An example of hierarchical bind names that include a named generate block
//
module foo1 (input logic a, input logic b, output logic c);
  // Magic happens here...
endmodule

module foo (input logic a, input logic b, output logic c);
  if (1'b1) begin : g_myblock
    foo1 f1 (.*);
  end
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module act (input u, input v, output w);
  foo foo_i (.a (u), .b (v), .c (w));
  bind foo.g_myblock.f1 bar bound_i (.*);
endmodule

module gold (input u, input v, output w);
  assign w = u ^ v;
endmodule
