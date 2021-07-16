// A basic example of the bind construct
//
// act contains an instance of foo. foo is empty, but we bind in an instance of bar to do the XOR.
// gold is the "reference implementation" that contains a bar with no binding required.
//
// The code to drive this is in basic.ys, which runs the hierarchy pass (to insert the bound
// module), flattens the design and then runs an equivalence check between act and gold.

module foo (input logic a, input logic b, output logic c);
  // Magic happens here...
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module act (input u, input v, output w);
  foo foo_i (.a (u), .b (v), .c (w));
  bind foo bar bound_i (.*);
endmodule

module gold (input u, input v, output w);
  assign w = u ^ v;
endmodule
