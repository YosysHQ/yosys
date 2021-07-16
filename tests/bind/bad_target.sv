// An example of a bind construct that points at a non-existent target

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

bind cabbage bar bound_i (.*);
