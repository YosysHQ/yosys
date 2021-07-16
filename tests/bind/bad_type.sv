// An example of a bind construct using bind_target_instance_list which points at the wrong sort of
// cell.

module foo0 (input logic a, input logic b, output logic c);
endmodule

module foo1 (input logic a, input logic b, output logic c);
endmodule

module bar (input a, input b, output c);
  assign c = a ^ b;
endmodule

module act (input u, input v, output w);
  foo0 foo_i (.a (u), .b (v), .c (w));
  bind foo1 : foo_i bar bound_i (.*);
endmodule
