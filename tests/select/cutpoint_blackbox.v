(* blackbox *)
module add #(parameter N=3) (input [N-1:0] a, b, output [N-1:0] q);
endmodule

module top(input [7:0] a, b, output [7:0] q);
   add #(.N(8)) add_i(.a(a), .b(b), .q(q));
endmodule
