module top(input a, b, output o);
assign o = a & b;
endmodule

(* blackbox *)
module bb(input a, b, output o);
assign o = a | b;
specify
	(a => o) = 1;
endspecify
endmodule

(* whitebox *)
module wb(input a, b, output o);
assign o = a ^ b;
endmodule
