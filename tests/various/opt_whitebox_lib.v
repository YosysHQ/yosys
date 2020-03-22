(* lib_whitebox *)
module and2(input a, b, output y);
	assign y = a & b;
endmodule

(* lib_whitebox *)
module or2(input a, b, output y);
	assign y = a | b;
endmodule
