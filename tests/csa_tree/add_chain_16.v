module add_chain_16(
	input  [15:0] a0, a1, a2, a3, a4, a5, a6, a7,
	input  [15:0] a8, a9, a10, a11, a12, a13, a14, a15,
	output [15:0] y
);
	assign y = a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15;
endmodule
