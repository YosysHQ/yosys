module add_1bit_wide_out(
	input  a, b, c, d,
	output [3:0] y
);
	assign y = a + b + c + d;
endmodule
