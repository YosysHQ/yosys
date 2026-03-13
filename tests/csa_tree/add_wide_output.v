module add_wide_output(
	input  [7:0] a, b, c, d,
	output [31:0] y
);
	assign y = a + b + c + d;
endmodule
