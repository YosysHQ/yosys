module sub_signed(
	input  signed [7:0] a, b, c, d,
	output signed [9:0] y
);
	assign y = a + b - c - d;
endmodule
