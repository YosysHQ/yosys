module sub_double_neg(
	input  [7:0] a, b, c,
	output [7:0] y
);
	wire [7:0] ab = a - b;
	assign y = c - ab;
endmodule
