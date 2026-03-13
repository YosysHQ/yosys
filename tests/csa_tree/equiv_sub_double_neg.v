module equiv_sub_double_neg(
	input  [3:0] a, b, c,
	output [3:0] y
);
	wire [3:0] ab = a - b;
	assign y = c - ab;
endmodule
