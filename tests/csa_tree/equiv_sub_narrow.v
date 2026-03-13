module equiv_sub_mixed(
	input  [3:0] a, b, c, d,
	output [3:0] y
);
	assign y = a + b - c + d;
endmodule

module equiv_sub_all(
	input  [3:0] a, b, c, d,
	output [3:0] y
);
	assign y = a - b - c - d;
endmodule

module equiv_sub_3op(
	input  [3:0] a, b, c,
	output [3:0] y
);
	assign y = a - b + c;
endmodule

module equiv_sub_signed(
	input  signed [3:0] a, b, c, d,
	output signed [5:0] y
);
	assign y = a + b - c - d;
endmodule
