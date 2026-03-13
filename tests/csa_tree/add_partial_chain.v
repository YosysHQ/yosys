module add_partial_chain(
	input  [7:0] a, b, c, d, e,
	output [7:0] mid,
	output [7:0] y
);
	wire [7:0] ab = a + b;
	assign mid = ab;
	assign y = ab + c + d + e;
endmodule
