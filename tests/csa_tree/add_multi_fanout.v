module add_multi_fanout(
	input  [7:0] a, b, c,
	output [7:0] mid,
	output [7:0] y
);
	wire [7:0] ab = a + b;
	assign mid = ab;
	assign y   = ab + c;
endmodule

