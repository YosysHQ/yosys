module add_two_chains(
	input  [7:0] a, b, c, d,
	input  [7:0] e, f, g, h,
	output [7:0] y1,
	output [7:0] y2
);
	assign y1 = a + b + c + d;
	assign y2 = e + f + g + h;
endmodule
