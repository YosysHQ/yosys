module add_mixed_widths(
	input  [7:0]  a,
	input  [3:0]  b,
	input  [15:0] c,
	input  [7:0]  d,
	output [15:0] y
);
	assign y = a + b + c + d;
endmodule

