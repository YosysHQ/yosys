module sim_add4(
	input  [7:0] a, b, c, d,
	output [7:0] y
);
	assign y = a + b + c + d;
endmodule
