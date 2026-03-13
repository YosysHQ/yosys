module add_multi_const(
	input  [7:0] x,
	output [7:0] y
);
	assign y = 8'd1 + 8'd2 + 8'd3 + x;
endmodule
