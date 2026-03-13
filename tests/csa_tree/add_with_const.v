module add_with_const(
	input  [7:0] a, b, c,
	output [7:0] y
);
	assign y = a + b + c + 8'd42;
endmodule

