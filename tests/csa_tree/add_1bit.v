// Edge case for carry shifting

module add_1bit(
	input  a, b, c,
	output [1:0] y
);
	assign y = a + b + c;
endmodule

