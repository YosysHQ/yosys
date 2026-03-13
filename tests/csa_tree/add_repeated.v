module add_repeated(
	input  [7:0] a,
	output [7:0] y
);
	assign y = a + a + a + a;
endmodule
