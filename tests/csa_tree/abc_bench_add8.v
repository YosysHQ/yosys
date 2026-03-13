module abc_bench_add8(
	input  [7:0] a, b, c, d, e, f, g, h,
	output [7:0] y
);
	assign y = a + b + c + d + e + f + g + h;
endmodule
