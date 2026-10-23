module real_cond(input i, output a, b, c);
	localparam real Q = 0.25, N = -0.0;
	assign a = Q ? 1 : 0;
	assign b = N ? 1 : 0;
	reg r;
	always @* if (Q) r = i; else r = ~i;
	assign c = r;
endmodule
