module \$__MUL18X18 (input [17:0] A, input [17:0] B, output [35:0] Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter B_WIDTH = 0;
	parameter Y_WIDTH = 0;

	MULT18X18 _TECHMAP_REPLACE_ (
		.A(A),
		.B(B),
		.P(Y)
	);
endmodule

