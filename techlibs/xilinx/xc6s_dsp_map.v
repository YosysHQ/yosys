module \$__MUL18X18 (input [17:0] A, input [17:0] B, output [35:0] Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter B_WIDTH = 0;
	parameter Y_WIDTH = 0;

	wire [47:0] P_48;
	DSP48A1 #(
		// Disable all registers
		.A0REG(0),
		.A1REG(0),
		.B0REG(0),
		.B1REG(0),
		.CARRYINREG(0),
		.CARRYINSEL("OPMODE5"),
		.CREG(0),
		.DREG(0),
		.MREG(0),
		.OPMODEREG(0),
		.PREG(0)
	) _TECHMAP_REPLACE_ (
		//Data path
		.A(A),
		.B(B),
		.C(48'b0),
		.D(18'b0),
		.P(P_48),

		.OPMODE(8'b0000001)
	);
	assign Y = P_48;
endmodule


