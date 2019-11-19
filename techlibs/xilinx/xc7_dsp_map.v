module \$__MUL25X18 (input [24:0] A, input [17:0] B, output [42:0] Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter B_WIDTH = 0;
	parameter Y_WIDTH = 0;

	wire [47:0] P_48;
	DSP48E1 #(
		// Disable all registers
		.ACASCREG(0),
		.ADREG(0),
		.A_INPUT("DIRECT"),
		.ALUMODEREG(0),
		.AREG(0),
		.BCASCREG(0),
		.B_INPUT("DIRECT"),
		.BREG(0),
		.CARRYINREG(0),
		.CARRYINSELREG(0),
		.CREG(0),
		.DREG(0),
		.INMODEREG(0),
		.MREG(0),
		.OPMODEREG(0),
		.PREG(0),
		.USE_MULT("MULTIPLY"),
		.USE_SIMD("ONE48"),
		.USE_DPORT("FALSE")
	) _TECHMAP_REPLACE_ (
		//Data path
		.A({{5{A[24]}}, A}),
		.B(B),
		.C(48'b0),
		.D(25'b0),
		.P(P_48),

		.INMODE(5'b00000),
		.ALUMODE(4'b0000),
		.OPMODE(7'b000101),
		.CARRYINSEL(3'b000),

		.ACIN(30'b0),
		.BCIN(18'b0),
		.PCIN(48'b0),
		.CARRYIN(1'b0)
	);
	assign Y = P_48;
endmodule
