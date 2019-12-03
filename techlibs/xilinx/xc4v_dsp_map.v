module \$__MUL18X18 (input [17:0] A, input [17:0] B, output [35:0] Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter B_WIDTH = 0;
	parameter Y_WIDTH = 0;

	wire [47:0] P_48;
	DSP48 #(
		// Disable all registers
		.AREG(0),
		.BREG(0),
		.B_INPUT("DIRECT"),
		.CARRYINREG(0),
		.CARRYINSELREG(0),
		.CREG(0),
		.MREG(0),
		.OPMODEREG(0),
		.PREG(0),
		.SUBTRACTREG(0),
		.LEGACY_MODE("MULT18X18")
	) _TECHMAP_REPLACE_ (
		//Data path
		.A(A),
		.B(B),
		.C(48'b0),
		.P(P_48),

		.SUBTRACT(1'b0),
		.OPMODE(7'b000101),
		.CARRYINSEL(2'b00),

		.BCIN(18'b0),
		.PCIN(48'b0),
		.CARRYIN(1'b0)
	);
	assign Y = P_48;
endmodule
