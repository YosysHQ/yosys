module \$__MUL22X22 (input [21:0] A, input [21:0] B, output [43:0] Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter B_WIDTH = 0;
	parameter Y_WIDTH = 0;

	wire [47:0] P_48;
	RBBDSP #(
		// Disable all registers
		.AI_SEL_IN(1'b0),
		.BC_CI(2'b00),
		.BI_SEL(1'b0),
		.BI_SEL_IN(1'b0),
		.CE_A(1'b0),
		.CE_ADD(1'b0),
		.CE_B(1'b0),
		.CE_C(1'b0),
		.CE_CRY(1'b0),
		.CE_D(2'b0),
		.CE_M(1'b0),
		.CE_OPCODE(1'b0),
		.CE_PADD(1'b0),
		.CE_RST(1'b1),
		.CE_SEL(1'b0),
		.CE_SFT(1'b0),
		.CI_SEL(4'd3),
		.DI_SEL(1'b0),
		.DI_SEL_IN(1'b0),
		.OPCODE_SEL(1'b0),
		.OP_ADD(10'b0),
		.OP_CPLX(1'b0),
		.OP_MULT(2'b11),
		.OP_PADD(10'b0000000000),
		.OP_SFT(6'b000000),
		.OP_X(4'b1010),
		.OP_Y(4'b0101),
		.OP_Z(4'b0000),
		.PO_LOC_SEL(1'b1),
		.PO_NWK_SEL(1'b1),
		.REG_A(1'b0),
		.REG_ADD(1'b0),
		.REG_B(1'b0),
		.REG_C(1'b0),
		.REG_CRY(1'b0),
		.REG_D(2'b0),
		.REG_M(1'b0),
		.REG_OPCODE(1'b0),
		.REG_PADD(1'b0),
		.REG_SFT(1'b0),
		.RST_SEL(1'b0),
		.FF_SYNC_RST(1'b0),
	) _TECHMAP_REPLACE_ (
		.P(P_48),
		.A(A),
		.B(B),
		.D(48'b0)
	);
	assign Y = P_48;
endmodule
