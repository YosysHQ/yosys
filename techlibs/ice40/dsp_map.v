module \$__MUL16X16 (input [15:0] A, input [15:0] B, output [31:0] Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter B_WIDTH = 0;
	parameter Y_WIDTH = 0;

	SB_MAC16 #(
		.NEG_TRIGGER(1'b0),
		.C_REG(1'b0),
		.A_REG(1'b0),
		.B_REG(1'b0),
		.D_REG(1'b0),
		.TOP_8x8_MULT_REG(1'b0),
		.BOT_8x8_MULT_REG(1'b0),
		.PIPELINE_16x16_MULT_REG1(1'b0),
		.PIPELINE_16x16_MULT_REG2(1'b0),
		.TOPOUTPUT_SELECT(2'b11),
		.TOPADDSUB_LOWERINPUT(2'b0),
		.TOPADDSUB_UPPERINPUT(1'b0),
		.TOPADDSUB_CARRYSELECT(2'b0),
		.BOTOUTPUT_SELECT(2'b11),
		.BOTADDSUB_LOWERINPUT(2'b0),
		.BOTADDSUB_UPPERINPUT(1'b0),
		.BOTADDSUB_CARRYSELECT(2'b0),
		.MODE_8x8(1'b0),
		.A_SIGNED(A_SIGNED),
		.B_SIGNED(B_SIGNED)
	) _TECHMAP_REPLACE_ (
		.A(A),
		.B(B),
		.O(Y),
	);
endmodule
