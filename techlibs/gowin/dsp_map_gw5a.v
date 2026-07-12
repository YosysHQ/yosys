module \$__MUL27X18 (input [26:0] A, input [17:0] B, output [44:0] Y);

    parameter A_WIDTH = 27;
    parameter B_WIDTH = 18;
    parameter Y_WIDTH = 45;
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;

	wire [47:0] dout_w;

	MULTALU27X18 #(
		.MULT12X12_EN("FALSE"),
		.MULT_RESET_MODE("SYNC"),
		.AREG_CLK("BYPASS"),
		.BREG_CLK("BYPASS"),
		.PREG_CLK("BYPASS"),
		.OREG_CLK("BYPASS")
	) __TECHMAP_REPLACE__ (
		.DOUT(dout_w),
		.CASO(),
		.SOA(),
		.A(A),
		.SIA(27'd0),
		.B(B),
		.C(48'd0),
		.D(26'd0),
		.CASI(48'd0),
		.ACCSEL(1'b0),
		.PSEL(1'b0),
		.ASEL(1'b0),
		.PADDSUB(1'b0),
		.CSEL(1'b0),
		.CASISEL(1'b0),
		.ADDSUB(2'b00),
		.CLK(2'b00),
		.CE(2'b00),
		.RESET(2'b00)
	);

	assign Y = dout_w[44:0];

endmodule

module \$__MUL12X12 (input [11:0] A, input [11:0] B, output [23:0] Y);

    parameter A_WIDTH = 12;
    parameter B_WIDTH = 12;
    parameter Y_WIDTH = 24;
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;

	MULT12X12 #(
		.MULT_RESET_MODE("SYNC"),
		.AREG_CLK("BYPASS"),
		.BREG_CLK("BYPASS"),
		.PREG_CLK("BYPASS"),
		.OREG_CLK("BYPASS")
	) __TECHMAP_REPLACE__ (
		.DOUT(Y),
		.A(A),
		.B(B),
		.CLK(2'b00),
		.CE(2'b00),
		.RESET(2'b00)
	);

endmodule

module \$__MUL27X36 (input [26:0] A, input [35:0] B, output [62:0] Y);

    parameter A_WIDTH = 27;
    parameter B_WIDTH = 36;
    parameter Y_WIDTH = 63;
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;

	MULT27X36 #(
		.MULT_RESET_MODE("SYNC"),
		.AREG_CLK("BYPASS"),
		.BREG_CLK("BYPASS"),
		.PREG_CLK("BYPASS"),
		.OREG_CLK("BYPASS")
	) __TECHMAP_REPLACE__ (
		.DOUT(Y),
		.A(A),
		.B(B),
		.D(26'd0),
		.PSEL(1'b0),
		.PADDSUB(1'b0),
		.CLK(2'b00),
		.CE(2'b00),
		.RESET(2'b00)
	);

endmodule
