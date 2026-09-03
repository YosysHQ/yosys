module \$macc_v2 (A, B, C, Y);

	parameter NPRODUCTS = 0;
	parameter PRODUCT_NEGATED = 1'b0;
	parameter NADDENDS = 0;
	parameter ADDEND_NEGATED = 1'b0;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter C_SIGNED = 0;
	parameter A_WIDTHS = 1;
	parameter B_WIDTHS = 1;
	parameter C_WIDTHS = 1;
	parameter Y_WIDTH = 1;

	input  [A_WIDTHS-1:0]  A;
	input  [B_WIDTHS-1:0]  B;
	input  [C_WIDTHS-1:0]  C;
	output [Y_WIDTH-1:0]   Y;

	wire _TECHMAP_FAIL_ = !(NPRODUCTS == 1 && NADDENDS == 1 &&
		PRODUCT_NEGATED == 1'b0 && ADDEND_NEGATED == 1'b0 &&
		A_SIGNED && B_SIGNED && C_SIGNED &&
		A_WIDTHS <= 27 && B_WIDTHS <= 18 && C_WIDTHS <= 48);

	wire [47:0] dout_w;

	MULTALU27X18 #(
		.MULT12X12_EN("FALSE"),
		.MULT_RESET_MODE("SYNC"),
		.AREG_CLK("BYPASS"),
		.BREG_CLK("BYPASS"),
		.PREG_CLK("BYPASS"),
		.OREG_CLK("BYPASS"),
		.DYN_C_SEL("TRUE")
	) __TECHMAP_REPLACE__ (
		.DOUT(dout_w),
		.CASO(),
		.SOA(),
		.A(A),
		.SIA(27'd0),
		.B(B),
		.C(C),
		.D(26'd0),
		.CASI(48'd0),
		.ACCSEL(1'b0),
		.PSEL(1'b0),
		.ASEL(1'b0),
		.PADDSUB(1'b0),
		.CSEL(1'b1),
		.CASISEL(1'b0),
		.ADDSUB(2'b00),
		.CLK(2'b00),
		.CE(2'b00),
		.RESET(2'b00)
	);

	assign Y = dout_w;

endmodule
