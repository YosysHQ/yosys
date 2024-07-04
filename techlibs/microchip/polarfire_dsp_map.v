/*
ISC License

Copyright (C) 2024 Microchip Technology Inc. and its subsidiaries

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

module \$__MUL18X18 (input [17:0] A, input [17:0] B, output [35:0] Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 0;
	parameter B_WIDTH = 0;
	parameter Y_WIDTH = 0;

	wire [47:0] P_48;
	// For pin descriptions, see Section 9 of PolarFire FPGA Macro Library Guide:
	// https://coredocs.s3.amazonaws.com/Libero/2021_2/Tool/pf_mlg.pdf
	MACC_PA _TECHMAP_REPLACE_ (
		.DOTP(1'b0), 
		.SIMD(1'b0), 
		.OVFL_CARRYOUT_SEL(1'b0), 

		.AL_N(1'b1),
		.A(A),
		.A_BYPASS(1'b1),
		.A_SRST_N(1'b1),
		.A_EN(1'b1),

		.B(B),
		.B_BYPASS(1'b1),
		.B_SRST_N(1'b1),
		.B_EN(1'b1),

		.D(18'b0),
		.D_BYPASS(1'b1),
		.D_ARST_N(1'b1),
		.D_SRST_N(1'b1),
		.D_EN(1'b1),
		
		.CARRYIN(1'b0),
		.C(48'b0),
		.C_BYPASS(1'b1),
		.C_ARST_N(1'b1),
		.C_SRST_N(1'b1),
		.C_EN(1'b1),

		
		.P(P_48),

		.P_BYPASS(1'b1),
		.P_SRST_N(1'b1),
		.P_EN(1'b1),

		.PASUB(1'b0),
		.PASUB_BYPASS(1'b1),
		.PASUB_AD_N(1'b0),
		.PASUB_SL_N(1'b1),
		.PASUB_SD_N(1'b0),
		.PASUB_EN(1'b1),

		.CDIN_FDBK_SEL(2'b00),
		.CDIN_FDBK_SEL_BYPASS(1'b1),
		.CDIN_FDBK_SEL_AD_N(2'b00),
		.CDIN_FDBK_SEL_SL_N(1'b1),
		.CDIN_FDBK_SEL_SD_N(2'b00),
		.CDIN_FDBK_SEL_EN(1'b1),

		.ARSHFT17(1'b0),
		.ARSHFT17_BYPASS(1'b1),
		.ARSHFT17_AD_N(1'b0),
		.ARSHFT17_SL_N(1'b1),
		.ARSHFT17_SD_N(1'b0),
		.ARSHFT17_EN(1'b1),

		.SUB(1'b0),
		.SUB_BYPASS(1'b1),
		.SUB_AD_N(1'b0),
		.SUB_SL_N(1'b1),
		.SUB_SD_N(1'b0),
		.SUB_EN(1'b1)

	);
	assign Y = P_48;
endmodule
