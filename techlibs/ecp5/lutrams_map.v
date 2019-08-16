module \$__TRELLIS_DPR16X4 (CLK1, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter [63:0] INIT = 64'bx;
	parameter CLKPOL2 = 1;
	input CLK1;

	input [3:0] A1ADDR;
	output [3:0] A1DATA;

	input [3:0] B1ADDR;
	input [3:0] B1DATA;
	input B1EN;

	localparam WCKMUX = CLKPOL2 ? "WCK" : "INV";

	TRELLIS_DPR16X4 #(
		.INITVAL(INIT),
		.WCKMUX(WCKMUX),
		.WREMUX("WRE")
	) _TECHMAP_REPLACE_ (
		.RAD(A1ADDR),
		.DO(A1DATA),

		.WAD(B1ADDR),
		.DI(B1DATA),
		.WCK(CLK1),
		.WRE(B1EN)
	);
endmodule
