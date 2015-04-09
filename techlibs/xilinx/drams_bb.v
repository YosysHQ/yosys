
module RAM64X1D (
	output DPO, SPO,
	input  D, WCLK, WE,
	input  A0, A1, A2, A3, A4, A5,
	input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4, DPRA5
);
	parameter INIT = 64'h0;
	parameter IS_WCLK_INVERTED = 1'b0;
endmodule

module RAM128X1D (
	output       DPO, SPO,
	input        D, WCLK, WE,
	input  [6:0] A, DPRA
);
	parameter INIT = 128'h0;
	parameter IS_WCLK_INVERTED = 1'b0;
endmodule

