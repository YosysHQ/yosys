
module RAM32X1D (
	output DPO, SPO,
	input  A0, A1, A2, A3, A4, D,
	input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4,
	input  WCLK, WE
);
	parameter INIT = 32'h0;
	parameter IS_WCLK_INVERTED = 1'b0;
endmodule

