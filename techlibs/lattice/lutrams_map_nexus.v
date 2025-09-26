module $__NEXUS_DPR16X4_ (...);
	parameter INIT = 64'b0;

	input PORT_W_CLK;
	input [3:0] PORT_W_ADDR;
	input [3:0] PORT_W_WR_DATA;
	input PORT_W_WR_EN;

	input [3:0] PORT_R_ADDR;
	output [3:0] PORT_R_RD_DATA;

	DPR16X4 #(
		.INITVAL($sformatf("0x%08x", INIT))
	) _TECHMAP_REPLACE_ (
		.RAD(PORT_R_ADDR),
		.DO(PORT_R_RD_DATA),

		.WAD(PORT_W_ADDR),
		.DI(PORT_W_WR_DATA),
		.WCK(PORT_W_CLK),
		.WRE(PORT_W_WR_EN)
	);
endmodule
