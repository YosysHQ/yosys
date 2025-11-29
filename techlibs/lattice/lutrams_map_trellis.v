module $__TRELLIS_DPR16X4_(...);

parameter INIT = 64'bx;
parameter PORT_W_CLK_POL = 1;

input PORT_W_CLK;
input [3:0] PORT_W_ADDR;
input [3:0] PORT_W_WR_DATA;
input PORT_W_WR_EN;

input [3:0] PORT_R_ADDR;
output [3:0] PORT_R_RD_DATA;

localparam WCKMUX = PORT_W_CLK_POL ? "WCK" : "INV";

TRELLIS_DPR16X4 #(
	.INITVAL(INIT),
	.WCKMUX(WCKMUX),
	.WREMUX("WRE")
) _TECHMAP_REPLACE_ (
	.RAD(PORT_R_ADDR),
	.DO(PORT_R_RD_DATA),

	.WAD(PORT_W_ADDR),
	.DI(PORT_W_WR_DATA),
	.WCK(PORT_W_CLK),
	.WRE(PORT_W_WR_EN)
);

endmodule
