module $__ANALOGDEVICES_BLOCKRAM_SDP_ (...);

parameter INIT = 0;
parameter OPTION_ENABLE_WIDTH = "BIT";
parameter WIDTH = 40;

`ifdef IS_T40LP
parameter ABITS = 12;
localparam NODE = "T40LP_Gen2.4";
localparam BRAM_MODE = WIDTH ==  5 ? "SDP_4096x05" :
	WIDTH == 10 ? "SDP_2048x10" : "SDP_1024x40";
`elsif IS_T16FFC
parameter ABITS = 13;
localparam NODE = "T16FFC_Gen2.4";
localparam BRAM_MODE = WIDTH ==  5 ? "SDP_8192x05" :
	WIDTH == 10 ? "SDP_4096x10" : "SDP_2048x40";
`endif

parameter PORT_W_WR_EN_WIDTH = 5;
parameter PORT_W_CLK_POL = 1;

parameter PORT_R_CLK_POL = 1;

input PORT_W_CLK;
input PORT_W_CLK_EN;
input [ABITS-1:0] PORT_W_ADDR;
input [WIDTH-1:0] PORT_W_WR_DATA;
input [PORT_W_WR_EN_WIDTH-1:0] PORT_W_WR_EN;

input PORT_R_CLK;
input PORT_R_CLK_EN;
input [ABITS-1:0] PORT_R_ADDR;
output [WIDTH-1:0] PORT_R_RD_DATA;

`ifdef IS_T40LP
RBRAM
`endif
`ifdef IS_T16FFC
RBRAM2
`endif
#(
	.TARGET_NODE(NODE),
	.BRAM_MODE(BRAM_MODE),
	.QA_REG(0),
	.QB_REG(0),
	.CLKA_INV(!PORT_W_CLK_POL),
	.CLKB_INV(!PORT_R_CLK_POL),
	.DATA_WIDTH(WIDTH),
	.ADDR_WIDTH(
		WIDTH ==  5 ? ABITS :
		WIDTH == 10 ? ABITS-1 : ABITS-2
	),
	.WE_WIDTH(OPTION_ENABLE_WIDTH == "BIT" ? WIDTH : PORT_W_WR_EN_WIDTH),
	.PERR_WIDTH(1),
)
_TECHMAP_REPLACE_
(
	// .QA(0),
	.DA(PORT_W_WR_DATA),
	.CEA(PORT_W_CLK_EN),
	.WEA(PORT_W_WR_EN),
	.AA(
		WIDTH ==  5 ? PORT_W_ADDR :
		WIDTH == 10 ? PORT_W_ADDR[ABITS-1:1] : PORT_W_ADDR[ABITS-1:2]
	),
	.CLKA(PORT_W_CLK),
	.QB(PORT_R_RD_DATA),
	// .DB(0),
	.CEB(PORT_R_CLK_EN),
	// .WEB(0),
	.AB(
		WIDTH ==  5 ? PORT_R_ADDR :
		WIDTH == 10 ? PORT_R_ADDR[ABITS-1:1] : PORT_R_ADDR[ABITS-1:2]
	),
	.CLKB(PORT_R_CLK),
);

endmodule
