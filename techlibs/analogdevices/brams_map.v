module $__ANALOGDEVICES_BLOCKRAM_FULL_ (...);
	// libmap params
	parameter INIT = 0;
	parameter OPTION_MODE = "NONE";
	parameter OPTION_SIZE = "NONE";
	parameter OPTION_ERR = "NONE";
	parameter PORT_A_WR_EN_WIDTH = 1;
	parameter PORT_A_CLK_POL = 1;
	parameter PORT_B_WR_EN_WIDTH = PORT_A_WR_EN_WIDTH;
	parameter PORT_B_CLK_POL = 1;

	// needs -force-params
	parameter WIDTH = 40;
	parameter ABITS = 13;

	// non libmap params
`ifdef IS_T40LP
	localparam NODE = "T40LP_Gen2.4";
`endif
`ifdef IS_T16FFC
	localparam NODE = "T16FFC_Gen2.4";
`endif
	// localparam BRAM_MODE = "SDP_2048x36_BP";
	localparam BRAM_MODE = (OPTION_ERR!="NONE") ? {OPTION_MODE, "_", OPTION_SIZE, "_", OPTION_ERR} :
							{OPTION_MODE, "_", OPTION_SIZE};
	localparam PBITS = 	(OPTION_ERR=="BP") ? PORT_A_WR_EN_WIDTH : 1;

	// libmap ports
	input PORT_A_CLK;
	input PORT_A_CLK_EN;
	input [ABITS-1:0] PORT_A_ADDR;
	input [WIDTH-1:0] PORT_A_WR_DATA;
	output [WIDTH-1:0] PORT_A_RD_DATA;
	input [PORT_A_WR_EN_WIDTH-1:0] PORT_A_WR_EN;

	input PORT_B_CLK;
	input PORT_B_CLK_EN;
	input [ABITS-1:0] PORT_B_ADDR;
	input [WIDTH-1:0] PORT_B_WR_DATA;
	output [WIDTH-1:0] PORT_B_RD_DATA;
	input [PORT_B_WR_EN_WIDTH-1:0] PORT_B_WR_EN;

`ifdef IS_T40LP
	RBRAM
`endif
`ifdef IS_T16FFC
	RBRAM2
`endif
	#(
		.TARGET_NODE(NODE),
		.BRAM_MODE(BRAM_MODE),
		.QA_REG((OPTION_ERR=="ECC") ? 1 : 0),
		.QB_REG((OPTION_ERR=="ECC") ? 1 : 0),
		.CLKA_INV(!PORT_A_CLK_POL),
		.CLKB_INV(!PORT_B_CLK_POL),
		.DATA_WIDTH(WIDTH),
		.ADDR_WIDTH(ABITS),
		.WE_WIDTH(PORT_A_WR_EN_WIDTH),
		.PERR_WIDTH(PBITS),
	)
	_TECHMAP_REPLACE_
	(
		.QA(PORT_A_RD_DATA),
		.DA(PORT_A_WR_DATA),
		.CEA(PORT_A_CLK_EN),
		.WEA(PORT_A_WR_EN),
		.AA(PORT_A_ADDR),
		.CLKA(PORT_A_CLK),
		.QB(PORT_B_RD_DATA),
		.DB(PORT_B_WR_DATA),
		.CEB(PORT_B_CLK_EN),
		.WEB(PORT_B_WR_EN),
		.AB(PORT_B_ADDR),
		.CLKB(PORT_B_CLK),
	);

	// check config
	generate
		if (PORT_A_WR_EN_WIDTH == PORT_B_WR_EN_WIDTH)
		case (BRAM_MODE)
		`ifdef IS_T40LP
			"SDP_1024x18_FP",
			"SDP_1024x16_BP",
			"SDP_2048x09",
			"SDP_4096x05",
			"SDP_1024x32_ECC",
			"SDP_1024x40",
			"SDP_1024x36_BP",
			"SDP_512x32_ECC",
			"SDP_512x36_BP",
			"SDP_2048x10",
			"SP_512x32_ECC",
			"SP_512x36_BP",
			"SP_1024x20",
			"SP2_512x18_BP",
			"SP2_1024x09",
			"SP2_2048x05": wire _TECHMAP_FAIL_ = 0;
		`endif
		`ifdef IS_T16FFC
			"TDP_2048x18_FP",
			"TDP_2048x16_BP",
			"TDP_4096x09",
			"TDP_8192x05",
			"TDP_2048x32_ECC",
			"TDP_2048x40",
			"TDP_2048x36_BP",
			"SDP_2048x18_FP",
			"SDP_2048x16_BP",
			// The following are rejected in eXpreso
			// "SDP_4096x09",
			// "SDP_8192x05",
			// "SDP_2048x32_ECC",
			// "SDP_2048x40",
			// "SDP_2048x36_BP",
			"SDP_1024x32_ECC",
			"SDP_1024x36_BP",
			"SDP_4096x10",
			"SP_1024x32_ECC",
			"SP_1024x36_BP",
			"SP_2048x20",
			"SP2_1024x18_BP",
			"SP2_2048x09",
			"SP2_4096x05": wire _TECHMAP_FAIL_ = 0;
		`endif
			default: wire _TECHMAP_FAIL_ = 1;
		endcase
		else
			wire _TECHMAP_FAIL_ = 1;
	endgenerate

endmodule

module $__ANALOGDEVICES_BLOCKRAM_HALF_ (...);
	// libmap params
	parameter INIT = 0;
	parameter OPTION_MODE = "NONE";
	parameter OPTION_SIZE = "NONE";
	parameter OPTION_ERR = "NONE";
	parameter PORT_A_WR_EN_WIDTH = 1;
	parameter PORT_A_CLK_POL = 1;
	parameter PORT_B_WR_EN_WIDTH = PORT_A_WR_EN_WIDTH;
	parameter PORT_B_CLK_POL = 1;

	// needs -force-params
	parameter WIDTH = 40;
	parameter ABITS = 13;

	// libmap ports
	input PORT_A_CLK;
	input PORT_A_CLK_EN;
	input [ABITS-1:0] PORT_A_ADDR;
	input [WIDTH-1:0] PORT_A_WR_DATA;
	output [WIDTH-1:0] PORT_A_RD_DATA;
	input [PORT_A_WR_EN_WIDTH-1:0] PORT_A_WR_EN;

	input PORT_B_CLK;
	input PORT_B_CLK_EN;
	input [ABITS-1:0] PORT_B_ADDR;
	input [WIDTH-1:0] PORT_B_WR_DATA;
	output [WIDTH-1:0] PORT_B_RD_DATA;
	input [PORT_B_WR_EN_WIDTH-1:0] PORT_B_WR_EN;

	$__ANALOGDEVICES_BLOCKRAM_FULL_
	# (
		.INIT(INIT),
		.OPTION_MODE(OPTION_MODE),
		.OPTION_SIZE(OPTION_SIZE),
		.OPTION_ERR(OPTION_ERR),
		.PORT_A_WR_EN_WIDTH(PORT_A_WR_EN_WIDTH),
		.PORT_A_CLK_POL(PORT_A_CLK_POL),
		.PORT_B_WR_EN_WIDTH(PORT_B_WR_EN_WIDTH),
		.PORT_B_CLK_POL(PORT_B_CLK_POL),
		.WIDTH(WIDTH),
		.ABITS(ABITS)
	)
	_TECHMAP_REPLACE_
	(
		.PORT_A_CLK(PORT_A_CLK),
		.PORT_A_CLK_EN(PORT_A_CLK_EN),
		.PORT_A_ADDR(PORT_A_ADDR),
		.PORT_A_WR_DATA(PORT_A_WR_DATA),
		.PORT_A_RD_DATA(PORT_A_RD_DATA),
		.PORT_A_WR_EN(PORT_A_WR_EN),
		.PORT_B_CLK(PORT_B_CLK),
		.PORT_B_CLK_EN(PORT_B_CLK_EN),
		.PORT_B_ADDR(PORT_B_ADDR),
		.PORT_B_WR_DATA(PORT_B_WR_DATA),
		.PORT_B_RD_DATA(PORT_B_RD_DATA),
		.PORT_B_WR_EN(PORT_B_WR_EN)
	);
endmodule

module $__ANALOGDEVICES_BLOCKRAM_QUARTER_ (...);
	// libmap params
	parameter INIT = 0;
	parameter OPTION_MODE = "NONE";
	parameter OPTION_SIZE = "NONE";
	parameter OPTION_ERR = "NONE";
	parameter PORT_A_WR_EN_WIDTH = 1;
	parameter PORT_A_CLK_POL = 1;
	parameter PORT_B_WR_EN_WIDTH = PORT_A_WR_EN_WIDTH;
	parameter PORT_B_CLK_POL = 1;

	// needs -force-params
	parameter WIDTH = 40;
	parameter ABITS = 13;

	// libmap ports
	input PORT_A_CLK;
	input PORT_A_CLK_EN;
	input [ABITS-1:0] PORT_A_ADDR;
	input [WIDTH-1:0] PORT_A_WR_DATA;
	output [WIDTH-1:0] PORT_A_RD_DATA;
	input [PORT_A_WR_EN_WIDTH-1:0] PORT_A_WR_EN;

	$__ANALOGDEVICES_BLOCKRAM_FULL_
	# (
		.INIT(INIT),
		.OPTION_MODE(OPTION_MODE),
		.OPTION_SIZE(OPTION_SIZE),
		.OPTION_ERR(OPTION_ERR),
		.PORT_A_WR_EN_WIDTH(PORT_A_WR_EN_WIDTH),
		.PORT_A_CLK_POL(PORT_A_CLK_POL),
		.PORT_B_WR_EN_WIDTH(PORT_B_WR_EN_WIDTH),
		.PORT_B_CLK_POL(PORT_B_CLK_POL),
		.WIDTH(WIDTH),
		.ABITS(ABITS)
	)
	_TECHMAP_REPLACE_
	(
		.PORT_A_CLK(PORT_A_CLK),
		.PORT_A_CLK_EN(PORT_A_CLK_EN),
		.PORT_A_ADDR(PORT_A_ADDR),
		.PORT_A_WR_DATA(PORT_A_WR_DATA),
		.PORT_A_RD_DATA(PORT_A_RD_DATA),
		.PORT_A_WR_EN(PORT_A_WR_EN),
	);
endmodule
