module $__XILINX_URAM_ (...);
	parameter OPTION_BYTEWIDTH = 8;
	localparam WR_BE_WIDTH = 72 / OPTION_BYTEWIDTH;

	parameter CLK_C_POL = 1;
	parameter PORT_A_CLK_POL = 1;
	parameter PORT_A_OPTION_RST_MODE = "SYNC";
	parameter PORT_B_CLK_POL = 1;
	parameter PORT_B_OPTION_RST_MODE = "SYNC";

	input CLK_C;

	input PORT_A_CLK;
	input PORT_A_CLK_EN;
	input PORT_A_RD_SRST;
	input PORT_A_RD_ARST;
	input PORT_A_WR_EN;
	input [WR_BE_WIDTH-1:0] PORT_A_WR_BE;
	input [11:0] PORT_A_ADDR;
	input [71:0] PORT_A_WR_DATA;
	output [71:0] PORT_A_RD_DATA;

	input PORT_B_CLK;
	input PORT_B_CLK_EN;
	input PORT_B_RD_SRST;
	input PORT_B_RD_ARST;
	input PORT_B_WR_EN;
	input [WR_BE_WIDTH-1:0] PORT_B_WR_BE;
	input [11:0] PORT_B_ADDR;
	input [71:0] PORT_B_WR_DATA;
	output [71:0] PORT_B_RD_DATA;

	wire [71:0] DIN_A, DIN_B, DOUT_A, DOUT_B;

	generate
		if (OPTION_BYTEWIDTH == 8) begin
			assign DIN_A = PORT_A_WR_DATA;
			assign DIN_B = PORT_B_WR_DATA;
			assign PORT_A_RD_DATA = DOUT_A;
			assign PORT_B_RD_DATA = DOUT_B;
		end else begin
			assign DIN_A = {
				PORT_A_WR_DATA[71],
				PORT_A_WR_DATA[62],
				PORT_A_WR_DATA[53],
				PORT_A_WR_DATA[44],
				PORT_A_WR_DATA[35],
				PORT_A_WR_DATA[26],
				PORT_A_WR_DATA[17],
				PORT_A_WR_DATA[8],
				PORT_A_WR_DATA[70:63],
				PORT_A_WR_DATA[61:54],
				PORT_A_WR_DATA[52:45],
				PORT_A_WR_DATA[43:36],
				PORT_A_WR_DATA[34:27],
				PORT_A_WR_DATA[25:18],
				PORT_A_WR_DATA[16:9],
				PORT_A_WR_DATA[7:0]
			};
			assign DIN_B = {
				PORT_B_WR_DATA[71],
				PORT_B_WR_DATA[62],
				PORT_B_WR_DATA[53],
				PORT_B_WR_DATA[44],
				PORT_B_WR_DATA[35],
				PORT_B_WR_DATA[26],
				PORT_B_WR_DATA[17],
				PORT_B_WR_DATA[8],
				PORT_B_WR_DATA[70:63],
				PORT_B_WR_DATA[61:54],
				PORT_B_WR_DATA[52:45],
				PORT_B_WR_DATA[43:36],
				PORT_B_WR_DATA[34:27],
				PORT_B_WR_DATA[25:18],
				PORT_B_WR_DATA[16:9],
				PORT_B_WR_DATA[7:0]
			};
			assign PORT_A_RD_DATA = {
				DOUT_A[71],
				DOUT_A[63:56],
				DOUT_A[70],
				DOUT_A[55:48],
				DOUT_A[69],
				DOUT_A[47:40],
				DOUT_A[68],
				DOUT_A[39:32],
				DOUT_A[67],
				DOUT_A[31:24],
				DOUT_A[66],
				DOUT_A[23:16],
				DOUT_A[65],
				DOUT_A[15:8],
				DOUT_A[64],
				DOUT_A[7:0]
			};
			assign PORT_B_RD_DATA = {
				DOUT_B[71],
				DOUT_B[63:56],
				DOUT_B[70],
				DOUT_B[55:48],
				DOUT_B[69],
				DOUT_B[47:40],
				DOUT_B[68],
				DOUT_B[39:32],
				DOUT_B[67],
				DOUT_B[31:24],
				DOUT_B[66],
				DOUT_B[23:16],
				DOUT_B[65],
				DOUT_B[15:8],
				DOUT_B[64],
				DOUT_B[7:0]
			};
		end
	endgenerate

	URAM288 #(
		.BWE_MODE_A(OPTION_BYTEWIDTH == 8 ? "PARITY_INDEPENDENT" : "PARITY_INTERLEAVED"),
		.BWE_MODE_B(OPTION_BYTEWIDTH == 8 ? "PARITY_INDEPENDENT" : "PARITY_INTERLEAVED"),
		.EN_AUTO_SLEEP_MODE("FALSE"),
		.IREG_PRE_A("FALSE"),
		.IREG_PRE_B("FALSE"),
		.IS_CLK_INVERTED(!CLK_C_POL),
		.OREG_A("FALSE"),
		.OREG_B("FALSE"),
		.RST_MODE_A(PORT_A_OPTION_RST_MODE),
		.RST_MODE_B(PORT_B_OPTION_RST_MODE),
	) _TECHMAP_REPLACE_ (
		.ADDR_A({11'b0, PORT_A_ADDR}),
		.BWE_A(PORT_A_WR_BE),
		.EN_A(PORT_A_CLK_EN),
		.RDB_WR_A(PORT_A_WR_EN),
		.INJECT_DBITERR_A(1'b0),
		.INJECT_SBITERR_A(1'b0),
		.RST_A(PORT_A_OPTION_RST_MODE == "SYNC" ? PORT_A_RD_SRST : PORT_A_RD_ARST),
		.DIN_A(DIN_A),
		.DOUT_A(DOUT_A),

		.ADDR_B({11'b0, PORT_B_ADDR}),
		.BWE_B(PORT_B_WR_BE),
		.EN_B(PORT_B_CLK_EN),
		.RDB_WR_B(PORT_B_WR_EN),
		.INJECT_DBITERR_B(1'b0),
		.INJECT_SBITERR_B(1'b0),
		.RST_B(PORT_B_OPTION_RST_MODE == "SYNC" ? PORT_B_RD_SRST : PORT_B_RD_ARST),
		.DIN_B(DIN_B),
		.DOUT_B(DOUT_B),

		.CLK(CLK_C),
		.SLEEP(1'b0)
	);
endmodule
