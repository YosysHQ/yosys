module $__DP8KC_ (...);

parameter INIT = 0;
parameter OPTION_RESETMODE = "SYNC";

parameter PORT_A_WIDTH = 18;
parameter PORT_A_OPTION_WRITEMODE = "NORMAL";

input PORT_A_CLK;
input PORT_A_CLK_EN;
input PORT_A_WR_EN;
input PORT_A_RD_SRST;
input PORT_A_RD_ARST;
input [12:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

parameter PORT_B_WIDTH = 18;
parameter PORT_B_OPTION_WRITEMODE = "NORMAL";

input PORT_B_CLK;
input PORT_B_CLK_EN;
input PORT_B_WR_EN;
input PORT_B_RD_SRST;
input PORT_B_RD_ARST;
input [12:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;

function [319:0] init_slice;
	input integer idx;
	integer i, j;
	init_slice = 0;
	for (i = 0; i < 16; i = i + 1) begin
		init_slice[i*20+:18] = INIT[(idx * 16 + i) * 18+:18];
	end
endfunction

wire [8:0] DOA;
wire [8:0] DOB;
wire [8:0] DIA;
wire [8:0] DIB;

case(PORT_A_WIDTH)
	1: assign DIA = {7'bx, PORT_A_WR_DATA[0], 1'bx};
	2: assign DIA = {3'bx, PORT_A_WR_DATA[1], 2'bx, PORT_A_WR_DATA[0], 2'bx};
	default: assign DIA = PORT_A_WR_DATA;
endcase

case(PORT_B_WIDTH)
	1: assign DIB = {7'bx, PORT_B_WR_DATA[0], 1'bx};
	2: assign DIB = {3'bx, PORT_B_WR_DATA[1], 2'bx, PORT_B_WR_DATA[0], 2'bx};
	default: assign DIB = PORT_B_WR_DATA;
endcase

assign PORT_A_RD_DATA = DOA;
assign PORT_B_RD_DATA = DOB;

DP8KC #(
	.INITVAL_00(init_slice('h00)),
	.INITVAL_01(init_slice('h01)),
	.INITVAL_02(init_slice('h02)),
	.INITVAL_03(init_slice('h03)),
	.INITVAL_04(init_slice('h04)),
	.INITVAL_05(init_slice('h05)),
	.INITVAL_06(init_slice('h06)),
	.INITVAL_07(init_slice('h07)),
	.INITVAL_08(init_slice('h08)),
	.INITVAL_09(init_slice('h09)),
	.INITVAL_0A(init_slice('h0a)),
	.INITVAL_0B(init_slice('h0b)),
	.INITVAL_0C(init_slice('h0c)),
	.INITVAL_0D(init_slice('h0d)),
	.INITVAL_0E(init_slice('h0e)),
	.INITVAL_0F(init_slice('h0f)),
	.INITVAL_10(init_slice('h10)),
	.INITVAL_11(init_slice('h11)),
	.INITVAL_12(init_slice('h12)),
	.INITVAL_13(init_slice('h13)),
	.INITVAL_14(init_slice('h14)),
	.INITVAL_15(init_slice('h15)),
	.INITVAL_16(init_slice('h16)),
	.INITVAL_17(init_slice('h17)),
	.INITVAL_18(init_slice('h18)),
	.INITVAL_19(init_slice('h19)),
	.INITVAL_1A(init_slice('h1a)),
	.INITVAL_1B(init_slice('h1b)),
	.INITVAL_1C(init_slice('h1c)),
	.INITVAL_1D(init_slice('h1d)),
	.INITVAL_1E(init_slice('h1e)),
	.INITVAL_1F(init_slice('h1f)),
	.DATA_WIDTH_A(PORT_A_WIDTH),
	.DATA_WIDTH_B(PORT_B_WIDTH),
	.REGMODE_A("NOREG"),
	.REGMODE_B("NOREG"),
	.RESETMODE(OPTION_RESETMODE),
	.ASYNC_RESET_RELEASE(OPTION_RESETMODE),
	.CSDECODE_A("0b000"),
	.CSDECODE_B("0b000"),
	.WRITEMODE_A(PORT_A_OPTION_WRITEMODE),
	.WRITEMODE_B(PORT_B_OPTION_WRITEMODE),
	.GSR("AUTO")
) _TECHMAP_REPLACE_ (
	.CLKA(PORT_A_CLK),
	.WEA(PORT_A_WR_EN),
	.CEA(PORT_A_CLK_EN),
	.OCEA(1'b1),
	.RSTA(OPTION_RESETMODE == "SYNC" ? PORT_A_RD_SRST : PORT_A_RD_ARST),
	.CSA0(1'b0),
	.CSA1(1'b0),
	.CSA2(1'b0),
	.ADA0(PORT_A_WIDTH == 9 ? 1'b1 : PORT_A_ADDR[0]),
	.ADA1(PORT_A_ADDR[1]),
	.ADA2(PORT_A_ADDR[2]),
	.ADA3(PORT_A_ADDR[3]),
	.ADA4(PORT_A_ADDR[4]),
	.ADA5(PORT_A_ADDR[5]),
	.ADA6(PORT_A_ADDR[6]),
	.ADA7(PORT_A_ADDR[7]),
	.ADA8(PORT_A_ADDR[8]),
	.ADA9(PORT_A_ADDR[9]),
	.ADA10(PORT_A_ADDR[10]),
	.ADA11(PORT_A_ADDR[11]),
	.ADA12(PORT_A_ADDR[12]),
	.DIA0(DIA[0]),
	.DIA1(DIA[1]),
	.DIA2(DIA[2]),
	.DIA3(DIA[3]),
	.DIA4(DIA[4]),
	.DIA5(DIA[5]),
	.DIA6(DIA[6]),
	.DIA7(DIA[7]),
	.DIA8(DIA[8]),
	.DOA0(DOA[0]),
	.DOA1(DOA[1]),
	.DOA2(DOA[2]),
	.DOA3(DOA[3]),
	.DOA4(DOA[4]),
	.DOA5(DOA[5]),
	.DOA6(DOA[6]),
	.DOA7(DOA[7]),
	.DOA8(DOA[8]),

	.CLKB(PORT_B_CLK),
	.WEB(PORT_B_WR_EN),
	.CEB(PORT_B_CLK_EN),
	.OCEB(1'b1),
	.RSTB(OPTION_RESETMODE == "SYNC" ? PORT_B_RD_SRST : PORT_B_RD_ARST),
	.CSB0(1'b0),
	.CSB1(1'b0),
	.CSB2(1'b0),
	.ADB0(PORT_B_WIDTH == 9 ? 1'b1 : PORT_B_ADDR[0]),
	.ADB1(PORT_B_ADDR[1]),
	.ADB2(PORT_B_ADDR[2]),
	.ADB3(PORT_B_ADDR[3]),
	.ADB4(PORT_B_ADDR[4]),
	.ADB5(PORT_B_ADDR[5]),
	.ADB6(PORT_B_ADDR[6]),
	.ADB7(PORT_B_ADDR[7]),
	.ADB8(PORT_B_ADDR[8]),
	.ADB9(PORT_B_ADDR[9]),
	.ADB10(PORT_B_ADDR[10]),
	.ADB11(PORT_B_ADDR[11]),
	.ADB12(PORT_B_ADDR[12]),
	.DIB0(DIB[0]),
	.DIB1(DIB[1]),
	.DIB2(DIB[2]),
	.DIB3(DIB[3]),
	.DIB4(DIB[4]),
	.DIB5(DIB[5]),
	.DIB6(DIB[6]),
	.DIB7(DIB[7]),
	.DIB8(DIB[8]),
	.DOB0(DOB[0]),
	.DOB1(DOB[1]),
	.DOB2(DOB[2]),
	.DOB3(DOB[3]),
	.DOB4(DOB[4]),
	.DOB5(DOB[5]),
	.DOB6(DOB[6]),
	.DOB7(DOB[7]),
	.DOB8(DOB[8]),
);

endmodule


module $__PDPW8KC_ (...);

parameter INIT = 0;
parameter OPTION_RESETMODE = "SYNC";

parameter PORT_R_WIDTH = 18;

input PORT_R_CLK;
input PORT_R_CLK_EN;
input PORT_R_RD_SRST;
input PORT_R_RD_ARST;
input [12:0] PORT_R_ADDR;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;

parameter PORT_W_WIDTH = 18;
parameter PORT_W_WR_EN_WIDTH = 2;

input PORT_W_CLK;
input PORT_W_CLK_EN;
input [12:0] PORT_W_ADDR;
input [PORT_W_WR_EN_WIDTH-1:0] PORT_W_WR_EN;
input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;

function [319:0] init_slice;
	input integer idx;
	integer i, j;
	init_slice = 0;
	for (i = 0; i < 16; i = i + 1) begin
		init_slice[i*20+:18] = INIT[(idx * 16 + i) * 18+:18];
	end
endfunction

wire [17:0] DI = PORT_W_WR_DATA;
wire [17:0] DO;

assign PORT_R_RD_DATA = PORT_R_WIDTH == 18 ? DO : DO[17:9];

DP8KC #(
	.INITVAL_00(init_slice('h00)),
	.INITVAL_01(init_slice('h01)),
	.INITVAL_02(init_slice('h02)),
	.INITVAL_03(init_slice('h03)),
	.INITVAL_04(init_slice('h04)),
	.INITVAL_05(init_slice('h05)),
	.INITVAL_06(init_slice('h06)),
	.INITVAL_07(init_slice('h07)),
	.INITVAL_08(init_slice('h08)),
	.INITVAL_09(init_slice('h09)),
	.INITVAL_0A(init_slice('h0a)),
	.INITVAL_0B(init_slice('h0b)),
	.INITVAL_0C(init_slice('h0c)),
	.INITVAL_0D(init_slice('h0d)),
	.INITVAL_0E(init_slice('h0e)),
	.INITVAL_0F(init_slice('h0f)),
	.INITVAL_10(init_slice('h10)),
	.INITVAL_11(init_slice('h11)),
	.INITVAL_12(init_slice('h12)),
	.INITVAL_13(init_slice('h13)),
	.INITVAL_14(init_slice('h14)),
	.INITVAL_15(init_slice('h15)),
	.INITVAL_16(init_slice('h16)),
	.INITVAL_17(init_slice('h17)),
	.INITVAL_18(init_slice('h18)),
	.INITVAL_19(init_slice('h19)),
	.INITVAL_1A(init_slice('h1a)),
	.INITVAL_1B(init_slice('h1b)),
	.INITVAL_1C(init_slice('h1c)),
	.INITVAL_1D(init_slice('h1d)),
	.INITVAL_1E(init_slice('h1e)),
	.INITVAL_1F(init_slice('h1f)),
	.DATA_WIDTH_A(PORT_W_WIDTH),
	.DATA_WIDTH_B(PORT_R_WIDTH),
	.REGMODE_A("NOREG"),
	.REGMODE_B("NOREG"),
	.RESETMODE(OPTION_RESETMODE),
	.ASYNC_RESET_RELEASE(OPTION_RESETMODE),
	.CSDECODE_A("0b000"),
	.CSDECODE_B("0b000"),
	.GSR("AUTO")
) _TECHMAP_REPLACE_ (
	.CLKA(PORT_W_CLK),
	.WEA(PORT_W_WIDTH >= 9 ? 1'b1 : PORT_W_WR_EN[0]),
	.CEA(PORT_W_CLK_EN),
	.OCEA(1'b0),
	.RSTA(1'b0),
	.CSA0(1'b0),
	.CSA1(1'b0),
	.CSA2(1'b0),
	.ADA0(PORT_W_WIDTH >= 9 ? PORT_W_WR_EN[0] : PORT_W_ADDR[0]),
	.ADA1(PORT_W_WIDTH >= 18 ? PORT_W_WR_EN[1] : PORT_W_ADDR[1]),
	.ADA2(PORT_W_ADDR[2]),
	.ADA3(PORT_W_ADDR[3]),
	.ADA4(PORT_W_ADDR[4]),
	.ADA5(PORT_W_ADDR[5]),
	.ADA6(PORT_W_ADDR[6]),
	.ADA7(PORT_W_ADDR[7]),
	.ADA8(PORT_W_ADDR[8]),
	.ADA9(PORT_W_ADDR[9]),
	.ADA10(PORT_W_ADDR[10]),
	.ADA11(PORT_W_ADDR[11]),
	.ADA12(PORT_W_ADDR[12]),
	.DIA0(DI[0]),
	.DIA1(DI[1]),
	.DIA2(DI[2]),
	.DIA3(DI[3]),
	.DIA4(DI[4]),
	.DIA5(DI[5]),
	.DIA6(DI[6]),
	.DIA7(DI[7]),
	.DIA8(DI[8]),
	.DIB0(DI[9]),
	.DIB1(DI[10]),
	.DIB2(DI[11]),
	.DIB3(DI[12]),
	.DIB4(DI[13]),
	.DIB5(DI[14]),
	.DIB6(DI[15]),
	.DIB7(DI[16]),
	.DIB8(DI[17]),

	.CLKB(PORT_R_CLK),
	.WEB(1'b0),
	.CEB(PORT_R_CLK_EN),
	.OCEB(1'b1),
	.RSTB(OPTION_RESETMODE == "SYNC" ? PORT_R_RD_SRST : PORT_R_RD_ARST),
	.CSB0(1'b0),
	.CSB1(1'b0),
	.CSB2(1'b0),
	.ADB0(PORT_R_ADDR[0]),
	.ADB1(PORT_R_ADDR[1]),
	.ADB2(PORT_R_ADDR[2]),
	.ADB3(PORT_R_ADDR[3]),
	.ADB4(PORT_R_ADDR[4]),
	.ADB5(PORT_R_ADDR[5]),
	.ADB6(PORT_R_ADDR[6]),
	.ADB7(PORT_R_ADDR[7]),
	.ADB8(PORT_R_ADDR[8]),
	.ADB9(PORT_R_ADDR[9]),
	.ADB10(PORT_R_ADDR[10]),
	.ADB11(PORT_R_ADDR[11]),
	.ADB12(PORT_R_ADDR[12]),
	.DOA0(DO[0]),
	.DOA1(DO[1]),
	.DOA2(DO[2]),
	.DOA3(DO[3]),
	.DOA4(DO[4]),
	.DOA5(DO[5]),
	.DOA6(DO[6]),
	.DOA7(DO[7]),
	.DOA8(DO[8]),
	.DOB0(DO[9]),
	.DOB1(DO[10]),
	.DOB2(DO[11]),
	.DOB3(DO[12]),
	.DOB4(DO[13]),
	.DOB5(DO[14]),
	.DOB6(DO[15]),
	.DOB7(DO[16]),
	.DOB8(DO[17]),
);

endmodule
