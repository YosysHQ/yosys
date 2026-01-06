module $__DP16KD_ (...);

parameter INIT = 0;
parameter OPTION_RESETMODE = "SYNC";

parameter PORT_A_WIDTH = 18;
parameter PORT_A_WR_BE_WIDTH = 2;
parameter PORT_A_CLK_POL = 1;
parameter PORT_A_OPTION_WRITEMODE = "NORMAL";

input PORT_A_CLK;
input PORT_A_CLK_EN;
input PORT_A_WR_EN;
input PORT_A_RD_SRST;
input PORT_A_RD_ARST;
input [13:0] PORT_A_ADDR;
input [PORT_A_WR_BE_WIDTH-1:0] PORT_A_WR_BE;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

parameter PORT_B_WIDTH = 18;
parameter PORT_B_WR_BE_WIDTH = 2;
parameter PORT_B_CLK_POL = 1;
parameter PORT_B_OPTION_WRITEMODE = "NORMAL";

input PORT_B_CLK;
input PORT_B_CLK_EN;
input PORT_B_WR_EN;
input PORT_B_RD_SRST;
input PORT_B_RD_ARST;
input [13:0] PORT_B_ADDR;
input [PORT_B_WR_BE_WIDTH-1:0] PORT_B_WR_BE;
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

wire [17:0] DOA;
wire [17:0] DOB;
wire [17:0] DIA = PORT_A_WR_DATA;
wire [17:0] DIB = PORT_B_WR_DATA;

assign PORT_A_RD_DATA = DOA;
assign PORT_B_RD_DATA = DOB;

DP16KD #(
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
	.INITVAL_20(init_slice('h20)),
	.INITVAL_21(init_slice('h21)),
	.INITVAL_22(init_slice('h22)),
	.INITVAL_23(init_slice('h23)),
	.INITVAL_24(init_slice('h24)),
	.INITVAL_25(init_slice('h25)),
	.INITVAL_26(init_slice('h26)),
	.INITVAL_27(init_slice('h27)),
	.INITVAL_28(init_slice('h28)),
	.INITVAL_29(init_slice('h29)),
	.INITVAL_2A(init_slice('h2a)),
	.INITVAL_2B(init_slice('h2b)),
	.INITVAL_2C(init_slice('h2c)),
	.INITVAL_2D(init_slice('h2d)),
	.INITVAL_2E(init_slice('h2e)),
	.INITVAL_2F(init_slice('h2f)),
	.INITVAL_30(init_slice('h30)),
	.INITVAL_31(init_slice('h31)),
	.INITVAL_32(init_slice('h32)),
	.INITVAL_33(init_slice('h33)),
	.INITVAL_34(init_slice('h34)),
	.INITVAL_35(init_slice('h35)),
	.INITVAL_36(init_slice('h36)),
	.INITVAL_37(init_slice('h37)),
	.INITVAL_38(init_slice('h38)),
	.INITVAL_39(init_slice('h39)),
	.INITVAL_3A(init_slice('h3a)),
	.INITVAL_3B(init_slice('h3b)),
	.INITVAL_3C(init_slice('h3c)),
	.INITVAL_3D(init_slice('h3d)),
	.INITVAL_3E(init_slice('h3e)),
	.INITVAL_3F(init_slice('h3f)),
	.DATA_WIDTH_A(PORT_A_WIDTH),
	.DATA_WIDTH_B(PORT_B_WIDTH),
	.REGMODE_A("NOREG"),
	.REGMODE_B("NOREG"),
	.RESETMODE(OPTION_RESETMODE),
	.ASYNC_RESET_RELEASE(OPTION_RESETMODE),
	.CSDECODE_A("0b000"),
	.CSDECODE_B("0b000"),
	.CLKAMUX(PORT_A_CLK_POL ? "CLKA" : "INV"),
	.CLKBMUX(PORT_B_CLK_POL ? "CLKB" : "INV"),
	.WRITEMODE_A(PORT_A_OPTION_WRITEMODE),
	.WRITEMODE_B(PORT_B_OPTION_WRITEMODE),
	.GSR("AUTO")
) _TECHMAP_REPLACE_ (
	.CLKA(PORT_A_CLK),
	.WEA(PORT_A_WIDTH == 18 ? PORT_A_WR_EN : (PORT_A_WR_EN | PORT_A_WR_BE[0])),
	.CEA(PORT_A_CLK_EN),
	.OCEA(1'b1),
	.RSTA(OPTION_RESETMODE == "SYNC" ? PORT_A_RD_SRST : PORT_A_RD_ARST),
	.CSA0(1'b0),
	.CSA1(1'b0),
	.CSA2(1'b0),
	.ADA0(PORT_A_WIDTH == 18 ? PORT_A_WR_BE[0] : PORT_A_ADDR[0]),
	.ADA1(PORT_A_WIDTH == 18 ? PORT_A_WR_BE[1] : PORT_A_ADDR[1]),
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
	.ADA13(PORT_A_ADDR[13]),
	.DIA0(DIA[0]),
	.DIA1(DIA[1]),
	.DIA2(DIA[2]),
	.DIA3(DIA[3]),
	.DIA4(DIA[4]),
	.DIA5(DIA[5]),
	.DIA6(DIA[6]),
	.DIA7(DIA[7]),
	.DIA8(DIA[8]),
	.DIA9(DIA[9]),
	.DIA10(DIA[10]),
	.DIA11(DIA[11]),
	.DIA12(DIA[12]),
	.DIA13(DIA[13]),
	.DIA14(DIA[14]),
	.DIA15(DIA[15]),
	.DIA16(DIA[16]),
	.DIA17(DIA[17]),
	.DOA0(DOA[0]),
	.DOA1(DOA[1]),
	.DOA2(DOA[2]),
	.DOA3(DOA[3]),
	.DOA4(DOA[4]),
	.DOA5(DOA[5]),
	.DOA6(DOA[6]),
	.DOA7(DOA[7]),
	.DOA8(DOA[8]),
	.DOA9(DOA[9]),
	.DOA10(DOA[10]),
	.DOA11(DOA[11]),
	.DOA12(DOA[12]),
	.DOA13(DOA[13]),
	.DOA14(DOA[14]),
	.DOA15(DOA[15]),
	.DOA16(DOA[16]),
	.DOA17(DOA[17]),

	.CLKB(PORT_B_CLK),
	.WEB(PORT_B_WIDTH == 18 ? PORT_B_WR_EN : (PORT_B_WR_EN | PORT_B_WR_BE[0])),
	.CEB(PORT_B_CLK_EN),
	.OCEB(1'b1),
	.RSTB(OPTION_RESETMODE == "SYNC" ? PORT_B_RD_SRST : PORT_B_RD_ARST),
	.CSB0(1'b0),
	.CSB1(1'b0),
	.CSB2(1'b0),
	.ADB0(PORT_B_WIDTH == 18 ? PORT_B_WR_BE[0] : PORT_B_ADDR[0]),
	.ADB1(PORT_B_WIDTH == 18 ? PORT_B_WR_BE[1] : PORT_B_ADDR[1]),
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
	.ADB13(PORT_B_ADDR[13]),
	.DIB0(DIB[0]),
	.DIB1(DIB[1]),
	.DIB2(DIB[2]),
	.DIB3(DIB[3]),
	.DIB4(DIB[4]),
	.DIB5(DIB[5]),
	.DIB6(DIB[6]),
	.DIB7(DIB[7]),
	.DIB8(DIB[8]),
	.DIB9(DIB[9]),
	.DIB10(DIB[10]),
	.DIB11(DIB[11]),
	.DIB12(DIB[12]),
	.DIB13(DIB[13]),
	.DIB14(DIB[14]),
	.DIB15(DIB[15]),
	.DIB16(DIB[16]),
	.DIB17(DIB[17]),
	.DOB0(DOB[0]),
	.DOB1(DOB[1]),
	.DOB2(DOB[2]),
	.DOB3(DOB[3]),
	.DOB4(DOB[4]),
	.DOB5(DOB[5]),
	.DOB6(DOB[6]),
	.DOB7(DOB[7]),
	.DOB8(DOB[8]),
	.DOB9(DOB[9]),
	.DOB10(DOB[10]),
	.DOB11(DOB[11]),
	.DOB12(DOB[12]),
	.DOB13(DOB[13]),
	.DOB14(DOB[14]),
	.DOB15(DOB[15]),
	.DOB16(DOB[16]),
	.DOB17(DOB[17]),
);

endmodule


module $__PDPW16KD_ (...);

parameter INIT = 0;
parameter OPTION_RESETMODE = "SYNC";

parameter PORT_R_WIDTH = 36;
parameter PORT_R_CLK_POL = 1;

input PORT_R_CLK;
input PORT_R_CLK_EN;
input PORT_R_RD_SRST;
input PORT_R_RD_ARST;
input [13:0] PORT_R_ADDR;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;

parameter PORT_W_WIDTH = 36;
parameter PORT_W_WR_EN_WIDTH = 4;
parameter PORT_W_CLK_POL = 1;

input PORT_W_CLK;
input PORT_W_CLK_EN;
input [13:0] PORT_W_ADDR;
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

wire [35:0] DI = PORT_W_WR_DATA;
wire [35:0] DO;

assign PORT_R_RD_DATA = PORT_R_WIDTH == 36 ? DO : DO[35:18];

DP16KD #(
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
	.INITVAL_20(init_slice('h20)),
	.INITVAL_21(init_slice('h21)),
	.INITVAL_22(init_slice('h22)),
	.INITVAL_23(init_slice('h23)),
	.INITVAL_24(init_slice('h24)),
	.INITVAL_25(init_slice('h25)),
	.INITVAL_26(init_slice('h26)),
	.INITVAL_27(init_slice('h27)),
	.INITVAL_28(init_slice('h28)),
	.INITVAL_29(init_slice('h29)),
	.INITVAL_2A(init_slice('h2a)),
	.INITVAL_2B(init_slice('h2b)),
	.INITVAL_2C(init_slice('h2c)),
	.INITVAL_2D(init_slice('h2d)),
	.INITVAL_2E(init_slice('h2e)),
	.INITVAL_2F(init_slice('h2f)),
	.INITVAL_30(init_slice('h30)),
	.INITVAL_31(init_slice('h31)),
	.INITVAL_32(init_slice('h32)),
	.INITVAL_33(init_slice('h33)),
	.INITVAL_34(init_slice('h34)),
	.INITVAL_35(init_slice('h35)),
	.INITVAL_36(init_slice('h36)),
	.INITVAL_37(init_slice('h37)),
	.INITVAL_38(init_slice('h38)),
	.INITVAL_39(init_slice('h39)),
	.INITVAL_3A(init_slice('h3a)),
	.INITVAL_3B(init_slice('h3b)),
	.INITVAL_3C(init_slice('h3c)),
	.INITVAL_3D(init_slice('h3d)),
	.INITVAL_3E(init_slice('h3e)),
	.INITVAL_3F(init_slice('h3f)),
	.DATA_WIDTH_A(PORT_W_WIDTH),
	.DATA_WIDTH_B(PORT_R_WIDTH),
	.REGMODE_A("NOREG"),
	.REGMODE_B("NOREG"),
	.RESETMODE(OPTION_RESETMODE),
	.ASYNC_RESET_RELEASE(OPTION_RESETMODE),
	.CSDECODE_A("0b000"),
	.CSDECODE_B("0b000"),
	.CLKAMUX(PORT_W_CLK_POL ? "CLKA" : "INV"),
	.CLKBMUX(PORT_R_CLK_POL ? "CLKB" : "INV"),
	.GSR("AUTO")
) _TECHMAP_REPLACE_ (
	.CLKA(PORT_W_CLK),
	.WEA(PORT_W_WIDTH >= 18 ? 1'b1 : PORT_W_WR_EN[0]),
	.CEA(PORT_W_CLK_EN),
	.OCEA(1'b0),
	.RSTA(1'b0),
	.CSA0(1'b0),
	.CSA1(1'b0),
	.CSA2(1'b0),
	.ADA0(PORT_W_WIDTH >= 18 ? PORT_W_WR_EN[0] : PORT_W_ADDR[0]),
	.ADA1(PORT_W_WIDTH >= 18 ? PORT_W_WR_EN[1] : PORT_W_ADDR[1]),
	.ADA2(PORT_W_WIDTH >= 36 ? PORT_W_WR_EN[2] : PORT_W_ADDR[2]),
	.ADA3(PORT_W_WIDTH >= 36 ? PORT_W_WR_EN[3] : PORT_W_ADDR[3]),
	.ADA4(PORT_W_ADDR[4]),
	.ADA5(PORT_W_ADDR[5]),
	.ADA6(PORT_W_ADDR[6]),
	.ADA7(PORT_W_ADDR[7]),
	.ADA8(PORT_W_ADDR[8]),
	.ADA9(PORT_W_ADDR[9]),
	.ADA10(PORT_W_ADDR[10]),
	.ADA11(PORT_W_ADDR[11]),
	.ADA12(PORT_W_ADDR[12]),
	.ADA13(PORT_W_ADDR[13]),
	.DIA0(DI[0]),
	.DIA1(DI[1]),
	.DIA2(DI[2]),
	.DIA3(DI[3]),
	.DIA4(DI[4]),
	.DIA5(DI[5]),
	.DIA6(DI[6]),
	.DIA7(DI[7]),
	.DIA8(DI[8]),
	.DIA9(DI[9]),
	.DIA10(DI[10]),
	.DIA11(DI[11]),
	.DIA12(DI[12]),
	.DIA13(DI[13]),
	.DIA14(DI[14]),
	.DIA15(DI[15]),
	.DIA16(DI[16]),
	.DIA17(DI[17]),
	.DIB0(DI[18]),
	.DIB1(DI[19]),
	.DIB2(DI[20]),
	.DIB3(DI[21]),
	.DIB4(DI[22]),
	.DIB5(DI[23]),
	.DIB6(DI[24]),
	.DIB7(DI[25]),
	.DIB8(DI[26]),
	.DIB9(DI[27]),
	.DIB10(DI[28]),
	.DIB11(DI[29]),
	.DIB12(DI[30]),
	.DIB13(DI[31]),
	.DIB14(DI[32]),
	.DIB15(DI[33]),
	.DIB16(DI[34]),
	.DIB17(DI[35]),

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
	.ADB13(PORT_R_ADDR[13]),
	.DOA0(DO[0]),
	.DOA1(DO[1]),
	.DOA2(DO[2]),
	.DOA3(DO[3]),
	.DOA4(DO[4]),
	.DOA5(DO[5]),
	.DOA6(DO[6]),
	.DOA7(DO[7]),
	.DOA8(DO[8]),
	.DOA9(DO[9]),
	.DOA10(DO[10]),
	.DOA11(DO[11]),
	.DOA12(DO[12]),
	.DOA13(DO[13]),
	.DOA14(DO[14]),
	.DOA15(DO[15]),
	.DOA16(DO[16]),
	.DOA17(DO[17]),
	.DOB0(DO[18]),
	.DOB1(DO[19]),
	.DOB2(DO[20]),
	.DOB3(DO[21]),
	.DOB4(DO[22]),
	.DOB5(DO[23]),
	.DOB6(DO[24]),
	.DOB7(DO[25]),
	.DOB8(DO[26]),
	.DOB9(DO[27]),
	.DOB10(DO[28]),
	.DOB11(DO[29]),
	.DOB12(DO[30]),
	.DOB13(DO[31]),
	.DOB14(DO[32]),
	.DOB15(DO[33]),
	.DOB16(DO[34]),
	.DOB17(DO[35]),
);

endmodule
