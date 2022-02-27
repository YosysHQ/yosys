module $__ANLOGIC_BRAM_TDP_ (...);

parameter INIT = 0;
parameter OPTION_RESETMODE = "SYNC";

parameter PORT_A_WIDTH = 9;
parameter PORT_A_CLK_POL = 1;
parameter PORT_A_OPTION_WRITEMODE = "NORMAL";

input PORT_A_CLK;
input PORT_A_CLK_EN;
input PORT_A_WR_EN;
input PORT_A_RD_SRST;
input PORT_A_RD_ARST;
input [12:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

parameter PORT_B_WIDTH = 9;
parameter PORT_B_CLK_POL = 1;
parameter PORT_B_OPTION_WRITEMODE = "NORMAL";

input PORT_B_CLK;
input PORT_B_CLK_EN;
input PORT_B_WR_EN;
input PORT_B_RD_SRST;
input PORT_B_RD_ARST;
input [12:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;

function [255:0] init_slice;
	input integer idx;
	integer i;
	for (i = 0; i < 32; i = i + 1) begin
		init_slice[i*8+:8] = INIT[(idx * 32 + i) * 9 +: 8];
	end
endfunction

function [255:0] initp_slice;
	input integer idx;
	integer i;
	for (i = 0; i < 256; i = i + 1) begin
		initp_slice[i] = INIT[(idx * 256 + i) * 9 + 8];
	end
endfunction

wire [8:0] DOA;
wire [8:0] DOB;
// the replication is important — the BRAM behaves in... unexpected ways for
// width 1 and 2
wire [8:0] DIA = {9{PORT_A_WR_DATA}};
wire [8:0] DIB = {9{PORT_B_WR_DATA}};

assign PORT_A_RD_DATA = DOA;
assign PORT_B_RD_DATA = DOB;

EG_PHY_BRAM #(
	.INIT_00(init_slice('h00)),
	.INIT_01(init_slice('h01)),
	.INIT_02(init_slice('h02)),
	.INIT_03(init_slice('h03)),
	.INIT_04(init_slice('h04)),
	.INIT_05(init_slice('h05)),
	.INIT_06(init_slice('h06)),
	.INIT_07(init_slice('h07)),
	.INIT_08(init_slice('h08)),
	.INIT_09(init_slice('h09)),
	.INIT_0A(init_slice('h0a)),
	.INIT_0B(init_slice('h0b)),
	.INIT_0C(init_slice('h0c)),
	.INIT_0D(init_slice('h0d)),
	.INIT_0E(init_slice('h0e)),
	.INIT_0F(init_slice('h0f)),
	.INIT_10(init_slice('h10)),
	.INIT_11(init_slice('h11)),
	.INIT_12(init_slice('h12)),
	.INIT_13(init_slice('h13)),
	.INIT_14(init_slice('h14)),
	.INIT_15(init_slice('h15)),
	.INIT_16(init_slice('h16)),
	.INIT_17(init_slice('h17)),
	.INIT_18(init_slice('h18)),
	.INIT_19(init_slice('h19)),
	.INIT_1A(init_slice('h1a)),
	.INIT_1B(init_slice('h1b)),
	.INIT_1C(init_slice('h1c)),
	.INIT_1D(init_slice('h1d)),
	.INIT_1E(init_slice('h1e)),
	.INIT_1F(init_slice('h1f)),
	.INITP_00(initp_slice('h00)),
	.INITP_01(initp_slice('h01)),
	.INITP_02(initp_slice('h02)),
	.INITP_03(initp_slice('h03)),
	.MODE("DP8K"),
	.DATA_WIDTH_A($sformatf("%d", PORT_A_WIDTH)),
	.DATA_WIDTH_B($sformatf("%d", PORT_B_WIDTH)),
	.REGMODE_A("NOREG"),
	.REGMODE_B("NOREG"),
	.RESETMODE(OPTION_RESETMODE),
	.ASYNC_RESET_RELEASE(OPTION_RESETMODE),
	.CLKAMUX(PORT_A_CLK_POL ? "SIG" : "INV"),
	.CLKBMUX(PORT_B_CLK_POL ? "SIG" : "INV"),
	.WRITEMODE_A(PORT_A_OPTION_WRITEMODE),
	.WRITEMODE_B(PORT_B_OPTION_WRITEMODE),
) _TECHMAP_REPLACE_ (
	.clka(PORT_A_CLK),
	.wea(PORT_A_WR_EN),
	.cea(PORT_A_CLK_EN),
	.ocea(1'b1),
	.rsta(OPTION_RESETMODE == "SYNC" ? PORT_A_RD_SRST : PORT_A_RD_ARST),
	.csa(3'b111),
	.addra(PORT_A_WIDTH == 9 ? {PORT_A_ADDR[12:1], 1'b1} : PORT_A_ADDR),
	.dia(DIA),
	.doa(DOA),

	.clkb(PORT_B_CLK),
	.web(PORT_B_WR_EN),
	.ceb(PORT_B_CLK_EN),
	.oceb(1'b1),
	.rstb(OPTION_RESETMODE == "SYNC" ? PORT_B_RD_SRST : PORT_B_RD_ARST),
	.csb(3'b111),
	.addrb(PORT_B_WIDTH == 9 ? {PORT_B_ADDR[12:1], 1'b1} : PORT_B_ADDR),
	.dib(DIB),
	.dob(DOB),
);

endmodule


module $__ANLOGIC_BRAM_SDP_ (...);

parameter INIT = 0;
parameter OPTION_RESETMODE = "SYNC";

parameter PORT_R_WIDTH = 18;
parameter PORT_R_CLK_POL = 1;

input PORT_R_CLK;
input PORT_R_CLK_EN;
input PORT_R_RD_SRST;
input PORT_R_RD_ARST;
input [12:0] PORT_R_ADDR;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;

parameter PORT_W_WIDTH = 18;
parameter PORT_W_WR_EN_WIDTH = 2;
parameter PORT_W_CLK_POL = 1;

input PORT_W_CLK;
input PORT_W_CLK_EN;
input [12:0] PORT_W_ADDR;
input [PORT_W_WR_EN_WIDTH-1:0] PORT_W_WR_EN;
input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;

function [255:0] init_slice;
	input integer idx;
	integer i;
	for (i = 0; i < 32; i = i + 1) begin
		init_slice[i*8+:8] = INIT[(idx * 32 + i) * 9 +: 8];
	end
endfunction

function [255:0] initp_slice;
	input integer idx;
	integer i;
	for (i = 0; i < 256; i = i + 1) begin
		initp_slice[i] = INIT[(idx * 256 + i) * 9 + 8];
	end
endfunction

wire [17:0] DI = {18{PORT_W_WR_DATA}};
wire [17:0] DO;

assign PORT_R_RD_DATA = PORT_R_WIDTH == 18 ? DO : DO[17:9];

EG_PHY_BRAM #(
	.INIT_00(init_slice('h00)),
	.INIT_01(init_slice('h01)),
	.INIT_02(init_slice('h02)),
	.INIT_03(init_slice('h03)),
	.INIT_04(init_slice('h04)),
	.INIT_05(init_slice('h05)),
	.INIT_06(init_slice('h06)),
	.INIT_07(init_slice('h07)),
	.INIT_08(init_slice('h08)),
	.INIT_09(init_slice('h09)),
	.INIT_0A(init_slice('h0a)),
	.INIT_0B(init_slice('h0b)),
	.INIT_0C(init_slice('h0c)),
	.INIT_0D(init_slice('h0d)),
	.INIT_0E(init_slice('h0e)),
	.INIT_0F(init_slice('h0f)),
	.INIT_10(init_slice('h10)),
	.INIT_11(init_slice('h11)),
	.INIT_12(init_slice('h12)),
	.INIT_13(init_slice('h13)),
	.INIT_14(init_slice('h14)),
	.INIT_15(init_slice('h15)),
	.INIT_16(init_slice('h16)),
	.INIT_17(init_slice('h17)),
	.INIT_18(init_slice('h18)),
	.INIT_19(init_slice('h19)),
	.INIT_1A(init_slice('h1a)),
	.INIT_1B(init_slice('h1b)),
	.INIT_1C(init_slice('h1c)),
	.INIT_1D(init_slice('h1d)),
	.INIT_1E(init_slice('h1e)),
	.INIT_1F(init_slice('h1f)),
	.INITP_00(initp_slice('h00)),
	.INITP_01(initp_slice('h01)),
	.INITP_02(initp_slice('h02)),
	.INITP_03(initp_slice('h03)),
	.MODE("PDPW8K"),
	.DATA_WIDTH_A($sformatf("%d", PORT_W_WIDTH)),
	.DATA_WIDTH_B($sformatf("%d", PORT_R_WIDTH)),
	.REGMODE_A("NOREG"),
	.REGMODE_B("NOREG"),
	.RESETMODE(OPTION_RESETMODE),
	.ASYNC_RESET_RELEASE(OPTION_RESETMODE),
	.CLKAMUX(PORT_W_CLK_POL ? "SIG" : "INV"),
	.CLKBMUX(PORT_R_CLK_POL ? "SIG" : "INV"),
) _TECHMAP_REPLACE_ (
	.clka(PORT_W_CLK),
	.wea(PORT_W_WIDTH >= 9 ? 1'b1 : PORT_W_WR_EN[0]),
	.cea(PORT_W_CLK_EN),
	.ocea(1'b1),
	.rsta(1'b0),
	.csa(3'b111),
	.addra(PORT_W_WIDTH == 18 ? {PORT_W_ADDR[12:2], PORT_W_WR_EN[1:0]} : (PORT_W_WIDTH == 9 ? {PORT_W_ADDR[12:1], PORT_W_WR_EN[0]} : PORT_W_ADDR)),
	.dia(DI[8:0]),
	.doa(DO[8:0]),

	.clkb(PORT_R_CLK),
	.web(1'b0),
	.ceb(PORT_R_CLK_EN),
	.oceb(1'b1),
	.rstb(OPTION_RESETMODE == "SYNC" ? PORT_R_RD_SRST : PORT_R_RD_ARST),
	.csb(3'b111),
	.addrb(PORT_R_ADDR),
	.dib(DI[17:9]),
	.dob(DO[17:9]),
);

endmodule


module $__ANLOGIC_BRAM32K_ (...);

parameter INIT = 0;

parameter PORT_A_WIDTH = 16;
parameter PORT_A_WR_EN_WIDTH = 2;
parameter PORT_A_CLK_POL = 1;
parameter PORT_A_OPTION_WRITEMODE = "NORMAL";

input PORT_A_CLK;
input PORT_A_CLK_EN;
input [PORT_A_WR_EN_WIDTH-1:0] PORT_A_WR_EN;
input [11:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

parameter PORT_B_WIDTH = 16;
parameter PORT_B_WR_EN_WIDTH = 2;
parameter PORT_B_CLK_POL = 1;
parameter PORT_B_OPTION_WRITEMODE = "NORMAL";

input PORT_B_CLK;
input PORT_B_CLK_EN;
input [PORT_B_WR_EN_WIDTH-1:0] PORT_B_WR_EN;
input [11:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;

function [255:0] init_slice;
	input integer idx;
	init_slice = INIT[256 * idx +: 256];
endfunction

wire [15:0] DOA;
wire [15:0] DOB;
wire [15:0] DIA = PORT_A_WR_DATA;
wire [15:0] DIB = PORT_B_WR_DATA;

assign PORT_A_RD_DATA = DOA;
assign PORT_B_RD_DATA = DOB;

wire BYTE_A, BYTEWE_A;
wire BYTE_B, BYTEWE_B;

generate

if (PORT_A_WIDTH == 8) begin
	assign BYTE_A = PORT_A_ADDR[0];
	assign BYTEWE_A = 1;
end else begin
	assign BYTE_A = PORT_A_WR_EN == 2;
	assign BYTEWE_A = ^PORT_A_WR_EN;
end

if (PORT_B_WIDTH == 8) begin
	assign BYTE_B = PORT_B_ADDR[0];
	assign BYTEWE_B = 1;
end else begin
	assign BYTE_B = PORT_B_WR_EN == 2;
	assign BYTEWE_B = ^PORT_B_WR_EN;
end

endgenerate

EG_PHY_BRAM32K #(
	.INIT_00(init_slice('h00)),
	.INIT_01(init_slice('h01)),
	.INIT_02(init_slice('h02)),
	.INIT_03(init_slice('h03)),
	.INIT_04(init_slice('h04)),
	.INIT_05(init_slice('h05)),
	.INIT_06(init_slice('h06)),
	.INIT_07(init_slice('h07)),
	.INIT_08(init_slice('h08)),
	.INIT_09(init_slice('h09)),
	.INIT_0A(init_slice('h0a)),
	.INIT_0B(init_slice('h0b)),
	.INIT_0C(init_slice('h0c)),
	.INIT_0D(init_slice('h0d)),
	.INIT_0E(init_slice('h0e)),
	.INIT_0F(init_slice('h0f)),
	.INIT_10(init_slice('h10)),
	.INIT_11(init_slice('h11)),
	.INIT_12(init_slice('h12)),
	.INIT_13(init_slice('h13)),
	.INIT_14(init_slice('h14)),
	.INIT_15(init_slice('h15)),
	.INIT_16(init_slice('h16)),
	.INIT_17(init_slice('h17)),
	.INIT_18(init_slice('h18)),
	.INIT_19(init_slice('h19)),
	.INIT_1A(init_slice('h1a)),
	.INIT_1B(init_slice('h1b)),
	.INIT_1C(init_slice('h1c)),
	.INIT_1D(init_slice('h1d)),
	.INIT_1E(init_slice('h1e)),
	.INIT_1F(init_slice('h1f)),
	.INIT_20(init_slice('h20)),
	.INIT_21(init_slice('h21)),
	.INIT_22(init_slice('h22)),
	.INIT_23(init_slice('h23)),
	.INIT_24(init_slice('h24)),
	.INIT_25(init_slice('h25)),
	.INIT_26(init_slice('h26)),
	.INIT_27(init_slice('h27)),
	.INIT_28(init_slice('h28)),
	.INIT_29(init_slice('h29)),
	.INIT_2A(init_slice('h2a)),
	.INIT_2B(init_slice('h2b)),
	.INIT_2C(init_slice('h2c)),
	.INIT_2D(init_slice('h2d)),
	.INIT_2E(init_slice('h2e)),
	.INIT_2F(init_slice('h2f)),
	.INIT_30(init_slice('h30)),
	.INIT_31(init_slice('h31)),
	.INIT_32(init_slice('h32)),
	.INIT_33(init_slice('h33)),
	.INIT_34(init_slice('h34)),
	.INIT_35(init_slice('h35)),
	.INIT_36(init_slice('h36)),
	.INIT_37(init_slice('h37)),
	.INIT_38(init_slice('h38)),
	.INIT_39(init_slice('h39)),
	.INIT_3A(init_slice('h3a)),
	.INIT_3B(init_slice('h3b)),
	.INIT_3C(init_slice('h3c)),
	.INIT_3D(init_slice('h3d)),
	.INIT_3E(init_slice('h3e)),
	.INIT_3F(init_slice('h3f)),
	.INIT_40(init_slice('h40)),
	.INIT_41(init_slice('h41)),
	.INIT_42(init_slice('h42)),
	.INIT_43(init_slice('h43)),
	.INIT_44(init_slice('h44)),
	.INIT_45(init_slice('h45)),
	.INIT_46(init_slice('h46)),
	.INIT_47(init_slice('h47)),
	.INIT_48(init_slice('h48)),
	.INIT_49(init_slice('h49)),
	.INIT_4A(init_slice('h4a)),
	.INIT_4B(init_slice('h4b)),
	.INIT_4C(init_slice('h4c)),
	.INIT_4D(init_slice('h4d)),
	.INIT_4E(init_slice('h4e)),
	.INIT_4F(init_slice('h4f)),
	.INIT_50(init_slice('h50)),
	.INIT_51(init_slice('h51)),
	.INIT_52(init_slice('h52)),
	.INIT_53(init_slice('h53)),
	.INIT_54(init_slice('h54)),
	.INIT_55(init_slice('h55)),
	.INIT_56(init_slice('h56)),
	.INIT_57(init_slice('h57)),
	.INIT_58(init_slice('h58)),
	.INIT_59(init_slice('h59)),
	.INIT_5A(init_slice('h5a)),
	.INIT_5B(init_slice('h5b)),
	.INIT_5C(init_slice('h5c)),
	.INIT_5D(init_slice('h5d)),
	.INIT_5E(init_slice('h5e)),
	.INIT_5F(init_slice('h5f)),
	.INIT_60(init_slice('h60)),
	.INIT_61(init_slice('h61)),
	.INIT_62(init_slice('h62)),
	.INIT_63(init_slice('h63)),
	.INIT_64(init_slice('h64)),
	.INIT_65(init_slice('h65)),
	.INIT_66(init_slice('h66)),
	.INIT_67(init_slice('h67)),
	.INIT_68(init_slice('h68)),
	.INIT_69(init_slice('h69)),
	.INIT_6A(init_slice('h6a)),
	.INIT_6B(init_slice('h6b)),
	.INIT_6C(init_slice('h6c)),
	.INIT_6D(init_slice('h6d)),
	.INIT_6E(init_slice('h6e)),
	.INIT_6F(init_slice('h6f)),
	.INIT_70(init_slice('h70)),
	.INIT_71(init_slice('h71)),
	.INIT_72(init_slice('h72)),
	.INIT_73(init_slice('h73)),
	.INIT_74(init_slice('h74)),
	.INIT_75(init_slice('h75)),
	.INIT_76(init_slice('h76)),
	.INIT_77(init_slice('h77)),
	.INIT_78(init_slice('h78)),
	.INIT_79(init_slice('h79)),
	.INIT_7A(init_slice('h7a)),
	.INIT_7B(init_slice('h7b)),
	.INIT_7C(init_slice('h7c)),
	.INIT_7D(init_slice('h7d)),
	.INIT_7E(init_slice('h7e)),
	.INIT_7F(init_slice('h7f)),
	.MODE("DP16K"),
	.DATA_WIDTH_A($sformatf("%d", PORT_A_WIDTH)),
	.DATA_WIDTH_B($sformatf("%d", PORT_B_WIDTH)),
	.REGMODE_A("NOREG"),
	.REGMODE_B("NOREG"),
	.WRITEMODE_A(PORT_A_OPTION_WRITEMODE),
	.WRITEMODE_B(PORT_B_OPTION_WRITEMODE),
	.CLKAMUX(PORT_A_CLK_POL ? "SIG" : "INV"),
	.CLKBMUX(PORT_B_CLK_POL ? "SIG" : "INV"),
) _TECHMAP_REPLACE_ (
	.clka(PORT_A_CLK),
	.csa(PORT_A_CLK_EN),
	.wea(|PORT_A_WR_EN),
	.ocea(1'b1),
	.rsta(1'b0),
	.addra(PORT_A_ADDR[11:1]),
	.bytea(BYTE_A),
	.bytewea(BYTEWE_A),
	.dia(DIA),
	.doa(DOA),

	.clkb(PORT_B_CLK),
	.csb(PORT_B_CLK_EN),
	.web(|PORT_B_WR_EN),
	.ocea(1'b1),
	.rsta(1'b0),
	.addrb(PORT_B_ADDR[11:1]),
	.byteb(BYTE_B),
	.byteweb(BYTEWE_B),
	.dib(DIB),
	.dob(DOB),
);

endmodule
