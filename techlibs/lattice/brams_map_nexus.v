module $__NX_DP16K_ (...);

parameter INIT = 0;

parameter PORT_A_OPTION_RESETMODE = "SYNC";
parameter PORT_A_WIDTH = 18;
parameter PORT_A_WR_BE_WIDTH = 2;

input PORT_A_CLK;
input PORT_A_CLK_EN;
input PORT_A_WR_EN;
input PORT_A_RD_SRST;
input PORT_A_RD_ARST;
input [13:0] PORT_A_ADDR;
input [PORT_A_WR_BE_WIDTH-1:0] PORT_A_WR_BE;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

parameter PORT_B_OPTION_RESETMODE = "SYNC";
parameter PORT_B_WIDTH = 18;
parameter PORT_B_WR_BE_WIDTH = 2;

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
	integer i;
	init_slice = 0;
	for (i = 0; i < 32; i = i + 1) begin
		init_slice[i*10+:9] = INIT[(idx * 32 + i) * 9+:9];
	end
endfunction

wire [17:0] DOA;
wire [17:0] DOB;
wire [17:0] DIA = PORT_A_WR_DATA;
wire [17:0] DIB = PORT_B_WR_DATA;
wire [13:0] ADA;
wire [13:0] ADB;

generate

case(PORT_A_WIDTH)
1: assign ADA = PORT_A_ADDR;
2: assign ADA = {PORT_A_ADDR[13:1], 1'b1};
4: assign ADA = {PORT_A_ADDR[13:2], 2'b11};
9: assign ADA = {PORT_A_ADDR[13:3], 3'b111};
18: assign ADA = {PORT_A_ADDR[13:4], 2'b11, PORT_A_WR_BE};
endcase

case(PORT_B_WIDTH)
1: assign ADB = PORT_B_ADDR;
2: assign ADB = {PORT_B_ADDR[13:1], 1'b1};
4: assign ADB = {PORT_B_ADDR[13:2], 2'b11};
9: assign ADB = {PORT_B_ADDR[13:3], 3'b111};
18: assign ADB = {PORT_B_ADDR[13:4], 2'b11, PORT_B_WR_BE};
endcase

endgenerate

assign PORT_A_RD_DATA = DOA;
assign PORT_B_RD_DATA = DOB;

DP16K #(
	.INITVAL_00($sformatf("0x%080x", init_slice('h00))),
	.INITVAL_01($sformatf("0x%080x", init_slice('h01))),
	.INITVAL_02($sformatf("0x%080x", init_slice('h02))),
	.INITVAL_03($sformatf("0x%080x", init_slice('h03))),
	.INITVAL_04($sformatf("0x%080x", init_slice('h04))),
	.INITVAL_05($sformatf("0x%080x", init_slice('h05))),
	.INITVAL_06($sformatf("0x%080x", init_slice('h06))),
	.INITVAL_07($sformatf("0x%080x", init_slice('h07))),
	.INITVAL_08($sformatf("0x%080x", init_slice('h08))),
	.INITVAL_09($sformatf("0x%080x", init_slice('h09))),
	.INITVAL_0A($sformatf("0x%080x", init_slice('h0a))),
	.INITVAL_0B($sformatf("0x%080x", init_slice('h0b))),
	.INITVAL_0C($sformatf("0x%080x", init_slice('h0c))),
	.INITVAL_0D($sformatf("0x%080x", init_slice('h0d))),
	.INITVAL_0E($sformatf("0x%080x", init_slice('h0e))),
	.INITVAL_0F($sformatf("0x%080x", init_slice('h0f))),
	.INITVAL_10($sformatf("0x%080x", init_slice('h10))),
	.INITVAL_11($sformatf("0x%080x", init_slice('h11))),
	.INITVAL_12($sformatf("0x%080x", init_slice('h12))),
	.INITVAL_13($sformatf("0x%080x", init_slice('h13))),
	.INITVAL_14($sformatf("0x%080x", init_slice('h14))),
	.INITVAL_15($sformatf("0x%080x", init_slice('h15))),
	.INITVAL_16($sformatf("0x%080x", init_slice('h16))),
	.INITVAL_17($sformatf("0x%080x", init_slice('h17))),
	.INITVAL_18($sformatf("0x%080x", init_slice('h18))),
	.INITVAL_19($sformatf("0x%080x", init_slice('h19))),
	.INITVAL_1A($sformatf("0x%080x", init_slice('h1a))),
	.INITVAL_1B($sformatf("0x%080x", init_slice('h1b))),
	.INITVAL_1C($sformatf("0x%080x", init_slice('h1c))),
	.INITVAL_1D($sformatf("0x%080x", init_slice('h1d))),
	.INITVAL_1E($sformatf("0x%080x", init_slice('h1e))),
	.INITVAL_1F($sformatf("0x%080x", init_slice('h1f))),
	.INITVAL_20($sformatf("0x%080x", init_slice('h20))),
	.INITVAL_21($sformatf("0x%080x", init_slice('h21))),
	.INITVAL_22($sformatf("0x%080x", init_slice('h22))),
	.INITVAL_23($sformatf("0x%080x", init_slice('h23))),
	.INITVAL_24($sformatf("0x%080x", init_slice('h24))),
	.INITVAL_25($sformatf("0x%080x", init_slice('h25))),
	.INITVAL_26($sformatf("0x%080x", init_slice('h26))),
	.INITVAL_27($sformatf("0x%080x", init_slice('h27))),
	.INITVAL_28($sformatf("0x%080x", init_slice('h28))),
	.INITVAL_29($sformatf("0x%080x", init_slice('h29))),
	.INITVAL_2A($sformatf("0x%080x", init_slice('h2a))),
	.INITVAL_2B($sformatf("0x%080x", init_slice('h2b))),
	.INITVAL_2C($sformatf("0x%080x", init_slice('h2c))),
	.INITVAL_2D($sformatf("0x%080x", init_slice('h2d))),
	.INITVAL_2E($sformatf("0x%080x", init_slice('h2e))),
	.INITVAL_2F($sformatf("0x%080x", init_slice('h2f))),
	.INITVAL_30($sformatf("0x%080x", init_slice('h30))),
	.INITVAL_31($sformatf("0x%080x", init_slice('h31))),
	.INITVAL_32($sformatf("0x%080x", init_slice('h32))),
	.INITVAL_33($sformatf("0x%080x", init_slice('h33))),
	.INITVAL_34($sformatf("0x%080x", init_slice('h34))),
	.INITVAL_35($sformatf("0x%080x", init_slice('h35))),
	.INITVAL_36($sformatf("0x%080x", init_slice('h36))),
	.INITVAL_37($sformatf("0x%080x", init_slice('h37))),
	.INITVAL_38($sformatf("0x%080x", init_slice('h38))),
	.INITVAL_39($sformatf("0x%080x", init_slice('h39))),
	.INITVAL_3A($sformatf("0x%080x", init_slice('h3a))),
	.INITVAL_3B($sformatf("0x%080x", init_slice('h3b))),
	.INITVAL_3C($sformatf("0x%080x", init_slice('h3c))),
	.INITVAL_3D($sformatf("0x%080x", init_slice('h3d))),
	.INITVAL_3E($sformatf("0x%080x", init_slice('h3e))),
	.INITVAL_3F($sformatf("0x%080x", init_slice('h3f))),
	.DATA_WIDTH_A($sformatf("X%0d", PORT_A_WIDTH)),
	.DATA_WIDTH_B($sformatf("X%0d", PORT_B_WIDTH)),
	.OUTREG_A("BYPASSED"),
	.OUTREG_B("BYPASSED"),
	.RESETMODE_A(PORT_A_OPTION_RESETMODE),
	.RESETMODE_B(PORT_B_OPTION_RESETMODE),
	.ASYNC_RST_RELEASE_A(PORT_A_OPTION_RESETMODE),
	.ASYNC_RST_RELEASE_B(PORT_B_OPTION_RESETMODE),
	.CSDECODE_A("111"),
	.CSDECODE_B("111"),
	.GSR("DISABLED"),
) _TECHMAP_REPLACE_ (
	.CLKA(PORT_A_CLK),
	.WEA(PORT_A_WIDTH == 18 ? PORT_A_WR_EN : (PORT_A_WR_EN | PORT_A_WR_BE[0])),
	.CEA(PORT_A_CLK_EN),
	.RSTA(PORT_A_OPTION_RESETMODE == "SYNC" ? PORT_A_RD_SRST : PORT_A_RD_ARST),
	.CSA(3'b111),
	.DIA(DIA),
	.DOA(DOA),
	.ADA(ADA),

	.CLKB(PORT_B_CLK),
	.WEB(PORT_B_WIDTH == 18 ? PORT_B_WR_EN : (PORT_B_WR_EN | PORT_B_WR_BE[0])),
	.CEB(PORT_B_CLK_EN),
	.RSTB(PORT_B_OPTION_RESETMODE == "SYNC" ? PORT_B_RD_SRST : PORT_B_RD_ARST),
	.CSB(3'b111),
	.ADB(ADB),
	.DIB(DIB),
	.DOB(DOB),
);

endmodule


module $__NX_PDP16K_ (...);

parameter INIT = 0;
parameter OPTION_SAME_CLOCK = 1;

parameter PORT_R_WIDTH = 36;
parameter PORT_R_OPTION_RESETMODE = "SYNC";

input CLK_C;

input PORT_R_CLK;
input PORT_R_CLK_EN;
input PORT_R_RD_SRST;
input PORT_R_RD_ARST;
input [13:0] PORT_R_ADDR;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;

parameter PORT_W_WIDTH = 36;
parameter PORT_W_WR_EN_WIDTH = 4;

input PORT_W_CLK;
input PORT_W_CLK_EN;
input [13:0] PORT_W_ADDR;
input [PORT_W_WR_EN_WIDTH-1:0] PORT_W_WR_EN;
input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;

function [319:0] init_slice;
	input integer idx;
	integer i;
	init_slice = 0;
	for (i = 0; i < 32; i = i + 1) begin
		init_slice[i*10+:9] = INIT[(idx * 32 + i) * 9+:9];
	end
endfunction

wire [35:0] DI = PORT_W_WR_DATA;
wire [35:0] DO;

assign PORT_R_RD_DATA = DO;

wire [13:0] ADW;
wire [13:0] ADR;

generate

case (PORT_W_WIDTH)
1: assign ADW = PORT_W_ADDR;
2: assign ADW = {PORT_W_ADDR[13:1], 1'b1};
4: assign ADW = {PORT_W_ADDR[13:2], 2'b11};
9: assign ADW = {PORT_W_ADDR[13:3], 3'b111};
18: assign ADW = {PORT_W_ADDR[13:4], 2'b11, PORT_W_WR_EN};
36: assign ADW = {PORT_W_ADDR[13:5], 1'b1, PORT_W_WR_EN};
endcase

case (PORT_R_WIDTH)
1: assign ADR = PORT_R_ADDR;
2: assign ADR = {PORT_R_ADDR[13:1], 1'b1};
4: assign ADR = {PORT_R_ADDR[13:2], 2'b11};
9: assign ADR = {PORT_R_ADDR[13:3], 3'b111};
18: assign ADR = {PORT_R_ADDR[13:4], 4'b1111};
36: assign ADR = {PORT_R_ADDR[13:5], 5'b11111};
endcase

if (OPTION_SAME_CLOCK) begin

PDPSC16K #(
	.INITVAL_00($sformatf("0x%080x", init_slice('h00))),
	.INITVAL_01($sformatf("0x%080x", init_slice('h01))),
	.INITVAL_02($sformatf("0x%080x", init_slice('h02))),
	.INITVAL_03($sformatf("0x%080x", init_slice('h03))),
	.INITVAL_04($sformatf("0x%080x", init_slice('h04))),
	.INITVAL_05($sformatf("0x%080x", init_slice('h05))),
	.INITVAL_06($sformatf("0x%080x", init_slice('h06))),
	.INITVAL_07($sformatf("0x%080x", init_slice('h07))),
	.INITVAL_08($sformatf("0x%080x", init_slice('h08))),
	.INITVAL_09($sformatf("0x%080x", init_slice('h09))),
	.INITVAL_0A($sformatf("0x%080x", init_slice('h0a))),
	.INITVAL_0B($sformatf("0x%080x", init_slice('h0b))),
	.INITVAL_0C($sformatf("0x%080x", init_slice('h0c))),
	.INITVAL_0D($sformatf("0x%080x", init_slice('h0d))),
	.INITVAL_0E($sformatf("0x%080x", init_slice('h0e))),
	.INITVAL_0F($sformatf("0x%080x", init_slice('h0f))),
	.INITVAL_10($sformatf("0x%080x", init_slice('h10))),
	.INITVAL_11($sformatf("0x%080x", init_slice('h11))),
	.INITVAL_12($sformatf("0x%080x", init_slice('h12))),
	.INITVAL_13($sformatf("0x%080x", init_slice('h13))),
	.INITVAL_14($sformatf("0x%080x", init_slice('h14))),
	.INITVAL_15($sformatf("0x%080x", init_slice('h15))),
	.INITVAL_16($sformatf("0x%080x", init_slice('h16))),
	.INITVAL_17($sformatf("0x%080x", init_slice('h17))),
	.INITVAL_18($sformatf("0x%080x", init_slice('h18))),
	.INITVAL_19($sformatf("0x%080x", init_slice('h19))),
	.INITVAL_1A($sformatf("0x%080x", init_slice('h1a))),
	.INITVAL_1B($sformatf("0x%080x", init_slice('h1b))),
	.INITVAL_1C($sformatf("0x%080x", init_slice('h1c))),
	.INITVAL_1D($sformatf("0x%080x", init_slice('h1d))),
	.INITVAL_1E($sformatf("0x%080x", init_slice('h1e))),
	.INITVAL_1F($sformatf("0x%080x", init_slice('h1f))),
	.INITVAL_20($sformatf("0x%080x", init_slice('h20))),
	.INITVAL_21($sformatf("0x%080x", init_slice('h21))),
	.INITVAL_22($sformatf("0x%080x", init_slice('h22))),
	.INITVAL_23($sformatf("0x%080x", init_slice('h23))),
	.INITVAL_24($sformatf("0x%080x", init_slice('h24))),
	.INITVAL_25($sformatf("0x%080x", init_slice('h25))),
	.INITVAL_26($sformatf("0x%080x", init_slice('h26))),
	.INITVAL_27($sformatf("0x%080x", init_slice('h27))),
	.INITVAL_28($sformatf("0x%080x", init_slice('h28))),
	.INITVAL_29($sformatf("0x%080x", init_slice('h29))),
	.INITVAL_2A($sformatf("0x%080x", init_slice('h2a))),
	.INITVAL_2B($sformatf("0x%080x", init_slice('h2b))),
	.INITVAL_2C($sformatf("0x%080x", init_slice('h2c))),
	.INITVAL_2D($sformatf("0x%080x", init_slice('h2d))),
	.INITVAL_2E($sformatf("0x%080x", init_slice('h2e))),
	.INITVAL_2F($sformatf("0x%080x", init_slice('h2f))),
	.INITVAL_30($sformatf("0x%080x", init_slice('h30))),
	.INITVAL_31($sformatf("0x%080x", init_slice('h31))),
	.INITVAL_32($sformatf("0x%080x", init_slice('h32))),
	.INITVAL_33($sformatf("0x%080x", init_slice('h33))),
	.INITVAL_34($sformatf("0x%080x", init_slice('h34))),
	.INITVAL_35($sformatf("0x%080x", init_slice('h35))),
	.INITVAL_36($sformatf("0x%080x", init_slice('h36))),
	.INITVAL_37($sformatf("0x%080x", init_slice('h37))),
	.INITVAL_38($sformatf("0x%080x", init_slice('h38))),
	.INITVAL_39($sformatf("0x%080x", init_slice('h39))),
	.INITVAL_3A($sformatf("0x%080x", init_slice('h3a))),
	.INITVAL_3B($sformatf("0x%080x", init_slice('h3b))),
	.INITVAL_3C($sformatf("0x%080x", init_slice('h3c))),
	.INITVAL_3D($sformatf("0x%080x", init_slice('h3d))),
	.INITVAL_3E($sformatf("0x%080x", init_slice('h3e))),
	.INITVAL_3F($sformatf("0x%080x", init_slice('h3f))),
	.DATA_WIDTH_W($sformatf("X%0d", PORT_W_WIDTH)),
	.DATA_WIDTH_R($sformatf("X%0d", PORT_R_WIDTH)),
	.OUTREG("BYPASSED"),
	.RESETMODE(PORT_R_OPTION_RESETMODE),
	.ASYNC_RST_RELEASE(PORT_R_OPTION_RESETMODE),
	.CSDECODE_W("111"),
	.CSDECODE_R("111"),
	.ECC("DISABLED"),
	.GSR("DISABLED"),
) _TECHMAP_REPLACE_ (
	.CLK(CLK_C),

	.CEW(PORT_W_CLK_EN & (|PORT_W_WR_EN)),
	.CSW(3'b111),
	.ADW(ADW),
	.DI(DI),

	.CER(PORT_R_CLK_EN),
	.RST(PORT_R_OPTION_RESETMODE == "SYNC" ? PORT_R_RD_SRST : PORT_R_RD_ARST),
	.CSR(3'b111),
	.ADR(ADR),
	.DO(DO),
);

end else begin

PDP16K #(
	.INITVAL_00($sformatf("0x%080x", init_slice('h00))),
	.INITVAL_01($sformatf("0x%080x", init_slice('h01))),
	.INITVAL_02($sformatf("0x%080x", init_slice('h02))),
	.INITVAL_03($sformatf("0x%080x", init_slice('h03))),
	.INITVAL_04($sformatf("0x%080x", init_slice('h04))),
	.INITVAL_05($sformatf("0x%080x", init_slice('h05))),
	.INITVAL_06($sformatf("0x%080x", init_slice('h06))),
	.INITVAL_07($sformatf("0x%080x", init_slice('h07))),
	.INITVAL_08($sformatf("0x%080x", init_slice('h08))),
	.INITVAL_09($sformatf("0x%080x", init_slice('h09))),
	.INITVAL_0A($sformatf("0x%080x", init_slice('h0a))),
	.INITVAL_0B($sformatf("0x%080x", init_slice('h0b))),
	.INITVAL_0C($sformatf("0x%080x", init_slice('h0c))),
	.INITVAL_0D($sformatf("0x%080x", init_slice('h0d))),
	.INITVAL_0E($sformatf("0x%080x", init_slice('h0e))),
	.INITVAL_0F($sformatf("0x%080x", init_slice('h0f))),
	.INITVAL_10($sformatf("0x%080x", init_slice('h10))),
	.INITVAL_11($sformatf("0x%080x", init_slice('h11))),
	.INITVAL_12($sformatf("0x%080x", init_slice('h12))),
	.INITVAL_13($sformatf("0x%080x", init_slice('h13))),
	.INITVAL_14($sformatf("0x%080x", init_slice('h14))),
	.INITVAL_15($sformatf("0x%080x", init_slice('h15))),
	.INITVAL_16($sformatf("0x%080x", init_slice('h16))),
	.INITVAL_17($sformatf("0x%080x", init_slice('h17))),
	.INITVAL_18($sformatf("0x%080x", init_slice('h18))),
	.INITVAL_19($sformatf("0x%080x", init_slice('h19))),
	.INITVAL_1A($sformatf("0x%080x", init_slice('h1a))),
	.INITVAL_1B($sformatf("0x%080x", init_slice('h1b))),
	.INITVAL_1C($sformatf("0x%080x", init_slice('h1c))),
	.INITVAL_1D($sformatf("0x%080x", init_slice('h1d))),
	.INITVAL_1E($sformatf("0x%080x", init_slice('h1e))),
	.INITVAL_1F($sformatf("0x%080x", init_slice('h1f))),
	.INITVAL_20($sformatf("0x%080x", init_slice('h20))),
	.INITVAL_21($sformatf("0x%080x", init_slice('h21))),
	.INITVAL_22($sformatf("0x%080x", init_slice('h22))),
	.INITVAL_23($sformatf("0x%080x", init_slice('h23))),
	.INITVAL_24($sformatf("0x%080x", init_slice('h24))),
	.INITVAL_25($sformatf("0x%080x", init_slice('h25))),
	.INITVAL_26($sformatf("0x%080x", init_slice('h26))),
	.INITVAL_27($sformatf("0x%080x", init_slice('h27))),
	.INITVAL_28($sformatf("0x%080x", init_slice('h28))),
	.INITVAL_29($sformatf("0x%080x", init_slice('h29))),
	.INITVAL_2A($sformatf("0x%080x", init_slice('h2a))),
	.INITVAL_2B($sformatf("0x%080x", init_slice('h2b))),
	.INITVAL_2C($sformatf("0x%080x", init_slice('h2c))),
	.INITVAL_2D($sformatf("0x%080x", init_slice('h2d))),
	.INITVAL_2E($sformatf("0x%080x", init_slice('h2e))),
	.INITVAL_2F($sformatf("0x%080x", init_slice('h2f))),
	.INITVAL_30($sformatf("0x%080x", init_slice('h30))),
	.INITVAL_31($sformatf("0x%080x", init_slice('h31))),
	.INITVAL_32($sformatf("0x%080x", init_slice('h32))),
	.INITVAL_33($sformatf("0x%080x", init_slice('h33))),
	.INITVAL_34($sformatf("0x%080x", init_slice('h34))),
	.INITVAL_35($sformatf("0x%080x", init_slice('h35))),
	.INITVAL_36($sformatf("0x%080x", init_slice('h36))),
	.INITVAL_37($sformatf("0x%080x", init_slice('h37))),
	.INITVAL_38($sformatf("0x%080x", init_slice('h38))),
	.INITVAL_39($sformatf("0x%080x", init_slice('h39))),
	.INITVAL_3A($sformatf("0x%080x", init_slice('h3a))),
	.INITVAL_3B($sformatf("0x%080x", init_slice('h3b))),
	.INITVAL_3C($sformatf("0x%080x", init_slice('h3c))),
	.INITVAL_3D($sformatf("0x%080x", init_slice('h3d))),
	.INITVAL_3E($sformatf("0x%080x", init_slice('h3e))),
	.INITVAL_3F($sformatf("0x%080x", init_slice('h3f))),
	.DATA_WIDTH_W($sformatf("X%0d", PORT_W_WIDTH)),
	.DATA_WIDTH_R($sformatf("X%0d", PORT_R_WIDTH)),
	.OUTREG("BYPASSED"),
	.RESETMODE(PORT_R_OPTION_RESETMODE),
	.ASYNC_RST_RELEASE(PORT_R_OPTION_RESETMODE),
	.CSDECODE_W("111"),
	.CSDECODE_R("111"),
	.ECC("DISABLED"),
	.GSR("DISABLED"),
) _TECHMAP_REPLACE_ (
	.CLKW(PORT_W_CLK),
	.CEW(PORT_W_CLK_EN & (|PORT_W_WR_EN)),
	.CSW(3'b111),
	.ADW(ADW),
	.DI(DI),

	.CLKR(PORT_R_CLK),
	.CER(PORT_R_CLK_EN),
	.RST(PORT_R_OPTION_RESETMODE == "SYNC" ? PORT_R_RD_SRST : PORT_R_RD_ARST),
	.CSR(3'b111),
	.ADR(ADR),
	.DO(DO),
);

end

endgenerate

endmodule
