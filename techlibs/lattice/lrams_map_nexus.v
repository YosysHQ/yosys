module $__NX_DPSC512K_ (...);

parameter INIT = 0;
parameter OPTION_RESETMODE = "SYNC";

input CLK_C;

input PORT_A_CLK;
input PORT_A_CLK_EN;
input PORT_A_WR_EN;
input PORT_A_RD_SRST;
input PORT_A_RD_ARST;
input [13:0] PORT_A_ADDR;
input [3:0] PORT_A_WR_BE;
input [31:0] PORT_A_WR_DATA;
output [31:0] PORT_A_RD_DATA;

input PORT_B_CLK;
input PORT_B_CLK_EN;
input PORT_B_WR_EN;
input PORT_B_RD_SRST;
input PORT_B_RD_ARST;
input [13:0] PORT_B_ADDR;
input [3:0] PORT_B_WR_BE;
input [31:0] PORT_B_WR_DATA;
output [31:0] PORT_B_RD_DATA;

function [5119:0] init_slice;
	input integer idx;
	integer i, j;
	init_slice = 0;
	for (i = 0; i < 128; i = i + 1) begin
		init_slice[i*40+:32] = INIT[(idx * 128 + i) * 32+:32];
	end
endfunction

DPSC512K #(
	.INITVAL_00($sformatf("0x%01280x", init_slice('h00))),
	.INITVAL_01($sformatf("0x%01280x", init_slice('h01))),
	.INITVAL_02($sformatf("0x%01280x", init_slice('h02))),
	.INITVAL_03($sformatf("0x%01280x", init_slice('h03))),
	.INITVAL_04($sformatf("0x%01280x", init_slice('h04))),
	.INITVAL_05($sformatf("0x%01280x", init_slice('h05))),
	.INITVAL_06($sformatf("0x%01280x", init_slice('h06))),
	.INITVAL_07($sformatf("0x%01280x", init_slice('h07))),
	.INITVAL_08($sformatf("0x%01280x", init_slice('h08))),
	.INITVAL_09($sformatf("0x%01280x", init_slice('h09))),
	.INITVAL_0A($sformatf("0x%01280x", init_slice('h0a))),
	.INITVAL_0B($sformatf("0x%01280x", init_slice('h0b))),
	.INITVAL_0C($sformatf("0x%01280x", init_slice('h0c))),
	.INITVAL_0D($sformatf("0x%01280x", init_slice('h0d))),
	.INITVAL_0E($sformatf("0x%01280x", init_slice('h0e))),
	.INITVAL_0F($sformatf("0x%01280x", init_slice('h0f))),
	.INITVAL_10($sformatf("0x%01280x", init_slice('h10))),
	.INITVAL_11($sformatf("0x%01280x", init_slice('h11))),
	.INITVAL_12($sformatf("0x%01280x", init_slice('h12))),
	.INITVAL_13($sformatf("0x%01280x", init_slice('h13))),
	.INITVAL_14($sformatf("0x%01280x", init_slice('h14))),
	.INITVAL_15($sformatf("0x%01280x", init_slice('h15))),
	.INITVAL_16($sformatf("0x%01280x", init_slice('h16))),
	.INITVAL_17($sformatf("0x%01280x", init_slice('h17))),
	.INITVAL_18($sformatf("0x%01280x", init_slice('h18))),
	.INITVAL_19($sformatf("0x%01280x", init_slice('h19))),
	.INITVAL_1A($sformatf("0x%01280x", init_slice('h1a))),
	.INITVAL_1B($sformatf("0x%01280x", init_slice('h1b))),
	.INITVAL_1C($sformatf("0x%01280x", init_slice('h1c))),
	.INITVAL_1D($sformatf("0x%01280x", init_slice('h1d))),
	.INITVAL_1E($sformatf("0x%01280x", init_slice('h1e))),
	.INITVAL_1F($sformatf("0x%01280x", init_slice('h1f))),
	.INITVAL_20($sformatf("0x%01280x", init_slice('h20))),
	.INITVAL_21($sformatf("0x%01280x", init_slice('h21))),
	.INITVAL_22($sformatf("0x%01280x", init_slice('h22))),
	.INITVAL_23($sformatf("0x%01280x", init_slice('h23))),
	.INITVAL_24($sformatf("0x%01280x", init_slice('h24))),
	.INITVAL_25($sformatf("0x%01280x", init_slice('h25))),
	.INITVAL_26($sformatf("0x%01280x", init_slice('h26))),
	.INITVAL_27($sformatf("0x%01280x", init_slice('h27))),
	.INITVAL_28($sformatf("0x%01280x", init_slice('h28))),
	.INITVAL_29($sformatf("0x%01280x", init_slice('h29))),
	.INITVAL_2A($sformatf("0x%01280x", init_slice('h2a))),
	.INITVAL_2B($sformatf("0x%01280x", init_slice('h2b))),
	.INITVAL_2C($sformatf("0x%01280x", init_slice('h2c))),
	.INITVAL_2D($sformatf("0x%01280x", init_slice('h2d))),
	.INITVAL_2E($sformatf("0x%01280x", init_slice('h2e))),
	.INITVAL_2F($sformatf("0x%01280x", init_slice('h2f))),
	.INITVAL_30($sformatf("0x%01280x", init_slice('h30))),
	.INITVAL_31($sformatf("0x%01280x", init_slice('h31))),
	.INITVAL_32($sformatf("0x%01280x", init_slice('h32))),
	.INITVAL_33($sformatf("0x%01280x", init_slice('h33))),
	.INITVAL_34($sformatf("0x%01280x", init_slice('h34))),
	.INITVAL_35($sformatf("0x%01280x", init_slice('h35))),
	.INITVAL_36($sformatf("0x%01280x", init_slice('h36))),
	.INITVAL_37($sformatf("0x%01280x", init_slice('h37))),
	.INITVAL_38($sformatf("0x%01280x", init_slice('h38))),
	.INITVAL_39($sformatf("0x%01280x", init_slice('h39))),
	.INITVAL_3A($sformatf("0x%01280x", init_slice('h3a))),
	.INITVAL_3B($sformatf("0x%01280x", init_slice('h3b))),
	.INITVAL_3C($sformatf("0x%01280x", init_slice('h3c))),
	.INITVAL_3D($sformatf("0x%01280x", init_slice('h3d))),
	.INITVAL_3E($sformatf("0x%01280x", init_slice('h3e))),
	.INITVAL_3F($sformatf("0x%01280x", init_slice('h3f))),
	.INITVAL_40($sformatf("0x%01280x", init_slice('h40))),
	.INITVAL_41($sformatf("0x%01280x", init_slice('h41))),
	.INITVAL_42($sformatf("0x%01280x", init_slice('h42))),
	.INITVAL_43($sformatf("0x%01280x", init_slice('h43))),
	.INITVAL_44($sformatf("0x%01280x", init_slice('h44))),
	.INITVAL_45($sformatf("0x%01280x", init_slice('h45))),
	.INITVAL_46($sformatf("0x%01280x", init_slice('h46))),
	.INITVAL_47($sformatf("0x%01280x", init_slice('h47))),
	.INITVAL_48($sformatf("0x%01280x", init_slice('h48))),
	.INITVAL_49($sformatf("0x%01280x", init_slice('h49))),
	.INITVAL_4A($sformatf("0x%01280x", init_slice('h4a))),
	.INITVAL_4B($sformatf("0x%01280x", init_slice('h4b))),
	.INITVAL_4C($sformatf("0x%01280x", init_slice('h4c))),
	.INITVAL_4D($sformatf("0x%01280x", init_slice('h4d))),
	.INITVAL_4E($sformatf("0x%01280x", init_slice('h4e))),
	.INITVAL_4F($sformatf("0x%01280x", init_slice('h4f))),
	.INITVAL_50($sformatf("0x%01280x", init_slice('h50))),
	.INITVAL_51($sformatf("0x%01280x", init_slice('h51))),
	.INITVAL_52($sformatf("0x%01280x", init_slice('h52))),
	.INITVAL_53($sformatf("0x%01280x", init_slice('h53))),
	.INITVAL_54($sformatf("0x%01280x", init_slice('h54))),
	.INITVAL_55($sformatf("0x%01280x", init_slice('h55))),
	.INITVAL_56($sformatf("0x%01280x", init_slice('h56))),
	.INITVAL_57($sformatf("0x%01280x", init_slice('h57))),
	.INITVAL_58($sformatf("0x%01280x", init_slice('h58))),
	.INITVAL_59($sformatf("0x%01280x", init_slice('h59))),
	.INITVAL_5A($sformatf("0x%01280x", init_slice('h5a))),
	.INITVAL_5B($sformatf("0x%01280x", init_slice('h5b))),
	.INITVAL_5C($sformatf("0x%01280x", init_slice('h5c))),
	.INITVAL_5D($sformatf("0x%01280x", init_slice('h5d))),
	.INITVAL_5E($sformatf("0x%01280x", init_slice('h5e))),
	.INITVAL_5F($sformatf("0x%01280x", init_slice('h5f))),
	.INITVAL_60($sformatf("0x%01280x", init_slice('h60))),
	.INITVAL_61($sformatf("0x%01280x", init_slice('h61))),
	.INITVAL_62($sformatf("0x%01280x", init_slice('h62))),
	.INITVAL_63($sformatf("0x%01280x", init_slice('h63))),
	.INITVAL_64($sformatf("0x%01280x", init_slice('h64))),
	.INITVAL_65($sformatf("0x%01280x", init_slice('h65))),
	.INITVAL_66($sformatf("0x%01280x", init_slice('h66))),
	.INITVAL_67($sformatf("0x%01280x", init_slice('h67))),
	.INITVAL_68($sformatf("0x%01280x", init_slice('h68))),
	.INITVAL_69($sformatf("0x%01280x", init_slice('h69))),
	.INITVAL_6A($sformatf("0x%01280x", init_slice('h6a))),
	.INITVAL_6B($sformatf("0x%01280x", init_slice('h6b))),
	.INITVAL_6C($sformatf("0x%01280x", init_slice('h6c))),
	.INITVAL_6D($sformatf("0x%01280x", init_slice('h6d))),
	.INITVAL_6E($sformatf("0x%01280x", init_slice('h6e))),
	.INITVAL_6F($sformatf("0x%01280x", init_slice('h6f))),
	.INITVAL_70($sformatf("0x%01280x", init_slice('h70))),
	.INITVAL_71($sformatf("0x%01280x", init_slice('h71))),
	.INITVAL_72($sformatf("0x%01280x", init_slice('h72))),
	.INITVAL_73($sformatf("0x%01280x", init_slice('h73))),
	.INITVAL_74($sformatf("0x%01280x", init_slice('h74))),
	.INITVAL_75($sformatf("0x%01280x", init_slice('h75))),
	.INITVAL_76($sformatf("0x%01280x", init_slice('h76))),
	.INITVAL_77($sformatf("0x%01280x", init_slice('h77))),
	.INITVAL_78($sformatf("0x%01280x", init_slice('h78))),
	.INITVAL_79($sformatf("0x%01280x", init_slice('h79))),
	.INITVAL_7A($sformatf("0x%01280x", init_slice('h7a))),
	.INITVAL_7B($sformatf("0x%01280x", init_slice('h7b))),
	.INITVAL_7C($sformatf("0x%01280x", init_slice('h7c))),
	.INITVAL_7D($sformatf("0x%01280x", init_slice('h7d))),
	.INITVAL_7E($sformatf("0x%01280x", init_slice('h7e))),
	.INITVAL_7F($sformatf("0x%01280x", init_slice('h7f))),
	.OUTREG_A("NO_REG"),
	.OUTREG_B("NO_REG"),
	.ECC_BYTE_SEL("BYTE_EN"),
	.GSR("DISABLED"),
	.RESETMODE(OPTION_RESETMODE),
	.ASYNC_RESET_RELEASE(OPTION_RESETMODE),
) _TECHMAP_REPLACE_ (
	.CLK(CLK_C),

	.WEA(PORT_A_WR_EN),
	.CEA(PORT_A_CLK_EN),
	.RSTA(OPTION_RESETMODE == "SYNC" ? PORT_A_RD_SRST : PORT_A_RD_ARST),
	.CSA(1'b1),
	.ADA(PORT_A_ADDR),
	.BENA_N(~PORT_A_WR_BE),
	.DIA(PORT_A_WR_DATA),
	.DOA(PORT_A_RD_DATA),

	.WEB(PORT_B_WR_EN),
	.CEB(PORT_B_CLK_EN),
	.RSTB(OPTION_RESETMODE == "SYNC" ? PORT_B_RD_SRST : PORT_B_RD_ARST),
	.CSB(1'b1),
	.BENB_N(~PORT_B_WR_BE),
	.ADB(PORT_B_ADDR),
	.DIB(PORT_B_WR_DATA),
	.DOB(PORT_B_RD_DATA),
);

endmodule
