module $__GOWIN_LUTRAM_(...);

parameter INIT = 64'bx;
parameter BITS_USED = 0;

input PORT_W_CLK;
input [3:0] PORT_W_ADDR;
input PORT_W_WR_EN;
input [3:0] PORT_W_WR_DATA;

input [3:0] PORT_R_ADDR;
output [3:0] PORT_R_RD_DATA;

function [15:0] init_slice;
input integer idx;
integer i;
for (i = 0; i < 16; i = i + 1)
	init_slice[i] = INIT[4*i+idx];
endfunction

generate

casez(BITS_USED)
4'b000z:
RAM16SDP1 #(
	.INIT_0(init_slice(0)),
) _TECHMAP_REPLACE_ (
	.WAD(PORT_W_ADDR),
	.RAD(PORT_R_ADDR),
	.DI(PORT_W_WR_DATA[0]),
	.DO(PORT_R_RD_DATA[0]),
	.CLK(PORT_W_CLK),
	.WRE(PORT_W_WR_EN)
);
4'b00zz:
RAM16SDP2 #(
	.INIT_0(init_slice(0)),
	.INIT_1(init_slice(1)),
) _TECHMAP_REPLACE_ (
	.WAD(PORT_W_ADDR),
	.RAD(PORT_R_ADDR),
	.DI(PORT_W_WR_DATA[1:0]),
	.DO(PORT_R_RD_DATA[1:0]),
	.CLK(PORT_W_CLK),
	.WRE(PORT_W_WR_EN)
);
default:
RAM16SDP4 #(
	.INIT_0(init_slice(0)),
	.INIT_1(init_slice(1)),
	.INIT_2(init_slice(2)),
	.INIT_3(init_slice(3)),
) _TECHMAP_REPLACE_ (
	.WAD(PORT_W_ADDR),
	.RAD(PORT_R_ADDR),
	.DI(PORT_W_WR_DATA),
	.DO(PORT_R_RD_DATA),
	.CLK(PORT_W_CLK),
	.WRE(PORT_W_WR_EN)
);
endcase

endgenerate

endmodule
