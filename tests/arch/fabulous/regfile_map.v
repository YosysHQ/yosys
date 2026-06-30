(* techmap_celltype = "$__REGFILE_[AS][AS]_" *)
module \$__REGFILE_XX_ (...);

parameter _TECHMAP_CELLTYPE_ = "";
localparam [0:0] B_SYNC = _TECHMAP_CELLTYPE_[15:8] == "S";
localparam [0:0] A_SYNC = _TECHMAP_CELLTYPE_[23:16] == "S";

localparam WIDTH = 4;
localparam ABITS = 5;

input [WIDTH-1:0] PORT_W_WR_DATA;
input [ABITS-1:0] PORT_W_ADDR;
input PORT_W_WR_EN;

output [WIDTH-1:0] PORT_A_RD_DATA;
input [ABITS-1:0] PORT_A_ADDR;

output [WIDTH-1:0] PORT_B_RD_DATA;
input [ABITS-1:0] PORT_B_ADDR;

// Unused - we have a shared clock - but keep techmap happy
input PORT_W_CLK;
input PORT_A_CLK;
input PORT_B_CLK;

input CLK_CLK;

RegFile_32x4 #(
	.AD_reg(A_SYNC),
	.BD_reg(B_SYNC)
) _TECHMAP_REPLACE_ (
	.D0(PORT_W_WR_DATA[0]), .D1(PORT_W_WR_DATA[1]), .D2(PORT_W_WR_DATA[2]), .D3(PORT_W_WR_DATA[3]),
	.W_ADR0(PORT_W_ADDR[0]), .W_ADR1(PORT_W_ADDR[1]), .W_ADR2(PORT_W_ADDR[2]), .W_ADR3(PORT_W_ADDR[3]), .W_ADR4(PORT_W_ADDR[4]),
	.W_en(PORT_W_WR_EN),
	.AD0(PORT_A_RD_DATA[0]), .AD1(PORT_A_RD_DATA[1]), .AD2(PORT_A_RD_DATA[2]), .AD3(PORT_A_RD_DATA[3]),
	.A_ADR0(PORT_A_ADDR[0]), .A_ADR1(PORT_A_ADDR[1]), .A_ADR2(PORT_A_ADDR[2]), .A_ADR3(PORT_A_ADDR[3]), .A_ADR4(PORT_A_ADDR[4]),
	.BD0(PORT_B_RD_DATA[0]), .BD1(PORT_B_RD_DATA[1]), .BD2(PORT_B_RD_DATA[2]), .BD3(PORT_B_RD_DATA[3]),
	.B_ADR0(PORT_B_ADDR[0]), .B_ADR1(PORT_B_ADDR[1]), .B_ADR2(PORT_B_ADDR[2]), .B_ADR3(PORT_B_ADDR[3]), .B_ADR4(PORT_B_ADDR[4]),
	.CLK(CLK_CLK)
);

endmodule
