module $__XILINX_BLOCKRAM_ (...);

parameter INIT = 0;

parameter PORT_A_WIDTH = 1;
parameter PORT_B_WIDTH = 1;
parameter PORT_A_USED = 1;
parameter PORT_B_USED = 0;

input PORT_A_CLK;
input PORT_A_CLK_EN;
input [11:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
input PORT_A_WR_EN;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;
input PORT_A_RD_SRST;

input PORT_B_CLK;
input PORT_B_CLK_EN;
input [11:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
input PORT_B_WR_EN;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;
input PORT_B_RD_SRST;

`define PARAMS_INIT \
	.INIT_00(INIT[0*256+:256]), \
	.INIT_01(INIT[1*256+:256]), \
	.INIT_02(INIT[2*256+:256]), \
	.INIT_03(INIT[3*256+:256]), \
	.INIT_04(INIT[4*256+:256]), \
	.INIT_05(INIT[5*256+:256]), \
	.INIT_06(INIT[6*256+:256]), \
	.INIT_07(INIT[7*256+:256]), \
	.INIT_08(INIT[8*256+:256]), \
	.INIT_09(INIT[9*256+:256]), \
	.INIT_0A(INIT[10*256+:256]), \
	.INIT_0B(INIT[11*256+:256]), \
	.INIT_0C(INIT[12*256+:256]), \
	.INIT_0D(INIT[13*256+:256]), \
	.INIT_0E(INIT[14*256+:256]), \
	.INIT_0F(INIT[15*256+:256]),

`define PORTS_DP(addr_slice_a, addr_slice_b) \
	.CLKA(PORT_A_CLK), \
	.ENA(PORT_A_CLK_EN), \
	.WEA(PORT_A_WR_EN), \
	.RSTA(PORT_A_RD_SRST), \
	.ADDRA(PORT_A_ADDR addr_slice_a), \
	.DOA(PORT_A_RD_DATA), \
	.DIA(PORT_A_WR_DATA), \
	.CLKB(PORT_B_CLK), \
	.ENB(PORT_B_CLK_EN), \
	.WEB(PORT_B_WR_EN), \
	.RSTB(PORT_B_RD_SRST), \
	.ADDRB(PORT_B_ADDR addr_slice_b), \
	.DOB(PORT_B_RD_DATA), \
	.DIB(PORT_B_WR_DATA),

`define PORTS_DP_SWAP(addr_slice_a, addr_slice_b) \
	.CLKB(PORT_A_CLK), \
	.ENB(PORT_A_CLK_EN), \
	.WEB(PORT_A_WR_EN), \
	.RSTB(PORT_A_RD_SRST), \
	.ADDRB(PORT_A_ADDR addr_slice_a), \
	.DOB(PORT_A_RD_DATA), \
	.DIB(PORT_A_WR_DATA), \
	.CLKA(PORT_B_CLK), \
	.ENA(PORT_B_CLK_EN), \
	.WEA(PORT_B_WR_EN), \
	.RSTA(PORT_B_RD_SRST), \
	.ADDRA(PORT_B_ADDR addr_slice_b), \
	.DOA(PORT_B_RD_DATA), \
	.DIA(PORT_B_WR_DATA),

`define PORTS_SP(addr_slice) \
	.CLK(PORT_A_CLK), \
	.EN(PORT_A_CLK_EN), \
	.WE(PORT_A_WR_EN), \
	.RST(PORT_A_RD_SRST), \
	.ADDR(PORT_A_ADDR addr_slice), \
	.DO(PORT_A_RD_DATA), \
	.DI(PORT_A_WR_DATA),

generate

if (!PORT_B_USED) begin
	case (PORT_A_WIDTH)
	1: RAMB4_S1 #(
		`PARAMS_INIT
	) _TECHMAP_REPLACE_ (
		`PORTS_SP([11:0])
	);
	2: RAMB4_S2 #(
		`PARAMS_INIT
	) _TECHMAP_REPLACE_ (
		`PORTS_SP([11:1])
	);
	4: RAMB4_S4 #(
		`PARAMS_INIT
	) _TECHMAP_REPLACE_ (
		`PORTS_SP([11:2])
	);
	8: RAMB4_S8 #(
		`PARAMS_INIT
	) _TECHMAP_REPLACE_ (
		`PORTS_SP([11:3])
	);
	16: RAMB4_S16 #(
		`PARAMS_INIT
	) _TECHMAP_REPLACE_ (
		`PORTS_SP([11:4])
	);
	endcase
end else begin
	case (PORT_A_WIDTH)
	1:	case(PORT_B_WIDTH)
		1: RAMB4_S1_S1 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:0], [11:0])
		);
		2: RAMB4_S1_S2 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:0], [11:1])
		);
		4: RAMB4_S1_S4 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:0], [11:2])
		);
		8: RAMB4_S1_S8 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:0], [11:3])
		);
		16: RAMB4_S1_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:0], [11:4])
		);
		endcase
	2:	case(PORT_B_WIDTH)
		1: RAMB4_S1_S2 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:1], [11:0])
		);
		2: RAMB4_S2_S2 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:1], [11:1])
		);
		4: RAMB4_S2_S4 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:1], [11:2])
		);
		8: RAMB4_S2_S8 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:1], [11:3])
		);
		16: RAMB4_S2_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:1], [11:4])
		);
		endcase
	4:	case(PORT_B_WIDTH)
		1: RAMB4_S1_S4 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:2], [11:0])
		);
		2: RAMB4_S2_S4 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:2], [11:1])
		);
		4: RAMB4_S4_S4 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:2], [11:2])
		);
		8: RAMB4_S4_S8 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:2], [11:3])
		);
		16: RAMB4_S4_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:2], [11:4])
		);
		endcase
	8:	case(PORT_B_WIDTH)
		1: RAMB4_S1_S8 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:3], [11:0])
		);
		2: RAMB4_S2_S8 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:3], [11:1])
		);
		4: RAMB4_S4_S8 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:3], [11:2])
		);
		8: RAMB4_S8_S8 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:3], [11:3])
		);
		16: RAMB4_S8_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:3], [11:4])
		);
		endcase
	16:	case(PORT_B_WIDTH)
		1: RAMB4_S1_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:4], [11:0])
		);
		2: RAMB4_S2_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:4], [11:1])
		);
		4: RAMB4_S4_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:4], [11:2])
		);
		8: RAMB4_S8_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP_SWAP([11:4], [11:3])
		);
		16: RAMB4_S16_S16 #(
			`PARAMS_INIT
		) _TECHMAP_REPLACE_ (
			`PORTS_DP([11:4], [11:4])
		);
		endcase
	endcase
end

endgenerate

endmodule
