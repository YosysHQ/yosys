module $__XILINX_BLOCKRAM_ (...);

parameter INIT = 0;
parameter OPTION_USE_BE = 0;

parameter PORT_A_WIDTH = 1;
parameter PORT_A_WR_EN_WIDTH = 1;
parameter PORT_A_USED = 1;
parameter PORT_A_OPTION_WRITE_MODE = "NO_CHANGE";
parameter PORT_A_RD_INIT_VALUE = 0;
parameter PORT_A_RD_SRST_VALUE = 0;

parameter PORT_B_WIDTH = 1;
parameter PORT_B_WR_EN_WIDTH = 1;
parameter PORT_B_USED = 0;
parameter PORT_B_OPTION_WRITE_MODE = "NO_CHANGE";
parameter PORT_B_RD_INIT_VALUE = 0;
parameter PORT_B_RD_SRST_VALUE = 0;

input PORT_A_CLK;
input PORT_A_CLK_EN;
input [13:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
input [PORT_A_WR_EN_WIDTH-1:0] PORT_A_WR_EN;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;
input PORT_A_RD_SRST;

input PORT_B_CLK;
input PORT_B_CLK_EN;
input [13:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
input [PORT_B_WR_EN_WIDTH-1:0] PORT_B_WR_EN;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;
input PORT_B_RD_SRST;

`include "brams_defs.vh"

`define PARAMS_DP \
	`PARAMS_INIT_18 \
	.WRITE_MODE_A(PORT_A_OPTION_WRITE_MODE), \
	.WRITE_MODE_B(PORT_B_OPTION_WRITE_MODE), \
	.SRVAL_A(SRVAL_A), \
	.SRVAL_B(SRVAL_B), \
	.INIT_A(INIT_A), \
	.INIT_B(INIT_B),

`define PARAMS_DP_SWAP \
	`PARAMS_INIT_18 \
	.WRITE_MODE_A(PORT_B_OPTION_WRITE_MODE), \
	.WRITE_MODE_B(PORT_A_OPTION_WRITE_MODE), \
	.SRVAL_A(SRVAL_B), \
	.SRVAL_B(SRVAL_A), \
	.INIT_A(INIT_B), \
	.INIT_B(INIT_A),

`define PARAMS_SP \
	`PARAMS_INIT_18 \
	.WRITE_MODE(PORT_A_OPTION_WRITE_MODE), \
	.SRVAL(SRVAL_A), \
	.INIT(INIT_A),

`define PORTS_DP(addr_slice_a, addr_slice_b) \
	.CLKA(PORT_A_CLK), \
	.ENA(PORT_A_CLK_EN), \
	.WEA(PORT_A_WR_EN), \
	.SSRA(PORT_A_RD_SRST), \
	.ADDRA(PORT_A_ADDR addr_slice_a), \
	.DOA(DO_A), \
	.DIA(DI_A), \
	.CLKB(PORT_B_CLK), \
	.ENB(PORT_B_CLK_EN), \
	.WEB(PORT_B_WR_EN), \
	.SSRB(PORT_B_RD_SRST), \
	.ADDRB(PORT_B_ADDR addr_slice_b), \
	.DOB(DO_B), \
	.DIB(DI_B),

`define PORTS_DP_SWAP(addr_slice_a, addr_slice_b) \
	.CLKB(PORT_A_CLK), \
	.ENB(PORT_A_CLK_EN), \
	.WEB(PORT_A_WR_EN), \
	.SSRB(PORT_A_RD_SRST), \
	.ADDRB(PORT_A_ADDR addr_slice_a), \
	.DOB(DO_A), \
	.DIB(DI_A), \
	.CLKA(PORT_B_CLK), \
	.ENA(PORT_B_CLK_EN), \
	.WEA(PORT_B_WR_EN), \
	.SSRA(PORT_B_RD_SRST), \
	.ADDRA(PORT_B_ADDR addr_slice_b), \
	.DOA(DO_B), \
	.DIA(DI_B),

`define PORTS_SP(addr_slice) \
	.CLK(PORT_A_CLK), \
	.EN(PORT_A_CLK_EN), \
	.WE(PORT_A_WR_EN), \
	.SSR(PORT_A_RD_SRST), \
	.ADDR(PORT_A_ADDR addr_slice), \
	.DO(DO_A), \
	.DI(DI_A),

localparam [PORT_A_WIDTH-1:0] SRVAL_A = ival(PORT_A_WIDTH, PORT_A_RD_SRST_VALUE);
localparam [PORT_B_WIDTH-1:0] SRVAL_B = ival(PORT_B_WIDTH, PORT_B_RD_SRST_VALUE);
localparam [PORT_A_WIDTH-1:0] INIT_A = ival(PORT_A_WIDTH, PORT_A_RD_INIT_VALUE);
localparam [PORT_B_WIDTH-1:0] INIT_B = ival(PORT_B_WIDTH, PORT_B_RD_INIT_VALUE);

`MAKE_DI(DI_A, DIP_A, PORT_A_WR_DATA)
`MAKE_DI(DI_B, DIP_B, PORT_B_WR_DATA)
`MAKE_DO(DO_A, DOP_A, PORT_A_RD_DATA)
`MAKE_DO(DO_B, DOP_B, PORT_B_RD_DATA)

generate

if (OPTION_USE_BE) begin
	if (!PORT_B_USED) begin
		case (PORT_A_WIDTH)
		9: RAMB16_S9 #(
			`PARAMS_SP
			`PARAMS_INITP_18
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:3])
			.DIP(DIP_A),
			.DOP(DOP_A),
		);
		18: RAMB16BWE_S18 #(
			`PARAMS_SP
			`PARAMS_INITP_18
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:4])
			.DIP(DIP_A),
			.DOP(DOP_A),
		);
		36: RAMB16BWE_S36 #(
			`PARAMS_SP
			`PARAMS_INITP_18
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:5])
			.DIP(DIP_A),
			.DOP(DOP_A),
		);
		endcase
	end else begin
		case (PORT_A_WIDTH)
		9:	case(PORT_B_WIDTH)
			9: RAMB16_S9_S9 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:3], [13:3])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			18: RAMB16BWE_S9_S18 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:3], [13:4])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			36: RAMB16BWE_S9_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:3], [13:5])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		18:	case(PORT_B_WIDTH)
			9: RAMB16BWE_S9_S18 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:4], [13:3])
				.DIPA(DIP_B), .DOPA(DOP_B),
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			18: RAMB16BWE_S18_S18 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:4], [13:4])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			36: RAMB16BWE_S18_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:4], [13:5])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		36:	case(PORT_B_WIDTH)
			9: RAMB16BWE_S9_S36 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:5], [13:3])
				.DIPA(DIP_B), .DOPA(DOP_B),
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			18: RAMB16BWE_S18_S36 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:5], [13:4])
				.DIPA(DIP_B), .DOPA(DOP_B),
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			36: RAMB16BWE_S36_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:5], [13:5])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		endcase
	end
end else begin
	if (!PORT_B_USED) begin
		case (PORT_A_WIDTH)
		1: RAMB16_S1 #(
			`PARAMS_SP
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:0])
		);
		2: RAMB16_S2 #(
			`PARAMS_SP
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:1])
		);
		4: RAMB16_S4 #(
			`PARAMS_SP
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:2])
		);
		9: RAMB16_S9 #(
			`PARAMS_SP
			`PARAMS_INITP_18
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:3])
			.DIP(DIP_A),
			.DOP(DOP_A),
		);
		18: RAMB16_S18 #(
			`PARAMS_SP
			`PARAMS_INITP_18
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:4])
			.DIP(DIP_A),
			.DOP(DOP_A),
		);
		36: RAMB16_S36 #(
			`PARAMS_SP
			`PARAMS_INITP_18
		) _TECHMAP_REPLACE_ (
			`PORTS_SP([13:5])
			.DIP(DIP_A),
			.DOP(DOP_A),
		);
		endcase
	end else begin
		case (PORT_A_WIDTH)
		1:	case(PORT_B_WIDTH)
			1: RAMB16_S1_S1 #(
				`PARAMS_DP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:0], [13:0])
			);
			2: RAMB16_S1_S2 #(
				`PARAMS_DP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:0], [13:1])
			);
			4: RAMB16_S1_S4 #(
				`PARAMS_DP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:0], [13:2])
			);
			9: RAMB16_S1_S9 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:0], [13:3])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			18: RAMB16_S1_S18 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:0], [13:4])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			36: RAMB16_S1_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:0], [13:5])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		2:	case(PORT_B_WIDTH)
			1: RAMB16_S1_S2 #(
				`PARAMS_DP_SWAP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:1], [13:0])
			);
			2: RAMB16_S2_S2 #(
				`PARAMS_DP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:1], [13:1])
			);
			4: RAMB16_S2_S4 #(
				`PARAMS_DP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:1], [13:2])
			);
			9: RAMB16_S2_S9 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:1], [13:3])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			18: RAMB16_S2_S18 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:1], [13:4])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			36: RAMB16_S2_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:1], [13:5])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		4:	case(PORT_B_WIDTH)
			1: RAMB16_S1_S4 #(
				`PARAMS_DP_SWAP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:2], [13:0])
			);
			2: RAMB16_S2_S4 #(
				`PARAMS_DP_SWAP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:2], [13:1])
			);
			4: RAMB16_S4_S4 #(
				`PARAMS_DP
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:2], [13:2])
			);
			9: RAMB16_S4_S9 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:2], [13:3])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			18: RAMB16_S4_S18 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:2], [13:4])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			36: RAMB16_S4_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:2], [13:5])
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		9:	case(PORT_B_WIDTH)
			1: RAMB16_S1_S9 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:3], [13:0])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			2: RAMB16_S2_S9 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:3], [13:1])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			4: RAMB16_S4_S9 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:3], [13:2])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			9: RAMB16_S9_S9 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:3], [13:3])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			18: RAMB16_S9_S18 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:3], [13:4])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			36: RAMB16_S9_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:3], [13:5])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		18:	case(PORT_B_WIDTH)
			1: RAMB16_S1_S18 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:4], [13:0])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			2: RAMB16_S2_S18 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:4], [13:1])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			4: RAMB16_S4_S18 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:4], [13:2])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			9: RAMB16_S9_S18 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:4], [13:3])
				.DIPA(DIP_B), .DOPA(DOP_B),
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			18: RAMB16_S18_S18 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:4], [13:4])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			36: RAMB16_S18_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:4], [13:5])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		36:	case(PORT_B_WIDTH)
			1: RAMB16_S1_S36 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:5], [13:0])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			2: RAMB16_S2_S36 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:5], [13:1])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			4: RAMB16_S4_S36 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:5], [13:2])
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			9: RAMB16_S9_S36 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:5], [13:3])
				.DIPA(DIP_B), .DOPA(DOP_B),
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			18: RAMB16_S18_S36 #(
				`PARAMS_DP_SWAP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP_SWAP([13:5], [13:4])
				.DIPA(DIP_B), .DOPA(DOP_B),
				.DIPB(DIP_A), .DOPB(DOP_A),
			);
			36: RAMB16_S36_S36 #(
				`PARAMS_DP
				`PARAMS_INITP_18
			) _TECHMAP_REPLACE_ (
				`PORTS_DP([13:5], [13:5])
				.DIPA(DIP_A), .DOPA(DOP_A),
				.DIPB(DIP_B), .DOPB(DOP_B),
			);
			endcase
		endcase
	end
end

endgenerate


endmodule
