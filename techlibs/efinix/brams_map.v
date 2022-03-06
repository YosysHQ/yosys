module $__EFINIX_5K_ (...);
	parameter INIT = 0;
	parameter OPTION_WRITE_MODE = "READ_FIRST";

	parameter PORT_R_WIDTH = 20;
	parameter PORT_R_CLK_POL = 1;
	parameter PORT_W_WIDTH = 20;
	parameter PORT_W_CLK_POL = 1;

	input PORT_R_CLK;
	input PORT_R_RD_EN;
	input [11:0] PORT_R_ADDR;
	output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;

	input PORT_W_CLK;
	input PORT_W_WR_EN;
	input [11:0] PORT_W_ADDR;
	input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;

	localparam IS_5BIT = PORT_R_WIDTH >= 5 && PORT_W_WIDTH >= 5;

	localparam RADDR_WIDTH =
		PORT_R_WIDTH == 1 ? 12 :
		PORT_R_WIDTH == 2 ? 11 :
		PORT_R_WIDTH == 5 ? 10 :
		PORT_R_WIDTH == 10 ? 9 :
		8;

	localparam WADDR_WIDTH =
		PORT_W_WIDTH == 1 ? 12 :
		PORT_W_WIDTH == 2 ? 11 :
		PORT_W_WIDTH == 5 ? 10 :
		PORT_W_WIDTH == 10 ? 9 :
		8;

	localparam READ_WIDTH = 
		PORT_R_WIDTH == 1 ? 1 :
		PORT_R_WIDTH == 2 ? 2 :
		PORT_R_WIDTH == 5 ? (IS_5BIT ? 5 : 4) :
		PORT_R_WIDTH == 10 ? (IS_5BIT ? 10 : 8) :
		(IS_5BIT ? 20 : 16);

	localparam WRITE_WIDTH = 
		PORT_W_WIDTH == 1 ? 1 :
		PORT_W_WIDTH == 2 ? 2 :
		PORT_W_WIDTH == 5 ? (IS_5BIT ? 5 : 4) :
		PORT_W_WIDTH == 10 ? (IS_5BIT ? 10 : 8) :
		(IS_5BIT ? 20 : 16);

	wire [RADDR_WIDTH-1:0] RADDR = PORT_R_ADDR[11:12-RADDR_WIDTH];
	wire [WADDR_WIDTH-1:0] WADDR = PORT_W_ADDR[11:12-WADDR_WIDTH];

	wire [WRITE_WIDTH-1:0] WDATA;
	wire [READ_WIDTH-1:0] RDATA;

	generate
		case (WRITE_WIDTH)
		1:	assign WDATA = PORT_W_WR_DATA;
		2:	assign WDATA = PORT_W_WR_DATA;
		4:	assign WDATA = PORT_W_WR_DATA[3:0];
		5:	assign WDATA = PORT_W_WR_DATA;
		8:	assign WDATA = {
			PORT_W_WR_DATA[8:5],
			PORT_W_WR_DATA[3:0]
		};
		10:	assign WDATA = PORT_W_WR_DATA;
		16:	assign WDATA = {
			PORT_W_WR_DATA[18:15],
			PORT_W_WR_DATA[13:10],
			PORT_W_WR_DATA[8:5],
			PORT_W_WR_DATA[3:0]
		};
		20:	assign WDATA = PORT_W_WR_DATA;
		endcase
		case (READ_WIDTH)
		1:	assign PORT_R_RD_DATA = RDATA;
		2:	assign PORT_R_RD_DATA = RDATA;
		4:	assign PORT_R_RD_DATA[3:0] = RDATA;
		5:	assign PORT_R_RD_DATA = RDATA;
		8:	assign {
			PORT_R_RD_DATA[8:5],
			PORT_R_RD_DATA[3:0]
		} = RDATA;
		10:	assign PORT_R_RD_DATA = RDATA;
		16:	assign {
			PORT_R_RD_DATA[18:15],
			PORT_R_RD_DATA[13:10],
			PORT_R_RD_DATA[8:5],
			PORT_R_RD_DATA[3:0]
		} = RDATA;
		20:	assign PORT_R_RD_DATA = RDATA;
		endcase
	endgenerate

	function [255:0] init_slice;
		input integer idx;
		integer i;
		if (IS_5BIT)
			init_slice = INIT[idx * 256 +: 256];
		else if (idx > 16)
			init_slice = 0;
		else
			for (i = 0; i < 64; i = i + 1)
				init_slice[i*4+:4] = INIT[(idx * 64 + i) * 5+:4];
	endfunction

	EFX_RAM_5K #(
		.READ_WIDTH(READ_WIDTH),
		.WRITE_WIDTH(WRITE_WIDTH),
		.OUTPUT_REG(1'b0),
		.RCLK_POLARITY(PORT_R_CLK_POL),
		.RE_POLARITY(1'b1),
		.WCLK_POLARITY(PORT_W_CLK_POL),
		.WE_POLARITY(1'b1),
		.WCLKE_POLARITY(1'b1),
		.WRITE_MODE(OPTION_WRITE_MODE),
		.INIT_0(init_slice('h00)),
		.INIT_1(init_slice('h01)),
		.INIT_2(init_slice('h02)),
		.INIT_3(init_slice('h03)),
		.INIT_4(init_slice('h04)),
		.INIT_5(init_slice('h05)),
		.INIT_6(init_slice('h06)),
		.INIT_7(init_slice('h07)),
		.INIT_8(init_slice('h08)),
		.INIT_9(init_slice('h09)),
		.INIT_A(init_slice('h0a)),
		.INIT_B(init_slice('h0b)),
		.INIT_C(init_slice('h0c)),
		.INIT_D(init_slice('h0d)),
		.INIT_E(init_slice('h0e)),
		.INIT_F(init_slice('h0f)),
		.INIT_10(init_slice('h10)),
		.INIT_11(init_slice('h11)),
		.INIT_12(init_slice('h12)),
		.INIT_13(init_slice('h13)),
	) _TECHMAP_REPLACE_ (
		.WDATA(WDATA),
		.WADDR(WADDR),
		.WE(PORT_W_WR_EN),
		.WCLK(PORT_W_CLK),
		.WCLKE(1'b1),
		.RDATA(RDATA),
		.RADDR(RADDR),
		.RE(PORT_R_RD_EN),
		.RCLK(PORT_R_CLK)
	);

endmodule
