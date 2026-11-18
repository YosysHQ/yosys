module $__ICE40_RAM4K_ (...);

parameter INIT = 0;
parameter OPTION_HAS_BE = 1;
parameter PORT_R_WIDTH = 16;
parameter PORT_W_WIDTH = 16;
parameter PORT_W_WR_BE_WIDTH = 16;
parameter PORT_R_CLK_POL = 1;
parameter PORT_W_CLK_POL = 1;

input PORT_R_CLK;
input PORT_R_RD_EN;
input [10:0] PORT_R_ADDR;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;

input PORT_W_CLK;
input PORT_W_WR_EN;
input [15:0] PORT_W_WR_BE;
input [10:0] PORT_W_ADDR;
input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;

wire [15:0] RDATA;
wire [15:0] WDATA;
wire [15:0] MASK;
wire [10:0] RADDR = {PORT_R_ADDR[0], PORT_R_ADDR[1], PORT_R_ADDR[2], PORT_R_ADDR[10:3]};
wire [10:0] WADDR = {PORT_W_ADDR[0], PORT_W_ADDR[1], PORT_W_ADDR[2], PORT_W_ADDR[10:3]};

function [1:0] mode;
	input integer width;
	case (width)
	16: mode = 0;
	8: mode = 1;
	4: mode = 2;
	2: mode = 3;
	endcase
endfunction

// INIT_P[idx*256 +: 256] equals what slice_init(idx) used to return.
// Bit reversal of the 4-bit position inside every 16-bit group, done as two
// delta swaps (index bits 0<->3, then 1<->2) on the whole 4096-bit vector.
localparam [4095:0] INIT_X0 = INIT;
localparam [4095:0] INIT_T1 = ((INIT_X0 >> 7) ^ INIT_X0) & {256{16'h00AA}};
localparam [4095:0] INIT_X1 = INIT_X0 ^ INIT_T1 ^ (INIT_T1 << 7);
localparam [4095:0] INIT_T2 = ((INIT_X1 >> 2) ^ INIT_X1) & {256{16'h0C0C}};
localparam [4095:0] INIT_P  = INIT_X1 ^ INIT_T2 ^ (INIT_T2 << 2);

`define INSTANCE(type, rclk, wclk) \
	type #( \
		.INIT_0(INIT_P[255:0]), \
		.INIT_1(INIT_P[511:256]), \
		.INIT_2(INIT_P[767:512]), \
		.INIT_3(INIT_P[1023:768]), \
		.INIT_4(INIT_P[1279:1024]), \
		.INIT_5(INIT_P[1535:1280]), \
		.INIT_6(INIT_P[1791:1536]), \
		.INIT_7(INIT_P[2047:1792]), \
		.INIT_8(INIT_P[2303:2048]), \
		.INIT_9(INIT_P[2559:2304]), \
		.INIT_A(INIT_P[2815:2560]), \
		.INIT_B(INIT_P[3071:2816]), \
		.INIT_C(INIT_P[3327:3072]), \
		.INIT_D(INIT_P[3583:3328]), \
		.INIT_E(INIT_P[3839:3584]), \
		.INIT_F(INIT_P[4095:3840]), \
		.READ_MODE(mode(PORT_R_WIDTH)), \
		.WRITE_MODE(mode(PORT_W_WIDTH)) \
	) _TECHMAP_REPLACE_ ( \
		.RDATA(RDATA), \
		.rclk(PORT_R_CLK), \
		.RCLKE(PORT_R_RD_EN), \
		.RE(1'b1), \
		.RADDR(RADDR), \
		.WDATA(WDATA), \
		.wclk(PORT_W_CLK), \
		.WCLKE(PORT_W_WR_EN), \
		.WE(1'b1), \
		.WADDR(WADDR), \
		.MASK(MASK), \
	);

generate

case(PORT_R_WIDTH)
	2: begin
		assign PORT_R_RD_DATA = {
			RDATA[11],
			RDATA[3]
		};
	end
	4: begin
		assign PORT_R_RD_DATA = {
			RDATA[13],
			RDATA[5],
			RDATA[9],
			RDATA[1]
		};
	end
	8: begin
		assign PORT_R_RD_DATA = {
			RDATA[14],
			RDATA[6],
			RDATA[10],
			RDATA[2],
			RDATA[12],
			RDATA[4],
			RDATA[8],
			RDATA[0]
		};
	end
	16: begin
		assign PORT_R_RD_DATA = {
			RDATA[15],
			RDATA[7],
			RDATA[11],
			RDATA[3],
			RDATA[13],
			RDATA[5],
			RDATA[9],
			RDATA[1],
			RDATA[14],
			RDATA[6],
			RDATA[10],
			RDATA[2],
			RDATA[12],
			RDATA[4],
			RDATA[8],
			RDATA[0]
		};
	end
endcase

case(PORT_W_WIDTH)
	2: begin
		assign {
			WDATA[11],
			WDATA[3]
		} = PORT_W_WR_DATA;
	end
	4: begin
		assign {
			WDATA[13],
			WDATA[5],
			WDATA[9],
			WDATA[1]
		} = PORT_W_WR_DATA;
	end
	8: begin
		assign {
			WDATA[14],
			WDATA[6],
			WDATA[10],
			WDATA[2],
			WDATA[12],
			WDATA[4],
			WDATA[8],
			WDATA[0]
		} = PORT_W_WR_DATA;
	end
	16: begin
		assign WDATA = {
			PORT_W_WR_DATA[15],
			PORT_W_WR_DATA[7],
			PORT_W_WR_DATA[11],
			PORT_W_WR_DATA[3],
			PORT_W_WR_DATA[13],
			PORT_W_WR_DATA[5],
			PORT_W_WR_DATA[9],
			PORT_W_WR_DATA[1],
			PORT_W_WR_DATA[14],
			PORT_W_WR_DATA[6],
			PORT_W_WR_DATA[10],
			PORT_W_WR_DATA[2],
			PORT_W_WR_DATA[12],
			PORT_W_WR_DATA[4],
			PORT_W_WR_DATA[8],
			PORT_W_WR_DATA[0]
		};
		assign MASK = ~{
			PORT_W_WR_BE[15],
			PORT_W_WR_BE[7],
			PORT_W_WR_BE[11],
			PORT_W_WR_BE[3],
			PORT_W_WR_BE[13],
			PORT_W_WR_BE[5],
			PORT_W_WR_BE[9],
			PORT_W_WR_BE[1],
			PORT_W_WR_BE[14],
			PORT_W_WR_BE[6],
			PORT_W_WR_BE[10],
			PORT_W_WR_BE[2],
			PORT_W_WR_BE[12],
			PORT_W_WR_BE[4],
			PORT_W_WR_BE[8],
			PORT_W_WR_BE[0]
		};
	end
endcase

if (PORT_R_CLK_POL) begin
	if (PORT_W_CLK_POL) begin
		`INSTANCE(SB_RAM40_4K, RCLK, WCLK)
	end else begin
		`INSTANCE(SB_RAM40_4KNW, RCLK, WCLKN)
	end
end else begin
	if (PORT_W_CLK_POL) begin
		`INSTANCE(SB_RAM40_4KNR, RCLKN, WCLK)
	end else begin
		`INSTANCE(SB_RAM40_4KNRNW, RCLKN, WCLKN)
	end
end

endgenerate

endmodule
