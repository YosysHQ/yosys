/*
ISC License

Copyright (C) 2024 Microchip Technology Inc. and its subsidiaries

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

// See document PolarFire Family Fabric User Guide
//   section 4.1 for port list.


//LSRAM true dual-port
module $__LSRAM_TDP_ (...);

parameter INIT = 0;
parameter ADDR_BITS = 14;

parameter OPTION_WIDTH_CONFIG = "A";

parameter PORT_A_WIDTH = 1;
parameter PORT_A_WR_EN_WIDTH = 1;
parameter PORT_A_RD_USED = 0;
parameter PORT_A_WR_USED = 0;
parameter PORT_A_OPTION_WRITE_MODE = "NO_CHANGE";

parameter PORT_B_WIDTH = 1;
parameter PORT_B_WR_EN_WIDTH = 1;
parameter PORT_B_RD_USED = 0;
parameter PORT_B_WR_USED = 0;
parameter PORT_B_OPTION_WRITE_MODE = "NO_CHANGE";


input PORT_A_CLK;
input PORT_A_RD_EN;
input [ADDR_BITS-1:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
input [PORT_A_WR_EN_WIDTH-1:0] PORT_A_WR_EN;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;


input PORT_B_CLK;
input PORT_B_RD_EN;
input [ADDR_BITS-1:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
input [PORT_B_WR_EN_WIDTH-1:0] PORT_B_WR_EN;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;


`include "brams_defs.vh"

// address wires
wire [ADDR_BITS-1:0] A_address;
wire [ADDR_BITS-1:0] B_address;
assign A_address = (OPTION_WIDTH_CONFIG == "REGULAR") ? PORT_A_ADDR : {PORT_A_ADDR, 2'b00};
assign B_address = (OPTION_WIDTH_CONFIG == "REGULAR") ? PORT_B_ADDR : {PORT_B_ADDR, 2'b00};

// if port is not used, set block sel to 0 to disable it (read-data output is set to 0)
parameter PORT_A_RD_USED = 0;
parameter PORT_A_WR_USED = 0;
wire [2:0] A_BLK_SEL = (PORT_A_RD_USED == 1 || PORT_A_WR_USED == 1) ? 3'b111 : 3'b000;
wire [2:0] B_BLK_SEL = (PORT_B_RD_USED == 1 || PORT_B_WR_USED == 1) ? 3'b111 : 3'b000;

// wires for write data 
generate
	wire [19:0] A_write_data;
	wire [19:0] B_write_data;
	if (PORT_A_WIDTH == 16) begin
		assign A_write_data[7:0] = PORT_A_WR_DATA[7:0];
		assign A_write_data[17:10] = PORT_A_WR_DATA[15:8];
		assign A_write_data[9:8] = 2'b0;
		assign A_write_data[19:18] = 2'b0;
	end else begin
		assign A_write_data[PORT_A_WIDTH-1:0] = PORT_A_WR_DATA;
	end

	if (PORT_B_WIDTH == 16) begin
		assign B_write_data[7:0] = PORT_B_WR_DATA[7:0];
		assign B_write_data[17:10] = PORT_B_WR_DATA[15:8];
		assign B_write_data[9:8] = 2'b0;
		assign B_write_data[19:18] = 2'b0;
	end else begin
		assign B_write_data[PORT_B_WIDTH-1:0] = PORT_B_WR_DATA;
	end
endgenerate

// wires for read data
wire [19:0] A_read_data;
assign PORT_A_RD_DATA = A_read_data[PORT_A_WIDTH-1:0];
wire [19:0] B_read_data;
assign PORT_B_RD_DATA = B_read_data[PORT_B_WIDTH-1:0];

// byte-write enables
wire [1:0] A_write_EN = (PORT_A_WR_EN_WIDTH == 1) ? {1'b0, PORT_A_WR_EN} : PORT_A_WR_EN;
wire [1:0] B_write_EN = (PORT_B_WR_EN_WIDTH == 1) ? {1'b0, PORT_B_WR_EN} : PORT_B_WR_EN;

// port width
wire [2:0] A_width = (PORT_A_WIDTH == 1) ? 3'b000 :
					(PORT_A_WIDTH == 2) ? 3'b001 :
					(PORT_A_WIDTH == 4 || PORT_A_WIDTH == 5) ? 3'b010 :
					(PORT_A_WIDTH == 8 || PORT_A_WIDTH == 10) ? 3'b011 : 3'b100;
wire [2:0] B_width = (PORT_B_WIDTH == 1) ? 3'b000 :
					(PORT_B_WIDTH == 2) ? 3'b001 :
					(PORT_B_WIDTH == 4 || PORT_B_WIDTH == 5) ? 3'b010 :
					(PORT_B_WIDTH == 8 || PORT_B_WIDTH == 10) ? 3'b011 : 3'b100;

// write modes
wire [1:0] A_write_mode = PORT_A_OPTION_WRITE_MODE == "NO_CHANGE" ? 2'b00 : 
						PORT_A_OPTION_WRITE_MODE == "WRITE_FIRST" ? 2'b01 : 2'b10;
wire [1:0] B_write_mode = PORT_B_OPTION_WRITE_MODE == "NO_CHANGE" ? 2'b00 : 
						PORT_B_OPTION_WRITE_MODE == "WRITE_FIRST" ? 2'b01 : 2'b10;

RAM1K20 #(
	`PARAMS_INIT_LSRAM
) _TECHMAP_REPLACE_ (

	// port A
	.A_ADDR(A_address),
	.A_BLK_EN(A_BLK_SEL),
	.A_CLK(PORT_A_CLK),
	.A_DIN(A_write_data),
	.A_DOUT(A_read_data),
	.A_WEN(A_write_EN),
	.A_REN(PORT_A_RD_EN),
	.A_WIDTH(A_width),
	.A_WMODE(A_write_mode),
	.A_BYPASS(1'b1),
	.A_DOUT_EN(1'b1),
	.A_DOUT_SRST_N(1'b1),
	.A_DOUT_ARST_N(1'b1),

	// port B
	.B_ADDR(B_address),
	.B_BLK_EN(B_BLK_SEL),
	.B_CLK(PORT_B_CLK),
	.B_DIN(B_write_data),
	.B_DOUT(B_read_data),
	.B_WEN(B_write_EN),
	.B_REN(PORT_B_RD_EN),
	.B_WIDTH(B_width),
	.B_WMODE(B_write_mode),
	.B_BYPASS(1'b1),
	.B_DOUT_EN(1'b1),
	.B_DOUT_SRST_N(1'b1),
	.B_DOUT_ARST_N(1'b1),

	// Disable ECC for TDP
	.ECC_EN(1'b0), 
	.ECC_BYPASS(1'b1),
	.BUSY_FB(1'b0)

);

endmodule

// single dual port configuration
module $__LSRAM_SDP_ (...);

parameter INIT = 0;
parameter OPTION_WIDTH_CONFIG = "REGULAR";
parameter ADDR_BITS = 14;

parameter PORT_W_WIDTH = 1;
parameter PORT_W_WR_EN_WIDTH = 4;
parameter PORT_W_USED = 1;

parameter PORT_R_WIDTH = 1;
parameter PORT_R_USED = 0;

input PORT_W_CLK;
input [ADDR_BITS-1:0] PORT_W_ADDR;
input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;
input [PORT_W_WR_EN_WIDTH-1:0] PORT_W_WR_EN;

input PORT_R_CLK;
input PORT_R_RD_EN;
input [ADDR_BITS-1:0] PORT_R_ADDR;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;
input PORT_R_RD_SRST;

`include "brams_defs.vh"


// address wires
wire [ADDR_BITS-1:0] A_address;
wire [ADDR_BITS-1:0] B_address;
assign A_address = (OPTION_WIDTH_CONFIG == "REGULAR") ? PORT_R_ADDR : {PORT_R_ADDR, 2'b00};
assign B_address = (OPTION_WIDTH_CONFIG == "REGULAR") ? PORT_W_ADDR : {PORT_W_ADDR, 2'b00};

// if port is not used, set block sel to 0 to disable it (read-data output is set to 0)
// port A is for read, port B for write
parameter PORT_W_USED = 0;
parameter PORT_R_USED = 0;
wire [2:0] A_BLK_SEL = (PORT_R_USED == 1) ? 3'b111 : 3'b000;
wire [2:0] B_BLK_SEL = (PORT_W_USED == 1) ? 3'b111 : 3'b000;

// read/write data & write enables
// Currently support only wide write, width = {32, 40}
generate
	wire [19:0] A_write_data;
	wire [19:0] B_write_data;
	wire [1:0] A_write_EN;
	wire [1:0] B_write_EN;

	// write port (A provides MSB) 
	if (PORT_W_WIDTH == 32) begin

		assign B_write_data[3:0] = PORT_W_WR_DATA[3:0];
		assign B_write_data[8:5] = PORT_W_WR_DATA[7:4];
		assign B_write_data[13:10] = PORT_W_WR_DATA[11:8];
		assign B_write_data[18:15] = PORT_W_WR_DATA[15:12];
		assign B_write_data[4] = 1'b0;
		assign B_write_data[9] = 1'b0;
		assign B_write_data[14] = 1'b0;
		assign B_write_data[19] = 1'b0;

		assign A_write_data[3:0] = PORT_W_WR_DATA[19:16];
		assign A_write_data[8:5] = PORT_W_WR_DATA[23:20];
		assign A_write_data[13:10] = PORT_W_WR_DATA[27:24];
		assign A_write_data[18:15] = PORT_W_WR_DATA[31:28];
		assign A_write_data[4] = 1'b0;
		assign A_write_data[9] = 1'b0;
		assign A_write_data[14] = 1'b0;
		assign A_write_data[19] = 1'b0;
		
	end else if (PORT_W_WIDTH == 40) begin
		assign B_write_data = PORT_W_WR_DATA[19:0];
		assign A_write_data = PORT_W_WR_DATA[39:20];
	end

	// byte-write enables
	assign A_write_EN = PORT_W_WR_EN[1:0];
	assign B_write_EN = PORT_W_WR_EN[3:2];

	// read ports (A provides MSB)
	wire [19:0] A_read_data;
	wire [19:0] B_read_data;
	if (PORT_R_WIDTH == 32) begin
		assign PORT_R_RD_DATA[3:0] = B_read_data[3:0];
		assign PORT_R_RD_DATA[8:5] = B_read_data[7:4];
		assign PORT_R_RD_DATA[13:10] = B_read_data[11:8];
		assign PORT_R_RD_DATA[18:15] = B_read_data[15:12];

		assign PORT_R_RD_DATA[19:16] = A_read_data[3:0];
		assign PORT_R_RD_DATA[23:20] = A_read_data[8:5];
		assign PORT_R_RD_DATA[27:24] = A_read_data[13:10];
		assign PORT_R_RD_DATA[31:28] = A_read_data[18:15];
	end else if (PORT_R_WIDTH == 40) begin
		assign PORT_R_RD_DATA[19:0] = B_read_data[19:0];
		assign PORT_R_RD_DATA[39:20] = A_read_data[19:0];
	end
endgenerate

// port width
wire [2:0] A_width = (PORT_R_WIDTH == 1) ? 3'b000 :
					(PORT_R_WIDTH == 2) ? 3'b001 :
					(PORT_R_WIDTH == 4 || PORT_R_WIDTH == 5) ? 3'b010 :
					(PORT_R_WIDTH == 8 || PORT_R_WIDTH == 10) ? 3'b011 : 
					(PORT_R_WIDTH == 16 || PORT_R_WIDTH == 20) ? 3'b100 : 3'b101;
wire [2:0] B_width = (PORT_W_WIDTH == 1) ? 3'b000 :
					(PORT_W_WIDTH == 2) ? 3'b001 :
					(PORT_W_WIDTH == 4 || PORT_W_WIDTH == 5) ? 3'b010 :
					(PORT_W_WIDTH == 8 || PORT_W_WIDTH == 10) ? 3'b011 :
					(PORT_W_WIDTH == 16 || PORT_W_WIDTH == 20) ? 3'b100 : 3'b101;

// write modes
wire [1:0] A_write_mode = 2'b00;
wire [1:0] B_write_mode = 2'b00;

RAM1K20 #(
	`PARAMS_INIT_LSRAM
) _TECHMAP_REPLACE_ (
	// port A - read
	.A_ADDR(A_address),
	.A_BLK_EN(A_BLK_SEL),
	.A_CLK(PORT_R_CLK),
	.A_DIN(A_write_data),
	.A_DOUT(A_read_data),
	.A_WEN(A_write_EN),
	.A_REN(PORT_R_RD_EN),
	.A_WIDTH(A_width),
	.A_WMODE(A_write_mode),
	.A_BYPASS(1'b1),
	.A_DOUT_EN(1'b1),
	.A_DOUT_SRST_N(1'b1),
	.A_DOUT_ARST_N(1'b1),

	// port B - write
	.B_ADDR(B_address),
	.B_BLK_EN(B_BLK_SEL),
	.B_CLK(PORT_W_CLK),
	.B_DIN(B_write_data),
	.B_DOUT(B_read_data),
	.B_WEN(B_write_EN),
	.B_REN(PORT_R_RD_EN),
	.B_WIDTH(B_width),
	.B_WMODE(B_write_mode),
	.B_BYPASS(1'b1),
	.B_DOUT_EN(1'b1),
	.B_DOUT_SRST_N(1'b1),
	.B_DOUT_ARST_N(1'b1),

	// Disable ECC for SDP
	.ECC_EN(1'b0), 
	.ECC_BYPASS(1'b1),
	.BUSY_FB(1'b0)
);


endmodule
