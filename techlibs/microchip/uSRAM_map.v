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
// section 4.2 for port list.

// Asynchronous read
module $__uSRAM_AR_ (...);

parameter INIT = 0;
parameter ADDR_BITS = 6;

parameter PORT_W_WIDTH = 12;
parameter PORT_R_WIDTH = 12;
parameter PORT_R_USED = 0;
parameter PORT_W_USED = 0;

input PORT_W_CLK;
input [ADDR_BITS-1:0] PORT_W_ADDR;
input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;
input PORT_W_WR_EN;

input [ADDR_BITS-1:0] PORT_R_ADDR;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;

`include "brams_defs.vh"

RAM64x12 #(
	`PARAMS_INIT_uSRAM
) _TECHMAP_REPLACE_ (
	.R_ADDR(PORT_R_ADDR),
	.R_ADDR_BYPASS(1'b1),
	.R_ADDR_EN(1'b0),
	.R_ADDR_SL_N(1'b1),
	.R_ADDR_SD(1'b0),
	.R_ADDR_AL_N(1'b1), 
	.R_ADDR_AD_N(1'b0),
	.BLK_EN(PORT_R_USED ? 1'b1 : 1'b0),
	.R_DATA(PORT_R_RD_DATA),
	.R_DATA_BYPASS(1'b1),
	.R_DATA_EN(1'b0),
	.R_DATA_SL_N(1'b1),
	.R_DATA_SD(1'b0),
	.R_DATA_AL_N(1'b1),
	.R_DATA_AD_N(1'b0),

	.W_CLK(PORT_W_CLK),
	.W_ADDR(PORT_W_ADDR),
	.W_DATA(PORT_W_WR_DATA),
	.W_EN(PORT_W_WR_EN),

	.BUSY_FB(1'b0)
);

endmodule

// Synchronous read
module $__uSRAM_SR_ (...);

parameter INIT = 0;
parameter ADDR_BITS = 6;

parameter PORT_W_WIDTH = 12;
parameter PORT_R_WIDTH = 12;
parameter PORT_R_USED = 0;
parameter PORT_W_USED = 0;

input PORT_W_CLK;
input [ADDR_BITS-1:0] PORT_W_ADDR;
input [PORT_W_WIDTH-1:0] PORT_W_WR_DATA;
input PORT_W_WR_EN;

// Read port clock and enable signal
// that async read uSRAM doesn't have
input PORT_R_CLK;
input PORT_R_RD_EN;
input [ADDR_BITS-1:0] PORT_R_ADDR;
output [PORT_R_WIDTH-1:0] PORT_R_RD_DATA;

`include "brams_defs.vh"

RAM64x12 #(
	`PARAMS_INIT_uSRAM
) _TECHMAP_REPLACE_ (
	.R_CLK(PORT_R_CLK),
	.R_ADDR(PORT_R_ADDR),
	.R_ADDR_BYPASS(1'b0),
	.R_ADDR_EN(PORT_R_RD_EN),
	.R_ADDR_SL_N(1'b1),
	.R_ADDR_SD(1'b0),
	.R_ADDR_AL_N(1'b1), 
	.R_ADDR_AD_N(1'b0),
	.BLK_EN(PORT_R_USED ? 1'b1 : 1'b0),
	.R_DATA(PORT_R_RD_DATA),
	.R_DATA_BYPASS(1'b1),
	.R_DATA_EN(1'b0),
	.R_DATA_SL_N(1'b1),
	.R_DATA_SD(1'b0),
	.R_DATA_AL_N(1'b1),
	.R_DATA_AD_N(1'b0),

	.W_CLK(PORT_W_CLK),
	.W_ADDR(PORT_W_ADDR),
	.W_DATA(PORT_W_WR_DATA),
	.W_EN(PORT_W_WR_EN),

	.BUSY_FB(1'b0)
);

endmodule

