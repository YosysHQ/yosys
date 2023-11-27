// Copyright 2020-2022 F4PGA Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0

module BRAM2x18_SP (
    RESET_ni,
    
    WEN1_i,
    REN1_i,
    WR1_CLK_i,
    RD1_CLK_i,
    WR1_BE_i,
    WR1_ADDR_i,
    RD1_ADDR_i,
    WDATA1_i,
    RDATA1_o,
    
    WEN2_i,
    REN2_i,
    WR2_CLK_i,
    RD2_CLK_i,
    WR2_BE_i,
    WR2_ADDR_i,
    RD2_ADDR_i,
    WDATA2_i,
    RDATA2_o
);

parameter WR1_ADDR_WIDTH = 10;
parameter RD1_ADDR_WIDTH = 10;
parameter WR1_DATA_WIDTH = 18;
parameter RD1_DATA_WIDTH = 18;
parameter BE1_WIDTH = 2;

parameter WR2_ADDR_WIDTH = 10;
parameter RD2_ADDR_WIDTH = 10;
parameter WR2_DATA_WIDTH = 18;
parameter RD2_DATA_WIDTH = 18;
parameter BE2_WIDTH = 2;

input wire RESET_ni;

input wire WEN1_i;
input wire REN1_i;
input wire WR1_CLK_i;
input wire RD1_CLK_i;
input wire [BE1_WIDTH-1:0] WR1_BE_i;
input wire [WR1_ADDR_WIDTH-1 :0] WR1_ADDR_i;
input wire [RD1_ADDR_WIDTH-1 :0] RD1_ADDR_i;
input wire [WR1_DATA_WIDTH-1 :0] WDATA1_i;
output wire [RD1_DATA_WIDTH-1 :0] RDATA1_o;

input wire WEN2_i;
input wire REN2_i;
input wire WR2_CLK_i;
input wire RD2_CLK_i;
input wire [BE2_WIDTH-1:0] WR2_BE_i;
input wire [WR2_ADDR_WIDTH-1 :0] WR2_ADDR_i;
input wire [RD2_ADDR_WIDTH-1 :0] RD2_ADDR_i;
input wire [WR2_DATA_WIDTH-1 :0] WDATA2_i;
output wire [RD2_DATA_WIDTH-1 :0] RDATA2_o;

// Fixed mode settings
localparam [ 0:0] SYNC_FIFO1_i  = 1'd0;
localparam [ 0:0] FMODE1_i      = 1'd0;
localparam [ 0:0] POWERDN1_i    = 1'd0;
localparam [ 0:0] SLEEP1_i      = 1'd0;
localparam [ 0:0] PROTECT1_i    = 1'd0;
localparam [11:0] UPAE1_i       = 12'd10;
localparam [11:0] UPAF1_i       = 12'd10;

localparam [ 0:0] SYNC_FIFO2_i  = 1'd0;
localparam [ 0:0] FMODE2_i      = 1'd0;
localparam [ 0:0] POWERDN2_i    = 1'd0;
localparam [ 0:0] SLEEP2_i      = 1'd0;
localparam [ 0:0] PROTECT2_i    = 1'd0;
localparam [10:0] UPAE2_i       = 11'd10;
localparam [10:0] UPAF2_i       = 11'd10;

// Width mode function
function [2:0] mode;
input integer width;
case (width)
1: mode = 3'b101;
2: mode = 3'b110;
4: mode = 3'b100;
8,9: mode = 3'b001;
16, 18: mode = 3'b010;
32, 36: mode = 3'b011;
default: mode = 3'b000;
endcase
endfunction

function integer rwmode;
input integer rwwidth;
case (rwwidth)
1: rwmode = 1;
2: rwmode = 2;
4: rwmode = 4;
8,9: rwmode = 9;
16, 18: rwmode = 18;
default: rwmode = 18;
endcase
endfunction

wire REN_A1_i;
wire REN_A2_i;

wire REN_B1_i;
wire REN_B2_i;

wire WEN_A1_i;
wire WEN_A2_i;

wire WEN_B1_i;
wire WEN_B2_i;

wire [1:0] BE_A1_i;
wire [1:0] BE_A2_i;

wire [1:0] BE_B1_i;
wire [1:0] BE_B2_i;

wire [14:0] ADDR_A1_i;
wire [13:0] ADDR_A2_i;

wire [14:0] ADDR_B1_i;
wire [13:0] ADDR_B2_i;

wire [17:0] WDATA_A1_i;
wire [17:0] WDATA_A2_i;

wire [17:0] WDATA_B1_i;
wire [17:0] WDATA_B2_i;

wire [17:0] RDATA_A1_o;
wire [17:0] RDATA_A2_o;

wire [17:0] RDATA_B1_o;
wire [17:0] RDATA_B2_o;

wire [1:0] WR1_BE;
wire [1:0] WR2_BE;

wire [17:0] PORT_B1_RDATA;
wire [17:0] PORT_A1_WDATA;

wire [17:0] PORT_B2_RDATA;
wire [17:0] PORT_A2_WDATA;

wire [13:0] WR1_ADDR_INT;
wire [13:0] RD1_ADDR_INT; 

wire [13:0] WR2_ADDR_INT;
wire [13:0] RD2_ADDR_INT; 

wire [13:0] PORT_A1_ADDR;
wire [13:0] PORT_B1_ADDR;

wire [13:0] PORT_A2_ADDR;
wire [13:0] PORT_B2_ADDR;


// Set port width mode (In non-split mode A2/B2 is not active. Set same values anyway to match previous behavior.)
localparam [ 2:0] RMODE_A1_i    = mode(WR1_DATA_WIDTH);
localparam [ 2:0] WMODE_A1_i    = mode(WR1_DATA_WIDTH);
localparam [ 2:0] RMODE_A2_i    = mode(WR2_DATA_WIDTH);
localparam [ 2:0] WMODE_A2_i    = mode(WR2_DATA_WIDTH);

localparam [ 2:0] RMODE_B1_i    = mode(RD1_DATA_WIDTH);
localparam [ 2:0] WMODE_B1_i    = mode(RD1_DATA_WIDTH);
localparam [ 2:0] RMODE_B2_i    = mode(RD2_DATA_WIDTH);
localparam [ 2:0] WMODE_B2_i    = mode(RD2_DATA_WIDTH);

localparam PORT_A1_WRWIDTH = rwmode(WR1_DATA_WIDTH);
localparam PORT_B1_WRWIDTH = rwmode(RD1_DATA_WIDTH);
localparam PORT_A2_WRWIDTH = rwmode(WR2_DATA_WIDTH);
localparam PORT_B2_WRWIDTH = rwmode(RD2_DATA_WIDTH);

generate
  if (WR1_ADDR_WIDTH == 14) begin
    assign WR1_ADDR_INT = WR1_ADDR_i;
  end else begin
    assign WR1_ADDR_INT[13:WR1_ADDR_WIDTH] = 0;
    assign WR1_ADDR_INT[WR1_ADDR_WIDTH-1:0] = WR1_ADDR_i;
  end
endgenerate

case (WR1_DATA_WIDTH)
	1: begin
		assign PORT_A1_ADDR = WR1_ADDR_INT;
	end
	2: begin
		assign PORT_A1_ADDR = WR1_ADDR_INT << 1;
	end
	4: begin
		assign PORT_A1_ADDR = WR1_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_A1_ADDR = WR1_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_A1_ADDR = WR1_ADDR_INT << 4;
	end
	default: begin
		assign PORT_A1_ADDR = WR1_ADDR_INT;
	end
endcase

generate
  if (RD1_ADDR_WIDTH == 14) begin
    assign RD1_ADDR_INT = RD1_ADDR_i;
  end else begin
    assign RD1_ADDR_INT[13:RD1_ADDR_WIDTH] = 0;
    assign RD1_ADDR_INT[RD1_ADDR_WIDTH-1:0] = RD1_ADDR_i;
  end
endgenerate

case (RD1_DATA_WIDTH)
	1: begin
		assign PORT_B1_ADDR = RD1_ADDR_INT;
	end
	2: begin
		assign PORT_B1_ADDR = RD1_ADDR_INT << 1;
	end
	4: begin
		assign PORT_B1_ADDR = RD1_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_B1_ADDR = RD1_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_B1_ADDR = RD1_ADDR_INT << 4;
	end
	default: begin
		assign PORT_B1_ADDR = RD1_ADDR_INT;
	end
endcase

generate
  if (WR2_ADDR_WIDTH == 14) begin
    assign WR2_ADDR_INT = WR2_ADDR_i;
  end else begin
    assign WR2_ADDR_INT[13:WR2_ADDR_WIDTH] = 0;
    assign WR2_ADDR_INT[WR2_ADDR_WIDTH-1:0] = WR2_ADDR_i;
  end
endgenerate

case (WR2_DATA_WIDTH)
	1: begin
		assign PORT_A2_ADDR = WR2_ADDR_INT;
	end
	2: begin
		assign PORT_A2_ADDR = WR2_ADDR_INT << 1;
	end
	4: begin
		assign PORT_A2_ADDR = WR2_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_A2_ADDR = WR2_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_A2_ADDR = WR2_ADDR_INT << 4;
	end
	default: begin
		assign PORT_A2_ADDR = WR2_ADDR_INT;
	end
endcase

generate
  if (RD2_ADDR_WIDTH == 14) begin
    assign RD2_ADDR_INT = RD2_ADDR_i;
  end else begin
    assign RD2_ADDR_INT[13:RD2_ADDR_WIDTH] = 0;
    assign RD2_ADDR_INT[RD2_ADDR_WIDTH-1:0] = RD2_ADDR_i;
  end
endgenerate

case (RD2_DATA_WIDTH)
	1: begin
		assign PORT_B2_ADDR = RD2_ADDR_INT;
	end
	2: begin
		assign PORT_B2_ADDR = RD2_ADDR_INT << 1;
	end
	4: begin
		assign PORT_B2_ADDR = RD2_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_B2_ADDR = RD2_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_B2_ADDR = RD2_ADDR_INT << 4;
	end
	default: begin
		assign PORT_B2_ADDR = RD2_ADDR_INT;
	end
endcase

case (BE1_WIDTH)
	2: begin
		assign WR1_BE = WR1_BE_i[BE1_WIDTH-1 :0];
	end
	default: begin
		assign WR1_BE[1:BE1_WIDTH] = 0;
		assign WR1_BE[BE1_WIDTH-1 :0] = WR1_BE_i[BE1_WIDTH-1 :0];
	end
endcase

case (BE2_WIDTH)
	2: begin
		assign WR2_BE = WR2_BE_i[BE2_WIDTH-1 :0];
	end
	default: begin
		assign WR2_BE[1:BE2_WIDTH] = 0;
		assign WR2_BE[BE2_WIDTH-1 :0] = WR2_BE_i[BE2_WIDTH-1 :0];
	end
endcase

assign REN_A1_i = 1'b0;
assign WEN_A1_i = WEN1_i;
assign BE_A1_i = WR1_BE;
assign REN_A2_i = 1'b0;
assign WEN_A2_i = WEN2_i;
assign BE_A2_i = WR2_BE;

assign REN_B1_i = REN1_i;
assign WEN_B1_i = 1'b0;
assign BE_B1_i = 4'h0;
assign REN_B2_i = REN2_i;
assign WEN_B2_i = 1'b0;
assign BE_B2_i = 4'h0;

generate
  if (WR1_DATA_WIDTH == 18) begin
    assign PORT_A1_WDATA[WR1_DATA_WIDTH-1:0] = WDATA1_i[WR1_DATA_WIDTH-1:0];
  end else if (WR1_DATA_WIDTH == 9) begin
    assign PORT_A1_WDATA = {1'b0, WDATA1_i[8], 8'h0, WDATA1_i[7:0]};
  end else begin
    assign PORT_A1_WDATA[17:WR1_DATA_WIDTH] = 0;
    assign PORT_A1_WDATA[WR1_DATA_WIDTH-1:0] = WDATA1_i[WR1_DATA_WIDTH-1:0];
  end
endgenerate

assign WDATA_A1_i = PORT_A1_WDATA[17:0];
assign WDATA_B1_i = 18'h0;

generate
  if (RD1_DATA_WIDTH == 9) begin
    assign PORT_B1_RDATA = { 9'h0, RDATA_B1_o[16], RDATA_B1_o[7:0]};
  end else begin
    assign PORT_B1_RDATA = RDATA_B1_o;
  end
endgenerate

assign RDATA1_o = PORT_B1_RDATA[RD1_DATA_WIDTH-1:0];

generate
  if (WR2_DATA_WIDTH == 18) begin
    assign PORT_A2_WDATA[WR2_DATA_WIDTH-1:0] = WDATA2_i[WR2_DATA_WIDTH-1:0];
  end else if (WR2_DATA_WIDTH == 9) begin
    assign PORT_A2_WDATA = {1'b0, WDATA2_i[8], 8'h0, WDATA2_i[7:0]};
  end else begin
    assign PORT_A2_WDATA[17:WR2_DATA_WIDTH] = 0;
    assign PORT_A2_WDATA[WR2_DATA_WIDTH-1:0] = WDATA2_i[WR2_DATA_WIDTH-1:0];
  end
endgenerate

assign WDATA_A2_i = PORT_A2_WDATA[17:0];
assign WDATA_B2_i = 18'h0;

generate
  if (RD2_DATA_WIDTH == 9) begin
    assign PORT_B2_RDATA = { 9'h0, RDATA_B2_o[16], RDATA_B2_o[7:0]};
  end else begin
    assign PORT_B2_RDATA = RDATA_B2_o;
  end
endgenerate

assign RDATA2_o = PORT_B2_RDATA[RD2_DATA_WIDTH-1:0];

defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b1,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
};

(* is_inferred = 0 *)
(* is_split = 0 *)
(* is_fifo = 0 *)
(* port_a_dwidth = PORT_A1_WRWIDTH *)
(* port_b_dwidth = PORT_B1_WRWIDTH *)
TDP36K _TECHMAP_REPLACE_ (
	.RESET_ni(1'b1),

	.CLK_A1_i(WR1_CLK_i),
	.ADDR_A1_i({1'b0,PORT_A1_ADDR}),
	.WEN_A1_i(WEN_A1_i),
	.BE_A1_i(BE_A1_i),
	.WDATA_A1_i(WDATA_A1_i),
	.REN_A1_i(REN_A1_i),
	.RDATA_A1_o(RDATA_A1_o),

	.CLK_A2_i(WR2_CLK_i),
	.ADDR_A2_i(PORT_A2_ADDR),
	.WEN_A2_i(WEN_A2_i),
	.BE_A2_i(BE_A2_i),
	.WDATA_A2_i(WDATA_A2_i),
	.REN_A2_i(REN_A2_i),
	.RDATA_A2_o(RDATA_A2_o),

	.CLK_B1_i(RD1_CLK_i),
	.ADDR_B1_i({1'b0,PORT_B1_ADDR}),
	.WEN_B1_i(WEN_B1_i),
	.BE_B1_i(BE_B1_i),
	.WDATA_B1_i(WDATA_B1_i),
	.REN_B1_i(REN_B1_i),
	.RDATA_B1_o(RDATA_B1_o),

	.CLK_B2_i(RD2_CLK_i),
	.ADDR_B2_i(PORT_B2_ADDR),
	.WEN_B2_i(WEN_B2_i),
	.BE_B2_i(BE_B2_i),
	.WDATA_B2_i(WDATA_B2_i),
	.REN_B2_i(REN_B2_i),
	.RDATA_B2_o(RDATA_B2_o),

	.FLUSH1_i(1'b0),
	.FLUSH2_i(1'b0)
);

endmodule

module BRAM2x18_dP (   
    PORT_A1_CLK_i,
    PORT_A1_WEN_i,
    PORT_A1_WR_BE_i,
    PORT_A1_REN_i,
    PORT_A1_ADDR_i,
    PORT_A1_WR_DATA_i,
    PORT_A1_RD_DATA_o,
    
    PORT_B1_CLK_i,
    PORT_B1_WEN_i,
    PORT_B1_WR_BE_i,
    PORT_B1_REN_i,
    PORT_B1_ADDR_i,
    PORT_B1_WR_DATA_i,
    PORT_B1_RD_DATA_o,
	
    PORT_A2_CLK_i,
    PORT_A2_WEN_i,
    PORT_A2_WR_BE_i,
    PORT_A2_REN_i,
    PORT_A2_ADDR_i,
    PORT_A2_WR_DATA_i,
    PORT_A2_RD_DATA_o,
    
    PORT_B2_CLK_i,
    PORT_B2_WEN_i,
    PORT_B2_WR_BE_i,
    PORT_B2_REN_i,
    PORT_B2_ADDR_i,
    PORT_B2_WR_DATA_i,
    PORT_B2_RD_DATA_o
);

parameter PORT_A1_AWIDTH = 10;
parameter PORT_A1_DWIDTH = 18;
parameter PORT_A1_WR_BE_WIDTH = 2;
				
parameter PORT_B1_AWIDTH = 10;
parameter PORT_B1_DWIDTH = 18;
parameter PORT_B1_WR_BE_WIDTH = 2;

parameter PORT_A2_AWIDTH = 10;
parameter PORT_A2_DWIDTH = 18;
parameter PORT_A2_WR_BE_WIDTH = 2;
				
parameter PORT_B2_AWIDTH = 10;
parameter PORT_B2_DWIDTH = 18;
parameter PORT_B2_WR_BE_WIDTH = 2;

input PORT_A1_CLK_i;
input [PORT_A1_AWIDTH-1:0] PORT_A1_ADDR_i;
input [PORT_A1_DWIDTH-1:0] PORT_A1_WR_DATA_i;
input PORT_A1_WEN_i;
input [PORT_A1_WR_BE_WIDTH-1:0] PORT_A1_WR_BE_i;
input PORT_A1_REN_i;
output [PORT_A1_DWIDTH-1:0] PORT_A1_RD_DATA_o;

input PORT_B1_CLK_i;
input [PORT_B1_AWIDTH-1:0] PORT_B1_ADDR_i;
input [PORT_B1_DWIDTH-1:0] PORT_B1_WR_DATA_i;
input PORT_B1_WEN_i;
input [PORT_B1_WR_BE_WIDTH-1:0] PORT_B1_WR_BE_i;
input PORT_B1_REN_i;
output [PORT_B1_DWIDTH-1:0] PORT_B1_RD_DATA_o;

input PORT_A2_CLK_i;
input [PORT_A2_AWIDTH-1:0] PORT_A2_ADDR_i;
input [PORT_A2_DWIDTH-1:0] PORT_A2_WR_DATA_i;
input PORT_A2_WEN_i;
input [PORT_A2_WR_BE_WIDTH-1:0] PORT_A2_WR_BE_i;
input PORT_A2_REN_i;
output [PORT_A2_DWIDTH-1:0] PORT_A2_RD_DATA_o;

input PORT_B2_CLK_i;
input [PORT_B2_AWIDTH-1:0] PORT_B2_ADDR_i;
input [PORT_B2_DWIDTH-1:0] PORT_B2_WR_DATA_i;
input PORT_B2_WEN_i;
input [PORT_B2_WR_BE_WIDTH-1:0] PORT_B2_WR_BE_i;
input PORT_B2_REN_i;
output [PORT_B2_DWIDTH-1:0] PORT_B2_RD_DATA_o;


// Fixed mode settings
localparam [ 0:0] SYNC_FIFO1_i  = 1'd0;
localparam [ 0:0] FMODE1_i      = 1'd0;
localparam [ 0:0] POWERDN1_i    = 1'd0;
localparam [ 0:0] SLEEP1_i      = 1'd0;
localparam [ 0:0] PROTECT1_i    = 1'd0;
localparam [11:0] UPAE1_i       = 12'd10;
localparam [11:0] UPAF1_i       = 12'd10;

localparam [ 0:0] SYNC_FIFO2_i  = 1'd0;
localparam [ 0:0] FMODE2_i      = 1'd0;
localparam [ 0:0] POWERDN2_i    = 1'd0;
localparam [ 0:0] SLEEP2_i      = 1'd0;
localparam [ 0:0] PROTECT2_i    = 1'd0;
localparam [10:0] UPAE2_i       = 11'd10;
localparam [10:0] UPAF2_i       = 11'd10;

// Width mode function
function [2:0] mode;
input integer width;
case (width)
1: mode = 3'b101;
2: mode = 3'b110;
4: mode = 3'b100;
8,9: mode = 3'b001;
16, 18: mode = 3'b010;
32, 36: mode = 3'b011;
default: mode = 3'b000;
endcase
endfunction

function integer rwmode;
input integer rwwidth;
case (rwwidth)
1: rwmode = 1;
2: rwmode = 2;
4: rwmode = 4;
8,9: rwmode = 9;
16, 18: rwmode = 18;
default: rwmode = 18;
endcase
endfunction

wire REN_A1_i;
wire REN_A2_i;

wire REN_B1_i;
wire REN_B2_i;

wire WEN_A1_i;
wire WEN_A2_i;

wire WEN_B1_i;
wire WEN_B2_i;

wire [1:0] BE_A1_i;
wire [1:0] BE_A2_i;

wire [1:0] BE_B1_i;
wire [1:0] BE_B2_i;

wire [14:0] ADDR_A1_i;
wire [13:0] ADDR_A2_i;

wire [14:0] ADDR_B1_i;
wire [13:0] ADDR_B2_i;

wire [17:0] WDATA_A1_i;
wire [17:0] WDATA_A2_i;

wire [17:0] WDATA_B1_i;
wire [17:0] WDATA_B2_i;

wire [17:0] RDATA_A1_o;
wire [17:0] RDATA_A2_o;

wire [17:0] RDATA_B1_o;
wire [17:0] RDATA_B2_o;

wire [1:0] PORT_A1_WR_BE;
wire [1:0] PORT_B1_WR_BE;

wire [1:0] PORT_A2_WR_BE;
wire [1:0] PORT_B2_WR_BE;

wire [17:0] PORT_B1_WDATA;
wire [17:0] PORT_B1_RDATA;
wire [17:0] PORT_A1_WDATA;
wire [17:0] PORT_A1_RDATA;

wire [17:0] PORT_B2_WDATA;
wire [17:0] PORT_B2_RDATA;
wire [17:0] PORT_A2_WDATA;
wire [17:0] PORT_A2_RDATA;

wire [13:0] PORT_A1_ADDR_INT;
wire [13:0] PORT_B1_ADDR_INT; 

wire [13:0] PORT_A2_ADDR_INT;
wire [13:0] PORT_B2_ADDR_INT; 
	   
wire [13:0] PORT_A1_ADDR;
wire [13:0] PORT_B1_ADDR;

wire [13:0] PORT_A2_ADDR;
wire [13:0] PORT_B2_ADDR;

wire PORT_A1_CLK;
wire PORT_B1_CLK;

wire PORT_A2_CLK;
wire PORT_B2_CLK;

// Set port width mode (In non-split mode A2/B2 is not active. Set same values anyway to match previous behavior.)
localparam [ 2:0] RMODE_A1_i    = mode(PORT_A1_DWIDTH);
localparam [ 2:0] WMODE_A1_i    = mode(PORT_A1_DWIDTH);
localparam [ 2:0] RMODE_A2_i    = mode(PORT_A2_DWIDTH);
localparam [ 2:0] WMODE_A2_i    = mode(PORT_A2_DWIDTH);

localparam [ 2:0] RMODE_B1_i    = mode(PORT_B1_DWIDTH);
localparam [ 2:0] WMODE_B1_i    = mode(PORT_B1_DWIDTH);
localparam [ 2:0] RMODE_B2_i    = mode(PORT_B2_DWIDTH);
localparam [ 2:0] WMODE_B2_i    = mode(PORT_B2_DWIDTH);

localparam PORT_A1_WRWIDTH = rwmode(PORT_A1_DWIDTH);
localparam PORT_B1_WRWIDTH = rwmode(PORT_B1_DWIDTH);
localparam PORT_A2_WRWIDTH = rwmode(PORT_A2_DWIDTH);
localparam PORT_B2_WRWIDTH = rwmode(PORT_B2_DWIDTH);

assign PORT_A1_CLK = PORT_A1_CLK_i;
assign PORT_B1_CLK = PORT_B1_CLK_i;

assign PORT_A2_CLK = PORT_A2_CLK_i;
assign PORT_B2_CLK = PORT_B2_CLK_i;

generate
  if (PORT_A1_AWIDTH == 14) begin
    assign PORT_A1_ADDR_INT = PORT_A1_ADDR_i;
  end else begin
    assign PORT_A1_ADDR_INT[13:PORT_A1_AWIDTH] = 0;
    assign PORT_A1_ADDR_INT[PORT_A1_AWIDTH-1:0] = PORT_A1_ADDR_i;
  end
endgenerate

case (PORT_A1_DWIDTH)
	1: begin
		assign PORT_A1_ADDR = PORT_A1_ADDR_INT;
	end
	2: begin
		assign PORT_A1_ADDR = PORT_A1_ADDR_INT << 1;
	end
	4: begin
		assign PORT_A1_ADDR = PORT_A1_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_A1_ADDR = PORT_A1_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_A1_ADDR = PORT_A1_ADDR_INT << 4;
	end
	default: begin
		assign PORT_A1_ADDR = PORT_A1_ADDR_INT;
	end
endcase

generate
  if (PORT_B1_AWIDTH == 14) begin
    assign PORT_B1_ADDR_INT = PORT_B1_ADDR_i;
  end else begin
    assign PORT_B1_ADDR_INT[13:PORT_B1_AWIDTH] = 0;
    assign PORT_B1_ADDR_INT[PORT_B1_AWIDTH-1:0] = PORT_B1_ADDR_i;
  end
endgenerate

case (PORT_B1_DWIDTH)
	1: begin
		assign PORT_B1_ADDR = PORT_B1_ADDR_INT;
	end
	2: begin
		assign PORT_B1_ADDR = PORT_B1_ADDR_INT << 1;
	end
	4: begin
		assign PORT_B1_ADDR = PORT_B1_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_B1_ADDR = PORT_B1_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_B1_ADDR = PORT_B1_ADDR_INT << 4;
	end
	default: begin
		assign PORT_B1_ADDR = PORT_B1_ADDR_INT;
	end
endcase

generate
  if (PORT_A2_AWIDTH == 14) begin
    assign PORT_A2_ADDR_INT = PORT_A2_ADDR_i;
  end else begin
    assign PORT_A2_ADDR_INT[13:PORT_A2_AWIDTH] = 0;
    assign PORT_A2_ADDR_INT[PORT_A2_AWIDTH-1:0] = PORT_A2_ADDR_i;
  end
endgenerate

case (PORT_A2_DWIDTH)
	1: begin
		assign PORT_A2_ADDR = PORT_A2_ADDR_INT;
	end
	2: begin
		assign PORT_A2_ADDR = PORT_A2_ADDR_INT << 1;
	end
	4: begin
		assign PORT_A2_ADDR = PORT_A2_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_A2_ADDR = PORT_A2_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_A2_ADDR = PORT_A2_ADDR_INT << 4;
	end
	default: begin
		assign PORT_A2_ADDR = PORT_A2_ADDR_INT;
	end
endcase

generate
  if (PORT_B2_AWIDTH == 14) begin
    assign PORT_B2_ADDR_INT = PORT_B2_ADDR_i;
  end else begin
    assign PORT_B2_ADDR_INT[13:PORT_B2_AWIDTH] = 0;
    assign PORT_B2_ADDR_INT[PORT_B2_AWIDTH-1:0] = PORT_B2_ADDR_i;
  end
endgenerate

case (PORT_B2_DWIDTH)
	1: begin
		assign PORT_B2_ADDR = PORT_B2_ADDR_INT;
	end
	2: begin
		assign PORT_B2_ADDR = PORT_B2_ADDR_INT << 1;
	end
	4: begin
		assign PORT_B2_ADDR = PORT_B2_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_B2_ADDR = PORT_B2_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_B2_ADDR = PORT_B2_ADDR_INT << 4;
	end
	default: begin
		assign PORT_B2_ADDR = PORT_B2_ADDR_INT;
	end
endcase

case (PORT_A1_WR_BE_WIDTH)
	2: begin
		assign PORT_A1_WR_BE = PORT_A1_WR_BE_i[PORT_A1_WR_BE_WIDTH-1 :0];
	end
	default: begin
		assign PORT_A1_WR_BE[1:PORT_A1_WR_BE_WIDTH] = 0;
		assign PORT_A1_WR_BE[PORT_A1_WR_BE_WIDTH-1 :0] = PORT_A1_WR_BE_i[PORT_A1_WR_BE_WIDTH-1 :0];
	end
endcase

case (PORT_B1_WR_BE_WIDTH)
	2: begin
		assign PORT_B1_WR_BE = PORT_B1_WR_BE_i[PORT_B1_WR_BE_WIDTH-1 :0];
	end
	default: begin
		assign PORT_B1_WR_BE[1:PORT_B1_WR_BE_WIDTH] = 0;
		assign PORT_B1_WR_BE[PORT_B1_WR_BE_WIDTH-1 :0] = PORT_B1_WR_BE_i[PORT_B1_WR_BE_WIDTH-1 :0];
	end
endcase

case (PORT_A2_WR_BE_WIDTH)
	2: begin
		assign PORT_A2_WR_BE = PORT_A2_WR_BE_i[PORT_A2_WR_BE_WIDTH-1 :0];
	end
	default: begin
		assign PORT_A2_WR_BE[1:PORT_A2_WR_BE_WIDTH] = 0;
		assign PORT_A2_WR_BE[PORT_A2_WR_BE_WIDTH-1 :0] = PORT_A2_WR_BE_i[PORT_A2_WR_BE_WIDTH-1 :0];
	end
endcase

case (PORT_B2_WR_BE_WIDTH)
	2: begin
		assign PORT_B2_WR_BE = PORT_B2_WR_BE_i[PORT_B2_WR_BE_WIDTH-1 :0];
	end
	default: begin
		assign PORT_B2_WR_BE[1:PORT_B2_WR_BE_WIDTH] = 0;
		assign PORT_B2_WR_BE[PORT_B2_WR_BE_WIDTH-1 :0] = PORT_B2_WR_BE_i[PORT_B2_WR_BE_WIDTH-1 :0];
	end
endcase

assign REN_A1_i = PORT_A1_REN_i;
assign WEN_A1_i = PORT_A1_WEN_i;
assign BE_A1_i  = PORT_A1_WR_BE;

assign REN_A2_i = PORT_A2_REN_i;
assign WEN_A2_i = PORT_A2_WEN_i;
assign BE_A2_i  = PORT_A2_WR_BE;

assign REN_B1_i = PORT_B1_REN_i;
assign WEN_B1_i = PORT_B1_WEN_i;
assign BE_B1_i  = PORT_B1_WR_BE;

assign REN_B2_i = PORT_B2_REN_i;
assign WEN_B2_i = PORT_B2_WEN_i;
assign BE_B2_i  = PORT_B2_WR_BE;

generate
  if (PORT_A1_DWIDTH == 18) begin
    assign PORT_A1_WDATA[PORT_A1_DWIDTH-1:0] = PORT_A1_WR_DATA_i[PORT_A1_DWIDTH-1:0];
  end else if (PORT_A1_DWIDTH == 9) begin
    assign PORT_A1_WDATA = {1'b0, PORT_A1_WR_DATA_i[8], 8'h0, PORT_A1_WR_DATA_i[7:0]};
  end else begin
    assign PORT_A1_WDATA[17:PORT_A1_DWIDTH] = 0;
    assign PORT_A1_WDATA[PORT_A1_DWIDTH-1:0] = PORT_A1_WR_DATA_i[PORT_A1_DWIDTH-1:0];
  end
endgenerate

assign WDATA_A1_i = PORT_A1_WDATA;

generate
  if (PORT_A2_DWIDTH == 18) begin
    assign PORT_A2_WDATA[PORT_A2_DWIDTH-1:0] = PORT_A2_WR_DATA_i[PORT_A2_DWIDTH-1:0];
  end else if (PORT_A2_DWIDTH == 9) begin
    assign PORT_A2_WDATA = {1'b0, PORT_A2_WR_DATA_i[8], 8'h0, PORT_A2_WR_DATA_i[7:0]};
  end else begin
    assign PORT_A2_WDATA[17:PORT_A2_DWIDTH] = 0;
    assign PORT_A2_WDATA[PORT_A2_DWIDTH-1:0] = PORT_A2_WR_DATA_i[PORT_A2_DWIDTH-1:0];
  end
endgenerate

assign WDATA_A2_i = PORT_A2_WDATA;

generate
  if (PORT_A1_DWIDTH == 9) begin
    assign PORT_A1_RDATA = { 9'h0, RDATA_A1_o[16], RDATA_A1_o[7:0]};
  end else begin
    assign PORT_A1_RDATA = RDATA_A1_o;
  end
endgenerate

assign PORT_A1_RD_DATA_o = PORT_A1_RDATA[PORT_A1_DWIDTH-1:0];

generate
  if (PORT_A2_DWIDTH == 9) begin
    assign PORT_A2_RDATA = { 9'h0, RDATA_A2_o[16], RDATA_A2_o[7:0]};
  end else begin
    assign PORT_A2_RDATA = RDATA_A2_o;
  end
endgenerate

assign PORT_A2_RD_DATA_o = PORT_A2_RDATA[PORT_A2_DWIDTH-1:0];

generate
  if (PORT_B1_DWIDTH == 18) begin
    assign PORT_B1_WDATA[PORT_B1_DWIDTH-1:0] = PORT_B1_WR_DATA_i[PORT_B1_DWIDTH-1:0];
  end else if (PORT_B1_DWIDTH == 9) begin
    assign PORT_B1_WDATA = {1'b0, PORT_B1_WR_DATA_i[8], 8'h0, PORT_B1_WR_DATA_i[7:0]};
  end else begin
    assign PORT_B1_WDATA[17:PORT_B1_DWIDTH] = 0;
    assign PORT_B1_WDATA[PORT_B1_DWIDTH-1:0] = PORT_B1_WR_DATA_i[PORT_B1_DWIDTH-1:0];
  end
endgenerate

assign WDATA_B1_i = PORT_B1_WDATA;

generate
  if (PORT_B2_DWIDTH == 18) begin
    assign PORT_B2_WDATA[PORT_B2_DWIDTH-1:0] = PORT_B2_WR_DATA_i[PORT_B2_DWIDTH-1:0];
  end else if (PORT_B2_DWIDTH == 9) begin
    assign PORT_B2_WDATA = {1'b0, PORT_B2_WR_DATA_i[8], 8'h0, PORT_B2_WR_DATA_i[7:0]};
  end else begin
    assign PORT_B2_WDATA[17:PORT_B2_DWIDTH] = 0;
    assign PORT_B2_WDATA[PORT_B2_DWIDTH-1:0] = PORT_B2_WR_DATA_i[PORT_B2_DWIDTH-1:0];
  end
endgenerate

assign WDATA_B2_i = PORT_B2_WDATA;

generate
  if (PORT_B1_DWIDTH == 9) begin
    assign PORT_B1_RDATA = { 9'h0, RDATA_B1_o[16], RDATA_B1_o[7:0]};
  end else begin
    assign PORT_B1_RDATA = RDATA_B1_o;
  end
endgenerate

assign PORT_B1_RD_DATA_o = PORT_B1_RDATA[PORT_B1_DWIDTH-1:0];

generate
  if (PORT_B2_DWIDTH == 9) begin
    assign PORT_B2_RDATA = { 9'h0, RDATA_B2_o[16], RDATA_B2_o[7:0]};
  end else begin
    assign PORT_B2_RDATA = RDATA_B2_o;
  end
endgenerate

assign PORT_B2_RD_DATA_o = PORT_B2_RDATA[PORT_B2_DWIDTH-1:0];

defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b1,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
};

(* is_inferred = 0 *)
(* is_split = 0 *)
(* is_fifo = 0 *)
(* port_a_dwidth = PORT_A1_WRWIDTH *)
(* port_b_dwidth = PORT_B1_WRWIDTH *)
TDP36K _TECHMAP_REPLACE_ (
	.RESET_ni(1'b1),

	.CLK_A1_i(PORT_A1_CLK),
	.ADDR_A1_i({1'b0,PORT_A1_ADDR}),
	.WEN_A1_i(WEN_A1_i),
	.BE_A1_i(BE_A1_i),
	.WDATA_A1_i(WDATA_A1_i),
	.REN_A1_i(REN_A1_i),
	.RDATA_A1_o(RDATA_A1_o),

	.CLK_A2_i(PORT_A2_CLK),
	.ADDR_A2_i(PORT_A2_ADDR),
	.WEN_A2_i(WEN_A2_i),
	.BE_A2_i(BE_A2_i),
	.WDATA_A2_i(WDATA_A2_i),
	.REN_A2_i(REN_A2_i),
	.RDATA_A2_o(RDATA_A2_o),

	.CLK_B1_i(PORT_B1_CLK),
	.ADDR_B1_i({1'b0,PORT_B1_ADDR}),
	.WEN_B1_i(WEN_B1_i),
	.BE_B1_i(BE_B1_i),
	.WDATA_B1_i(WDATA_B1_i),
	.REN_B1_i(REN_B1_i),
	.RDATA_B1_o(RDATA_B1_o),

	.CLK_B2_i(PORT_B2_CLK),
	.ADDR_B2_i(PORT_B2_ADDR),
	.WEN_B2_i(WEN_B2_i),
	.BE_B2_i(BE_B2_i),
	.WDATA_B2_i(WDATA_B2_i),
	.REN_B2_i(REN_B2_i),
	.RDATA_B2_o(RDATA_B2_o),

	.FLUSH1_i(1'b0),
	.FLUSH2_i(1'b0)
);

endmodule


module BRAM2x18_SFIFO (
    DIN1,
    PUSH1,
    POP1,
    CLK1,
    Async_Flush1,
    Overrun_Error1,
    Full_Watermark1,
    Almost_Full1,
    Full1,
    Underrun_Error1,
    Empty_Watermark1,
    Almost_Empty1,
    Empty1,
    DOUT1,
    
    DIN2,
    PUSH2,
    POP2,
    CLK2,
    Async_Flush2,
    Overrun_Error2,
    Full_Watermark2,
    Almost_Full2,
    Full2,
    Underrun_Error2,
    Empty_Watermark2,
    Almost_Empty2,
    Empty2,
    DOUT2
);

  parameter WR1_DATA_WIDTH = 18;
  parameter RD1_DATA_WIDTH = 18;
  
  parameter WR2_DATA_WIDTH = 18;
  parameter RD2_DATA_WIDTH = 18;
  
  parameter UPAE_DBITS1 = 12'd10;
  parameter UPAF_DBITS1 = 12'd10;
  
  parameter UPAE_DBITS2 = 11'd10;
  parameter UPAF_DBITS2 = 11'd10;

  input CLK1;
  input PUSH1, POP1;
  input [WR1_DATA_WIDTH-1:0] DIN1;
  input Async_Flush1;
  output [RD1_DATA_WIDTH-1:0] DOUT1;
  output Almost_Full1, Almost_Empty1;
  output Full1, Empty1;
  output Full_Watermark1, Empty_Watermark1;
  output Overrun_Error1, Underrun_Error1;
  
  input CLK2;
  input PUSH2, POP2;
  input [WR2_DATA_WIDTH-1:0] DIN2;
  input Async_Flush2;
  output [RD2_DATA_WIDTH-1:0] DOUT2;
  output Almost_Full2, Almost_Empty2;
  output Full2, Empty2;
  output Full_Watermark2, Empty_Watermark2;
  output Overrun_Error2, Underrun_Error2;
  
  // Fixed mode settings
  localparam [ 0:0] SYNC_FIFO1_i  = 1'd1;
  localparam [ 0:0] FMODE1_i      = 1'd1;
  localparam [ 0:0] POWERDN1_i    = 1'd0;
  localparam [ 0:0] SLEEP1_i      = 1'd0;
  localparam [ 0:0] PROTECT1_i    = 1'd0;
  localparam [11:0] UPAE1_i       = UPAE_DBITS1;
  localparam [11:0] UPAF1_i       = UPAF_DBITS1;
  
  localparam [ 0:0] SYNC_FIFO2_i  = 1'd1;
  localparam [ 0:0] FMODE2_i      = 1'd1;
  localparam [ 0:0] POWERDN2_i    = 1'd0;
  localparam [ 0:0] SLEEP2_i      = 1'd0;
  localparam [ 0:0] PROTECT2_i    = 1'd0;
  localparam [10:0] UPAE2_i       = UPAE_DBITS2;
  localparam [10:0] UPAF2_i       = UPAF_DBITS2;

  // Width mode function
  function [2:0] mode;
  input integer width;
  case (width)
  1: mode = 3'b101;
  2: mode = 3'b110;
  4: mode = 3'b100;
  8,9: mode = 3'b001;
  16, 18: mode = 3'b010;
  32, 36: mode = 3'b011;
  default: mode = 3'b000;
  endcase
  endfunction
  
  function integer rwmode;
  input integer rwwidth;
  case (rwwidth)
  1: rwmode = 1;
  2: rwmode = 2;
  4: rwmode = 4;
  8,9: rwmode = 9;
  16, 18: rwmode = 18;
  default: rwmode = 18;
  endcase
  endfunction
  
  wire [17:0] in_reg1;
  wire [17:0] out_reg1;
  wire [17:0] fifo1_flags;
  
  wire [17:0] in_reg2;
  wire [17:0] out_reg2;
  wire [17:0] fifo2_flags;
  
  wire Push_Clk1, Pop_Clk1;
  wire Push_Clk2, Pop_Clk2;
  assign Push_Clk1 = CLK1;
  assign Pop_Clk1 = CLK1;
  assign Push_Clk2 = CLK2;
  assign Pop_Clk2 = CLK2;
  
  assign Overrun_Error1 = fifo1_flags[0];
  assign Full_Watermark1 = fifo1_flags[1];
  assign Almost_Full1 = fifo1_flags[2];
  assign Full1 = fifo1_flags[3];
  assign Underrun_Error1 = fifo1_flags[4];
  assign Empty_Watermark1 = fifo1_flags[5];
  assign Almost_Empty1 = fifo1_flags[6];
  assign Empty1 = fifo1_flags[7];
  
  assign Overrun_Error2 = fifo2_flags[0];
  assign Full_Watermark2 = fifo2_flags[1];
  assign Almost_Full2 = fifo2_flags[2];
  assign Full2 = fifo2_flags[3];
  assign Underrun_Error2 = fifo2_flags[4];
  assign Empty_Watermark2 = fifo2_flags[5];
  assign Almost_Empty2 = fifo2_flags[6];
  assign Empty2 = fifo2_flags[7];
  
  localparam [ 2:0] RMODE_A1_i    = mode(WR1_DATA_WIDTH);
  localparam [ 2:0] WMODE_A1_i    = mode(WR1_DATA_WIDTH);
  localparam [ 2:0] RMODE_A2_i    = mode(WR2_DATA_WIDTH);
  localparam [ 2:0] WMODE_A2_i    = mode(WR2_DATA_WIDTH);
  
  localparam [ 2:0] RMODE_B1_i    = mode(RD1_DATA_WIDTH);
  localparam [ 2:0] WMODE_B1_i    = mode(RD1_DATA_WIDTH);
  localparam [ 2:0] RMODE_B2_i    = mode(RD2_DATA_WIDTH);
  localparam [ 2:0] WMODE_B2_i    = mode(RD2_DATA_WIDTH);
  
  localparam PORT_A1_WRWIDTH = rwmode(WR1_DATA_WIDTH);
  localparam PORT_B1_WRWIDTH = rwmode(RD1_DATA_WIDTH);
  localparam PORT_A2_WRWIDTH = rwmode(WR2_DATA_WIDTH);
  localparam PORT_B2_WRWIDTH = rwmode(RD2_DATA_WIDTH);
  
  generate
    if (WR1_DATA_WIDTH == 18) begin
      assign in_reg1[17:0] = DIN1[17:0];
    end else if (WR1_DATA_WIDTH == 9) begin
      assign in_reg1[17:0] = {1'b0, DIN1[8], 8'h0, DIN1[7:0]};
    end else begin
      assign in_reg1[17:WR1_DATA_WIDTH]  = 0;
      assign in_reg1[WR1_DATA_WIDTH-1:0] = DIN1[WR1_DATA_WIDTH-1:0];
    end
  endgenerate     
  
  generate
    if (RD1_DATA_WIDTH == 9) begin
      assign DOUT1[RD1_DATA_WIDTH-1:0] = {out_reg1[16], out_reg1[7:0]};
    end else begin
      assign DOUT1[RD1_DATA_WIDTH-1:0] = out_reg1[RD1_DATA_WIDTH-1:0];
    end
  endgenerate 
  
  generate
    if (WR2_DATA_WIDTH == 18) begin
      assign in_reg2[17:0] = DIN2[17:0];
    end else if (WR2_DATA_WIDTH == 9) begin
      assign in_reg2[17:0] = {1'b0, DIN2[8], 8'h0, DIN2[7:0]};
    end else begin
      assign in_reg2[17:WR2_DATA_WIDTH]  = 0;
      assign in_reg2[WR2_DATA_WIDTH-1:0] = DIN2[WR2_DATA_WIDTH-1:0];
    end
  endgenerate     
  
  generate
    if (RD2_DATA_WIDTH == 9) begin
      assign DOUT2[RD2_DATA_WIDTH-1:0] = {out_reg2[16], out_reg2[7:0]};
    end else begin
      assign DOUT2[RD2_DATA_WIDTH-1:0] = out_reg2[RD2_DATA_WIDTH-1:0];
    end
  endgenerate 
  
  defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b1,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
	};

  (* is_fifo = 1 *) 
  (* sync_fifo = 1 *) 
  (* is_split = 0 *)
  (* is_inferred = 0 *)
  (* port_a_dwidth = PORT_A1_WRWIDTH *)
  (* port_b_dwidth = PORT_B1_WRWIDTH *)
 	TDP36K _TECHMAP_REPLACE_ (
		.RESET_ni(1'b1),
		.WDATA_A1_i(in_reg1[17:0]),
		.WDATA_A2_i(in_reg2[17:0]),
		.RDATA_A1_o(fifo1_flags),
		.RDATA_A2_o(fifo2_flags),
		.ADDR_A1_i(14'h0),
		.ADDR_A2_i(14'h0),
		.CLK_A1_i(Push_Clk1),
		.CLK_A2_i(Push_Clk2),
		.REN_A1_i(1'b1),
		.REN_A2_i(1'b1),
		.WEN_A1_i(PUSH1),
		.WEN_A2_i(PUSH2),
		.BE_A1_i(2'b11),
		.BE_A2_i(2'b11),

		.WDATA_B1_i(18'h0),
		.WDATA_B2_i(18'h0),
		.RDATA_B1_o(out_reg1[17:0]),
		.RDATA_B2_o(out_reg2[17:0]),
		.ADDR_B1_i(14'h0),
		.ADDR_B2_i(14'h0),
		.CLK_B1_i(Pop_Clk1),
		.CLK_B2_i(Pop_Clk2),
		.REN_B1_i(POP1),
		.REN_B2_i(POP2),
		.WEN_B1_i(1'b0),
		.WEN_B2_i(1'b0),
		.BE_B1_i(2'b11),
		.BE_B2_i(2'b11),

		.FLUSH1_i(Async_Flush1),
		.FLUSH2_i(Async_Flush2)
	);

endmodule


module BRAM2x18_AFIFO (
    DIN1,
    PUSH1,
    POP1,
    Push_Clk1,
	Pop_Clk1,
    Async_Flush1,
    Overrun_Error1,
    Full_Watermark1,
    Almost_Full1,
    Full1,
    Underrun_Error1,
    Empty_Watermark1,
    Almost_Empty1,
    Empty1,
    DOUT1,
    
    DIN2,
    PUSH2,
    POP2,
    Push_Clk2,
	Pop_Clk2,
    Async_Flush2,
    Overrun_Error2,
    Full_Watermark2,
    Almost_Full2,
    Full2,
    Underrun_Error2,
    Empty_Watermark2,
    Almost_Empty2,
    Empty2,
    DOUT2
);

  parameter WR1_DATA_WIDTH = 18;
  parameter RD1_DATA_WIDTH = 18;
  
  parameter WR2_DATA_WIDTH = 18;
  parameter RD2_DATA_WIDTH = 18;
  
  parameter UPAE_DBITS1 = 12'd10;
  parameter UPAF_DBITS1 = 12'd10;
  
  parameter UPAE_DBITS2 = 11'd10;
  parameter UPAF_DBITS2 = 11'd10;

  input Push_Clk1, Pop_Clk1;
  input PUSH1, POP1;
  input [WR1_DATA_WIDTH-1:0] DIN1;
  input Async_Flush1;
  output [RD1_DATA_WIDTH-1:0] DOUT1;
  output Almost_Full1, Almost_Empty1;
  output Full1, Empty1;
  output Full_Watermark1, Empty_Watermark1;
  output Overrun_Error1, Underrun_Error1;
  
  input Push_Clk2, Pop_Clk2;
  input PUSH2, POP2;
  input [WR2_DATA_WIDTH-1:0] DIN2;
  input Async_Flush2;
  output [RD2_DATA_WIDTH-1:0] DOUT2;
  output Almost_Full2, Almost_Empty2;
  output Full2, Empty2;
  output Full_Watermark2, Empty_Watermark2;
  output Overrun_Error2, Underrun_Error2;
  
  // Fixed mode settings
  localparam [ 0:0] SYNC_FIFO1_i  = 1'd0;
  localparam [ 0:0] FMODE1_i      = 1'd1;
  localparam [ 0:0] POWERDN1_i    = 1'd0;
  localparam [ 0:0] SLEEP1_i      = 1'd0;
  localparam [ 0:0] PROTECT1_i    = 1'd0;
  localparam [11:0] UPAE1_i       = UPAE_DBITS1;
  localparam [11:0] UPAF1_i       = UPAF_DBITS1;
  
  localparam [ 0:0] SYNC_FIFO2_i  = 1'd0;
  localparam [ 0:0] FMODE2_i      = 1'd1;
  localparam [ 0:0] POWERDN2_i    = 1'd0;
  localparam [ 0:0] SLEEP2_i      = 1'd0;
  localparam [ 0:0] PROTECT2_i    = 1'd0;
  localparam [10:0] UPAE2_i       = UPAE_DBITS2;
  localparam [10:0] UPAF2_i       = UPAF_DBITS2;

  // Width mode function
  function [2:0] mode;
  input integer width;
  case (width)
  1: mode = 3'b101;
  2: mode = 3'b110;
  4: mode = 3'b100;
  8,9: mode = 3'b001;
  16, 18: mode = 3'b010;
  32, 36: mode = 3'b011;
  default: mode = 3'b000;
  endcase
  endfunction
  
  function integer rwmode;
  input integer rwwidth;
  case (rwwidth)
  1: rwmode = 1;
  2: rwmode = 2;
  4: rwmode = 4;
  8,9: rwmode = 9;
  16, 18: rwmode = 18;
  default: rwmode = 18;
  endcase
  endfunction
  
  wire [17:0] in_reg1;
  wire [17:0] out_reg1;
  wire [17:0] fifo1_flags;
  
  wire [17:0] in_reg2;
  wire [17:0] out_reg2;
  wire [17:0] fifo2_flags;
  
  wire Push_Clk1, Pop_Clk1;
  wire Push_Clk2, Pop_Clk2;
  
  assign Overrun_Error1 = fifo1_flags[0];
  assign Full_Watermark1 = fifo1_flags[1];
  assign Almost_Full1 = fifo1_flags[2];
  assign Full1 = fifo1_flags[3];
  assign Underrun_Error1 = fifo1_flags[4];
  assign Empty_Watermark1 = fifo1_flags[5];
  assign Almost_Empty1 = fifo1_flags[6];
  assign Empty1 = fifo1_flags[7];
  
  assign Overrun_Error2 = fifo2_flags[0];
  assign Full_Watermark2 = fifo2_flags[1];
  assign Almost_Full2 = fifo2_flags[2];
  assign Full2 = fifo2_flags[3];
  assign Underrun_Error2 = fifo2_flags[4];
  assign Empty_Watermark2 = fifo2_flags[5];
  assign Almost_Empty2 = fifo2_flags[6];
  assign Empty2 = fifo2_flags[7];
  
  localparam [ 2:0] RMODE_A1_i    = mode(WR1_DATA_WIDTH);
  localparam [ 2:0] WMODE_A1_i    = mode(WR1_DATA_WIDTH);
  localparam [ 2:0] RMODE_A2_i    = mode(WR2_DATA_WIDTH);
  localparam [ 2:0] WMODE_A2_i    = mode(WR2_DATA_WIDTH);
  
  localparam [ 2:0] RMODE_B1_i    = mode(RD1_DATA_WIDTH);
  localparam [ 2:0] WMODE_B1_i    = mode(RD1_DATA_WIDTH);
  localparam [ 2:0] RMODE_B2_i    = mode(RD2_DATA_WIDTH);
  localparam [ 2:0] WMODE_B2_i    = mode(RD2_DATA_WIDTH);
  
  localparam PORT_A1_WRWIDTH = rwmode(WR1_DATA_WIDTH);
  localparam PORT_B1_WRWIDTH = rwmode(RD1_DATA_WIDTH);
  localparam PORT_A2_WRWIDTH = rwmode(WR2_DATA_WIDTH);
  localparam PORT_B2_WRWIDTH = rwmode(RD2_DATA_WIDTH);
  
  generate
    if (WR1_DATA_WIDTH == 18) begin
      assign in_reg1[17:0] = DIN1[17:0];
    end else if (WR1_DATA_WIDTH == 9) begin
      assign in_reg1[17:0] = {1'b0, DIN1[8], 8'h0, DIN1[7:0]};
    end else begin
      assign in_reg1[17:WR1_DATA_WIDTH]  = 0;
      assign in_reg1[WR1_DATA_WIDTH-1:0] = DIN1[WR1_DATA_WIDTH-1:0];
    end
  endgenerate     
  
  generate
    if (RD1_DATA_WIDTH == 9) begin
      assign DOUT1[RD1_DATA_WIDTH-1:0] = {out_reg1[16], out_reg1[7:0]};
    end else begin
      assign DOUT1[RD1_DATA_WIDTH-1:0] = out_reg1[RD1_DATA_WIDTH-1:0];
    end
  endgenerate 
  
  generate
    if (WR2_DATA_WIDTH == 18) begin
      assign in_reg2[17:0] = DIN2[17:0];
    end else if (WR2_DATA_WIDTH == 9) begin
      assign in_reg2[17:0] = {1'b0, DIN2[8], 8'h0, DIN2[7:0]};
    end else begin
      assign in_reg2[17:WR2_DATA_WIDTH]  = 0;
      assign in_reg2[WR2_DATA_WIDTH-1:0] = DIN2[WR2_DATA_WIDTH-1:0];
    end
  endgenerate     
  
  generate
    if (RD2_DATA_WIDTH == 9) begin
      assign DOUT2[RD2_DATA_WIDTH-1:0] = {out_reg2[16], out_reg2[7:0]};
    end else begin
      assign DOUT2[RD2_DATA_WIDTH-1:0] = out_reg2[RD2_DATA_WIDTH-1:0];
    end
  endgenerate 
  
  defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b1,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
	};

  (* is_fifo = 1 *) 
  (* sync_fifo = 0 *) 
  (* is_split = 0 *)
  (* is_inferred = 0 *)
  (* port_a_dwidth = PORT_A1_WRWIDTH *)
  (* port_b_dwidth = PORT_B1_WRWIDTH *)
 	TDP36K _TECHMAP_REPLACE_ (
		.RESET_ni(1'b1),
		.WDATA_A1_i(in_reg1[17:0]),
		.WDATA_A2_i(in_reg2[17:0]),
		.RDATA_A1_o(fifo1_flags),
		.RDATA_A2_o(fifo2_flags),
		.ADDR_A1_i(14'h0),
		.ADDR_A2_i(14'h0),
		.CLK_A1_i(Push_Clk1),
		.CLK_A2_i(Push_Clk2),
		.REN_A1_i(1'b1),
		.REN_A2_i(1'b1),
		.WEN_A1_i(PUSH1),
		.WEN_A2_i(PUSH2),
		.BE_A1_i(2'b11),
		.BE_A2_i(2'b11),

		.WDATA_B1_i(18'h0),
		.WDATA_B2_i(18'h0),
		.RDATA_B1_o(out_reg1[17:0]),
		.RDATA_B2_o(out_reg2[17:0]),
		.ADDR_B1_i(14'h0),
		.ADDR_B2_i(14'h0),
		.CLK_B1_i(Pop_Clk1),
		.CLK_B2_i(Pop_Clk2),
		.REN_B1_i(POP1),
		.REN_B2_i(POP2),
		.WEN_B1_i(1'b0),
		.WEN_B2_i(1'b0),
		.BE_B1_i(2'b11),
		.BE_B2_i(2'b11),

		.FLUSH1_i(Async_Flush1),
		.FLUSH2_i(Async_Flush2)
	);

endmodule