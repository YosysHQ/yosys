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

module \$__QLF_TDP36K (PORT_A_CLK, PORT_A_ADDR, PORT_A_WR_DATA, PORT_A_WR_EN, PORT_A_WR_BE, PORT_A_CLK_EN, PORT_A_RD_DATA,
					   PORT_B_CLK, PORT_B_ADDR, PORT_B_WR_DATA, PORT_B_WR_EN, PORT_B_WR_BE, PORT_B_CLK_EN, PORT_B_RD_DATA);  

parameter INIT = 0;

parameter OPTION_SPLIT = 0;

parameter PORT_A_WIDTH = 1;
parameter PORT_A_WR_BE_WIDTH = 1;

parameter PORT_B_WIDTH = 1;
parameter PORT_B_WR_BE_WIDTH = 1;

input PORT_A_CLK;
input [14:0] PORT_A_ADDR;
input [PORT_A_WIDTH-1:0] PORT_A_WR_DATA;
input PORT_A_WR_EN;
input [PORT_A_WR_BE_WIDTH-1:0] PORT_A_WR_BE;
input PORT_A_CLK_EN;
output [PORT_A_WIDTH-1:0] PORT_A_RD_DATA;

input PORT_B_CLK;
input [14:0] PORT_B_ADDR;
input [PORT_B_WIDTH-1:0] PORT_B_WR_DATA;
input PORT_B_WR_EN;
input [PORT_B_WR_BE_WIDTH-1:0] PORT_B_WR_BE;
input PORT_B_CLK_EN;
output [PORT_B_WIDTH-1:0] PORT_B_RD_DATA;


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

function [36863:0] pack_init;
	integer i;
	reg [35:0] ri;
	for (i = 0; i < (OPTION_SPLIT ? 512 : 1024); i = i + 1) begin
		ri = INIT[i*36 +: 36];
		pack_init[i*36 +: 36] = {ri[35], ri[26], ri[34:27], ri[25:18],
								 ri[17], ri[8], ri[16:9], ri[7:0]};
	end
	if (OPTION_SPLIT)
		pack_init[36863:18432] = 18432'bx;
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


// Set port width mode (In non-split mode A2/B2 is not active. Set same values anyway to match previous behavior.)
localparam [ 2:0] RMODE_A1_i    = mode(PORT_A_WIDTH);
localparam [ 2:0] WMODE_A1_i    = mode(PORT_A_WIDTH);
localparam [ 2:0] RMODE_A2_i    = mode(PORT_A_WIDTH);
localparam [ 2:0] WMODE_A2_i    = mode(PORT_A_WIDTH);

localparam [ 2:0] RMODE_B1_i    = mode(PORT_B_WIDTH);
localparam [ 2:0] WMODE_B1_i    = mode(PORT_B_WIDTH);
localparam [ 2:0] RMODE_B2_i    = mode(PORT_B_WIDTH);
localparam [ 2:0] WMODE_B2_i    = mode(PORT_B_WIDTH);

assign REN_A1_i = PORT_A_CLK_EN;
assign WEN_A1_i = PORT_A_CLK_EN & PORT_A_WR_EN;
assign {BE_A2_i, BE_A1_i} = PORT_A_WR_BE;

assign REN_B1_i = PORT_B_CLK_EN;
assign WEN_B1_i = PORT_B_CLK_EN & PORT_B_WR_EN;
assign {BE_B2_i, BE_B1_i} = PORT_B_WR_BE;

case (PORT_A_WIDTH)
9: assign { WDATA_A1_i[16], WDATA_A1_i[7:0] } = PORT_A_WR_DATA;
18: assign { WDATA_A1_i[17], WDATA_A1_i[15:8], WDATA_A1_i[16], WDATA_A1_i[7:0] } = PORT_A_WR_DATA;
36: assign { WDATA_A2_i[17], WDATA_A2_i[15:8], WDATA_A2_i[16], WDATA_A2_i[7:0], WDATA_A1_i[17], WDATA_A1_i[15:8], WDATA_A1_i[16], WDATA_A1_i[7:0]} = PORT_A_WR_DATA;
default: assign WDATA_A1_i = PORT_A_WR_DATA; // 1,2,4
endcase

case (PORT_B_WIDTH)
9: assign { WDATA_B1_i[16], WDATA_B1_i[7:0] } = PORT_B_WR_DATA;
18: assign { WDATA_B1_i[17], WDATA_B1_i[15:8], WDATA_B1_i[16], WDATA_B1_i[7:0] } = PORT_B_WR_DATA;
36: assign { WDATA_B2_i[17], WDATA_B2_i[15:8], WDATA_B2_i[16], WDATA_B2_i[7:0], WDATA_B1_i[17], WDATA_B1_i[15:8], WDATA_B1_i[16], WDATA_B1_i[7:0]} = PORT_B_WR_DATA;
default: assign WDATA_B1_i = PORT_B_WR_DATA; // 1,2,4
endcase

case (PORT_A_WIDTH)
9: assign PORT_A_RD_DATA = { RDATA_A1_o[16], RDATA_A1_o[7:0] };
18: assign PORT_A_RD_DATA = { RDATA_A1_o[17], RDATA_A1_o[15:8], RDATA_A1_o[16], RDATA_A1_o[7:0] };
36: assign PORT_A_RD_DATA = { RDATA_A2_o[17], RDATA_A2_o[15:8], RDATA_A2_o[16], RDATA_A2_o[7:0], RDATA_A1_o[17], RDATA_A1_o[15:8], RDATA_A1_o[16], RDATA_A1_o[7:0]};
default: assign PORT_A_RD_DATA = RDATA_A1_o; // 1,2,4
endcase

case (PORT_B_WIDTH)
9: assign PORT_B_RD_DATA = { RDATA_B1_o[16], RDATA_B1_o[7:0] };
18: assign PORT_B_RD_DATA = { RDATA_B1_o[17], RDATA_B1_o[15:8], RDATA_B1_o[16], RDATA_B1_o[7:0] };
36: assign PORT_B_RD_DATA = { RDATA_B2_o[17], RDATA_B2_o[15:8], RDATA_B2_o[16], RDATA_B2_o[7:0], RDATA_B1_o[17], RDATA_B1_o[15:8], RDATA_B1_o[16], RDATA_B1_o[7:0]};
default: assign PORT_B_RD_DATA = RDATA_B1_o; // 1,2,4
endcase

defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b0,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
};

(* is_inferred = 1 *)
(* is_split = 0 *)
(* was_split_candidate = OPTION_SPLIT *)
(* port_a_width = PORT_A_WIDTH *)
(* port_b_width = PORT_B_WIDTH *)
TDP36K #(
	.RAM_INIT(pack_init()),
) _TECHMAP_REPLACE_ (
	.RESET_ni(1'b1),

	.CLK_A1_i(PORT_A_CLK),
	.ADDR_A1_i(PORT_A_ADDR),
	.WEN_A1_i(WEN_A1_i),
	.BE_A1_i(BE_A1_i),
	.WDATA_A1_i(WDATA_A1_i),
	.REN_A1_i(REN_A1_i),
	.RDATA_A1_o(RDATA_A1_o),

	.CLK_A2_i(PORT_A_CLK),
	.ADDR_A2_i(PORT_A_ADDR[13:0]),
	.WEN_A2_i(WEN_A1_i),
	.BE_A2_i(BE_A2_i),
	.WDATA_A2_i(WDATA_A2_i),
	.REN_A2_i(REN_A1_i),
	.RDATA_A2_o(RDATA_A2_o),

	.CLK_B1_i(PORT_B_CLK),
	.ADDR_B1_i(PORT_B_ADDR),
	.WEN_B1_i(WEN_B1_i),
	.BE_B1_i(BE_B1_i),
	.WDATA_B1_i(WDATA_B1_i),
	.REN_B1_i(REN_B1_i),
	.RDATA_B1_o(RDATA_B1_o),

	.CLK_B2_i(PORT_B_CLK),
	.ADDR_B2_i(PORT_B_ADDR[13:0]),
	.WEN_B2_i(WEN_B1_i),
	.BE_B2_i(BE_B2_i),
	.WDATA_B2_i(WDATA_B2_i),
	.REN_B2_i(REN_B1_i),
	.RDATA_B2_o(RDATA_B2_o),

	.FLUSH1_i(1'b0),
	.FLUSH2_i(1'b0)
);

endmodule


module \$__QLF_TDP36K_MERGED (...);

parameter INIT1 = 0;

parameter PORT_A1_WIDTH = 1;
parameter PORT_B1_WIDTH = 1;

parameter PORT_A1_WR_BE_WIDTH = 1;
parameter PORT_B1_WR_BE_WIDTH = 1;

input PORT_A1_CLK;
input [14:0] PORT_A1_ADDR;
input [PORT_A1_WIDTH-1:0] PORT_A1_WR_DATA;
input PORT_A1_WR_EN;
input [PORT_A1_WR_BE_WIDTH-1:0] PORT_A1_WR_BE;
input PORT_A1_CLK_EN;
output [PORT_A1_WIDTH-1:0] PORT_A1_RD_DATA;

input PORT_B1_CLK;
input [14:0] PORT_B1_ADDR;
input [PORT_B1_WIDTH-1:0] PORT_B1_WR_DATA;
input PORT_B1_WR_EN;
input [PORT_B1_WR_BE_WIDTH-1:0] PORT_B1_WR_BE;
input PORT_B1_CLK_EN;
output [PORT_B1_WIDTH-1:0] PORT_B1_RD_DATA;

parameter INIT2 = 0;

parameter PORT_A2_WIDTH = 1;
parameter PORT_B2_WIDTH = 1;
parameter PORT_A2_WR_BE_WIDTH = 1;
parameter PORT_B2_WR_BE_WIDTH = 1;

input PORT_A2_CLK;
input [14:0] PORT_A2_ADDR;
input [PORT_A2_WIDTH-1:0] PORT_A2_WR_DATA;
input PORT_A2_WR_EN;
input [PORT_A2_WR_BE_WIDTH-1:0] PORT_A2_WR_BE;
input PORT_A2_CLK_EN;
output [PORT_A2_WIDTH-1:0] PORT_A2_RD_DATA;

input PORT_B2_CLK;
input [14:0] PORT_B2_ADDR;
input [PORT_B2_WIDTH-1:0] PORT_B2_WR_DATA;
input PORT_B2_WR_EN;
input [PORT_B2_WR_BE_WIDTH-1:0] PORT_B2_WR_BE;
input PORT_B2_CLK_EN;
output [PORT_B2_WIDTH-1:0] PORT_B2_RD_DATA;


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
default: mode = 3'b000;
endcase
endfunction

function [36863:0] pack_init;
	integer i;
	reg [35:0] ri;
	for (i = 0; i < 1024; i = i + 1) begin
		ri = {INIT2[i*18 +: 18], INIT1[i*18 +: 18]};
		pack_init[i*36 +: 36] = {ri[35], ri[26], ri[34:27], ri[25:18], ri[17], ri[8], ri[16:9], ri[7:0]};
	end
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


// Set port width mode (In non-split mode A2/B2 is not active. Set same values anyway to match previous behavior.)
localparam [ 2:0] RMODE_A1_i    = mode(PORT_A1_WIDTH);
localparam [ 2:0] WMODE_A1_i    = mode(PORT_A1_WIDTH);
localparam [ 2:0] RMODE_B1_i    = mode(PORT_B1_WIDTH);
localparam [ 2:0] WMODE_B1_i    = mode(PORT_B1_WIDTH);

localparam [ 2:0] RMODE_A2_i    = mode(PORT_A2_WIDTH);
localparam [ 2:0] WMODE_A2_i    = mode(PORT_A2_WIDTH);
localparam [ 2:0] RMODE_B2_i    = mode(PORT_B2_WIDTH);
localparam [ 2:0] WMODE_B2_i    = mode(PORT_B2_WIDTH);

assign REN_A1_i = PORT_A1_CLK_EN;
assign WEN_A1_i = PORT_A1_CLK_EN & PORT_A1_WR_EN;
assign BE_A1_i = PORT_A1_WR_BE;

assign REN_B1_i = PORT_B1_CLK_EN;
assign WEN_B1_i = PORT_B1_CLK_EN & PORT_B1_WR_EN;
assign BE_B1_i = PORT_B1_WR_BE;

assign REN_A2_i = PORT_A2_CLK_EN;
assign WEN_A2_i = PORT_A2_CLK_EN & PORT_A2_WR_EN;
assign BE_A2_i = PORT_A2_WR_BE;

assign REN_B2_i = PORT_B2_CLK_EN;
assign WEN_B2_i = PORT_B2_CLK_EN & PORT_B2_WR_EN;
assign BE_B2_i = PORT_B2_WR_BE;

assign ADDR_A1_i = PORT_A1_ADDR;
assign ADDR_B1_i = PORT_B1_ADDR;
assign ADDR_A2_i = PORT_A2_ADDR;
assign ADDR_B2_i = PORT_B2_ADDR;

case (PORT_A1_WIDTH)
9: assign { WDATA_A1_i[16], WDATA_A1_i[7:0] } = PORT_A1_WR_DATA;
18: assign { WDATA_A1_i[17], WDATA_A1_i[15:8], WDATA_A1_i[16], WDATA_A1_i[7:0] } = PORT_A1_WR_DATA;
default: assign WDATA_A1_i = PORT_A1_WR_DATA; // 1,2,4,8,16
endcase

case (PORT_B1_WIDTH)
9: assign { WDATA_B1_i[16], WDATA_B1_i[7:0] } = PORT_B1_WR_DATA;
18: assign { WDATA_B1_i[17], WDATA_B1_i[15:8], WDATA_B1_i[16], WDATA_B1_i[7:0] } = PORT_B1_WR_DATA;
default: assign WDATA_B1_i = PORT_B1_WR_DATA; // 1,2,4,8,16
endcase

case (PORT_A1_WIDTH)
9: assign PORT_A1_RD_DATA = { RDATA_A1_o[16], RDATA_A1_o[7:0] };
18: assign PORT_A1_RD_DATA = { RDATA_A1_o[17], RDATA_A1_o[15:8], RDATA_A1_o[16], RDATA_A1_o[7:0] };
default: assign PORT_A1_RD_DATA = RDATA_A1_o; // 1,2,4,8,16
endcase

case (PORT_B1_WIDTH)
9: assign PORT_B1_RD_DATA = { RDATA_B1_o[16], RDATA_B1_o[7:0] };
18: assign PORT_B1_RD_DATA = { RDATA_B1_o[17], RDATA_B1_o[15:8], RDATA_B1_o[16], RDATA_B1_o[7:0] };
default: assign PORT_B1_RD_DATA = RDATA_B1_o; // 1,2,4,8,16
endcase

case (PORT_A2_WIDTH)
9: assign { WDATA_A2_i[16], WDATA_A2_i[7:0] } = PORT_A2_WR_DATA;
18: assign { WDATA_A2_i[17], WDATA_A2_i[15:8], WDATA_A2_i[16], WDATA_A2_i[7:0] } = PORT_A2_WR_DATA;
default: assign WDATA_A2_i = PORT_A2_WR_DATA; // 1,2,4,8,16
endcase

case (PORT_B2_WIDTH)
9: assign { WDATA_B2_i[16], WDATA_B2_i[7:0] } = PORT_B2_WR_DATA;
18: assign { WDATA_B2_i[17], WDATA_B2_i[15:8], WDATA_B2_i[16], WDATA_B2_i[7:0] } = PORT_B2_WR_DATA;
default: assign WDATA_B2_i = PORT_B2_WR_DATA; // 1,2,4,8,16
endcase

case (PORT_A2_WIDTH)
9: assign PORT_A2_RD_DATA = { RDATA_A2_o[16], RDATA_A2_o[7:0] };
18: assign PORT_A2_RD_DATA = { RDATA_A2_o[17], RDATA_A2_o[15:8], RDATA_A2_o[16], RDATA_A2_o[7:0] };
default: assign PORT_A2_RD_DATA = RDATA_A2_o; // 1,2,4,8,16
endcase

case (PORT_B2_WIDTH)
9: assign PORT_B2_RD_DATA = { RDATA_B2_o[16], RDATA_B2_o[7:0] };
18: assign PORT_B2_RD_DATA = { RDATA_B2_o[17], RDATA_B2_o[15:8], RDATA_B2_o[16], RDATA_B2_o[7:0] };
default: assign PORT_B2_RD_DATA = RDATA_B2_o; // 1,2,4,8,16
endcase

defparam _TECHMAP_REPLACE_.MODE_BITS = {1'b1,
			UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
			UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
		};

(* is_inferred = 1 *)
(* is_split = 1 *)
(* port_a1_width = PORT_A1_WIDTH *)
(* port_a2_width = PORT_A2_WIDTH *)
(* port_b1_width = PORT_B1_WIDTH *)
(* port_b2_width = PORT_B2_WIDTH *)
TDP36K #(
	.RAM_INIT(pack_init()),
) _TECHMAP_REPLACE_ (
	.RESET_ni(1'b1),
	.WDATA_A1_i(WDATA_A1_i),
	.WDATA_A2_i(WDATA_A2_i),
	.RDATA_A1_o(RDATA_A1_o),
	.RDATA_A2_o(RDATA_A2_o),
	.ADDR_A1_i(ADDR_A1_i),
	.ADDR_A2_i(ADDR_A2_i),
	.CLK_A1_i(PORT_A1_CLK),
	.CLK_A2_i(PORT_A2_CLK),
	.REN_A1_i(REN_A1_i),
	.REN_A2_i(REN_A2_i),
	.WEN_A1_i(WEN_A1_i),
	.WEN_A2_i(WEN_A2_i),
	.BE_A1_i(BE_A1_i),
	.BE_A2_i(BE_A2_i),

	.WDATA_B1_i(WDATA_B1_i),
	.WDATA_B2_i(WDATA_B2_i),
	.RDATA_B1_o(RDATA_B1_o),
	.RDATA_B2_o(RDATA_B2_o),
	.ADDR_B1_i(ADDR_B1_i),
	.ADDR_B2_i(ADDR_B2_i),
	.CLK_B1_i(PORT_B1_CLK),
	.CLK_B2_i(PORT_B2_CLK),
	.REN_B1_i(REN_B1_i),
	.REN_B2_i(REN_B2_i),
	.WEN_B1_i(WEN_B1_i),
	.WEN_B2_i(WEN_B2_i),
	.BE_B1_i(BE_B1_i),
	.BE_B2_i(BE_B2_i),

	.FLUSH1_i(1'b0),
	.FLUSH2_i(1'b0)
);

endmodule