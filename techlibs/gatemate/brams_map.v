/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Cologne Chip AG <support@colognechip.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

module \$__CC_BRAM_20K_SDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

	parameter CFG_ABITS = 14;
	parameter CFG_DBITS = 40;
	parameter CFG_ENABLE_A = 1;
	parameter CFG_ENABLE_B = 1;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	// 512 x 40 bit
	parameter [20479:0] INIT = 20480'b0;

	input CLK2;
	input CLK3;

	// write side of the memory
	input [15:0] A1ADDR;
	input [39:0] A1DATA;
	input [39:0] A1EN;

	// read side of the memory
	input [15:0] B1ADDR;
	output [39:0] B1DATA;
	input [0:0] B1EN;

	// unconnected signals
	wire ECC_1B_ERR, ECC_2B_ERR;

	// internal signals
	wire [15:0] ADDRA = {A1ADDR, 7'b0};
	wire [15:0] ADDRB = {B1ADDR, 7'b0};

	localparam INIT_CHUNK_SIZE = 320;

	function [319:0] permute_init;
		input [INIT_CHUNK_SIZE-1:0] chunk;
		integer i;
		begin
			permute_init = chunk;
		end
	endfunction

	CC_BRAM_20K #(
		`include "brams_init_20.vh"
		.LOC("UNPLACED"),
		.A_RD_WIDTH(0), .B_RD_WIDTH(CFG_DBITS),
		.A_WR_WIDTH(CFG_DBITS), .B_WR_WIDTH(0),
		.RAM_MODE("SDP"),
		.A_WR_MODE("NO_CHANGE"), .B_WR_MODE("NO_CHANGE"),
		.A_CLK_INV(!CLKPOL2), .B_CLK_INV(!CLKPOL3),
		.A_EN_INV(1'b0), .B_EN_INV(1'b0),
		.A_WE_INV(1'b0), .B_WE_INV(1'b0),
		.A_DO_REG(1'b0), .B_DO_REG(1'b0),
		.ECC_EN(1'b0)
	) _TECHMAP_REPLACE_ (
		.A_DO(B1DATA[19:0]),
		.B_DO(B1DATA[39:20]),
		.ECC_1B_ERR(ECC_1B_ERR),
		.ECC_2B_ERR(ECC_2B_ERR),
		.A_CLK(CLK2),
		.B_CLK(CLK3),
		.A_EN(1'b1),
		.B_EN(B1EN),
		.A_WE(|A1EN),
		.B_WE(1'b0),
		.A_ADDR(ADDRA),
		.B_ADDR(ADDRB),
		.A_DI(A1DATA[19:0]),
		.B_DI(A1DATA[39:20]),
		.A_BM(A1EN[19:0]),
		.B_BM(A1EN[39:20])
	);

endmodule


module \$__CC_BRAM_40K_SDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

	parameter CFG_ABITS = 15;
	parameter CFG_DBITS = 80;
	parameter CFG_ENABLE_A = 1;
	parameter CFG_ENABLE_B = 1;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	// 512 x 80 bit
	parameter [40959:0] INIT = 40960'b0;

	input CLK2;
	input CLK3;

	// write side of the memory
	input [15:0] A1ADDR;
	input [79:0] A1DATA;
	input [79:0] A1EN;

	// read side of the memory
	input [15:0] B1ADDR;
	output [79:0] B1DATA;
	input [0:0] B1EN;

	// unconnected signals
	wire A_ECC_1B_ERR, B_ECC_1B_ERR, A_ECC_2B_ERR, B_ECC_2B_ERR;

	// internal signals
	wire [15:0] ADDRA = {A1ADDR, 7'b0};
	wire [15:0] ADDRB = {B1ADDR, 7'b0};

	localparam INIT_CHUNK_SIZE = 320;

	function [319:0] permute_init;
		input [INIT_CHUNK_SIZE-1:0] chunk;
		integer i;
		begin
			permute_init = chunk;
		end
	endfunction

	CC_BRAM_40K #(
		`define INIT_LOWER
		`include "brams_init_40.vh"
		`undef INIT_LOWER
		.LOC("UNPLACED"),
		.CAS("NONE"),
		.A_RD_WIDTH(0), .B_RD_WIDTH(CFG_DBITS),
		.A_WR_WIDTH(CFG_DBITS), .B_WR_WIDTH(0),
		.RAM_MODE("SDP"),
		.A_WR_MODE("NO_CHANGE"), .B_WR_MODE("NO_CHANGE"),
		.A_CLK_INV(!CLKPOL2), .B_CLK_INV(!CLKPOL3),
		.A_EN_INV(1'b0), .B_EN_INV(1'b0),
		.A_WE_INV(1'b0), .B_WE_INV(1'b0),
		.A_DO_REG(1'b0), .B_DO_REG(1'b0),
		.A_ECC_EN(1'b0), .B_ECC_EN(1'b0)
	) _TECHMAP_REPLACE_ (
		.A_DO(B1DATA[39:0]),
		.B_DO(B1DATA[79:40]),
		.A_ECC_1B_ERR(A_ECC_1B_ERR),
		.B_ECC_1B_ERR(B_ECC_1B_ERR),
		.A_ECC_2B_ERR(A_ECC_2B_ERR),
		.B_ECC_2B_ERR(B_ECC_2B_ERR),
		.A_CLK(CLK2),
		.B_CLK(CLK3),
		.A_EN(1'b1),
		.B_EN(B1EN),
		.A_WE(|A1EN),
		.B_WE(1'b0),
		.A_ADDR(ADDRA),
		.B_ADDR(ADDRB),
		.A_DI(A1DATA[39:0]),
		.B_DI(A1DATA[79:40]),
		.A_BM(A1EN[39:0]),
		.B_BM(A1EN[79:40])
	);

endmodule


module \$__CC_BRAM_20K_TDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

	parameter CFG_ABITS = 14;
	parameter CFG_DBITS = 20;
	parameter CFG_ENABLE_A = 1;
	parameter CFG_ENABLE_B = 1;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	// 512 x 40 bit
	parameter [20479:0] INIT = 20480'b0;

	input CLK2;
	input CLK3;

	// write side of the memory
	input [15:0] A1ADDR;
	input [19:0] A1DATA;
	input [19:0] A1EN;

	// read side of the memory
	input [15:0] B1ADDR;
	output [19:0] B1DATA;
	input [0:0] B1EN;

	// unconnected signals
	wire [19:0] A_DO;
	wire ECC_1B_ERR, ECC_2B_ERR;

	localparam INIT_CHUNK_SIZE = (CFG_DBITS <= 2) ? 256 : 320;

	function [319:0] permute_init;
		input [INIT_CHUNK_SIZE-1:0] chunk;
		integer i;
		begin
			if (CFG_DBITS <= 2) begin
				for (i = 0; i < 64; i = i + 1) begin
					permute_init[i * 5 +: 5] = {1'b0, chunk[i * 4 +: 4]};
				end
			end else begin
				permute_init = chunk;
			end
		end
	endfunction

	// internal signals
	generate
		wire [15:0] ADDRA;
		wire [15:0] ADDRB;

		if (CFG_DBITS == 1) begin: blk
			assign ADDRA = {A1ADDR[13:5], 1'b0, A1ADDR[4:0], 1'b0};
			assign ADDRB = {B1ADDR[13:5], 1'b0, B1ADDR[4:0], 1'b0};
		end
		else if (CFG_DBITS == 2) begin: blk
			assign ADDRA = {A1ADDR[12:4], 1'b0, A1ADDR[3:0], 2'b0};
			assign ADDRB = {B1ADDR[12:4], 1'b0, B1ADDR[3:0], 2'b0};
		end
		else if (CFG_DBITS == 5) begin: blk
			assign ADDRA = {A1ADDR[11:3], 1'b0, A1ADDR[2:0], 3'b0};
			assign ADDRB = {B1ADDR[11:3], 1'b0, B1ADDR[2:0], 3'b0};
		end
		else if (CFG_DBITS == 10) begin: blk
			assign ADDRA = {A1ADDR[10:2], 1'b0, A1ADDR[1:0], 4'b0};
			assign ADDRB = {B1ADDR[10:2], 1'b0, B1ADDR[1:0], 4'b0};
		end
		else if (CFG_DBITS == 20) begin: blk
			assign ADDRA = {A1ADDR[9:1], 1'b0, A1ADDR[0], 5'b0};
			assign ADDRB = {B1ADDR[9:1], 1'b0, B1ADDR[0], 5'b0};
		end

		CC_BRAM_20K #(
			`include "brams_init_20.vh"
			.LOC("UNPLACED"),
			.A_RD_WIDTH(0), .B_RD_WIDTH(CFG_DBITS),
			.A_WR_WIDTH(CFG_DBITS), .B_WR_WIDTH(0),
			.RAM_MODE("TDP"),
			.A_WR_MODE("NO_CHANGE"), .B_WR_MODE("NO_CHANGE"),
			.A_CLK_INV(!CLKPOL2), .B_CLK_INV(!CLKPOL3),
			.A_EN_INV(1'b0), .B_EN_INV(1'b0),
			.A_WE_INV(1'b0), .B_WE_INV(1'b0),
			.A_DO_REG(1'b0), .B_DO_REG(1'b0),
			.ECC_EN(1'b0)
		) _TECHMAP_REPLACE_ (
			.A_DO(A_DO),
			.B_DO(B1DATA),
			.ECC_1B_ERR(ECC_1B_ERR),
			.ECC_2B_ERR(ECC_2B_ERR),
			.A_CLK(CLK2),
			.B_CLK(CLK3),
			.A_EN(1'b1),
			.B_EN(B1EN),
			.A_WE(|A1EN),
			.B_WE(1'b0),
			.A_ADDR(ADDRA),
			.B_ADDR(ADDRB),
			.A_DI(A1DATA),
			.B_DI(20'b0),
			.A_BM(A1EN),
			.B_BM(20'b0)
		);
	endgenerate

endmodule


module \$__CC_BRAM_40K_TDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

	parameter CFG_ABITS = 15;
	parameter CFG_DBITS = 40;
	parameter CFG_ENABLE_A = 1;
	parameter CFG_ENABLE_B = 1;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	// 512 x 80 bit
	parameter [40959:0] INIT = 40960'b0;

	input CLK2;
	input CLK3;

	// write side of the memory
	input [15:0] A1ADDR;
	input [39:0] A1DATA;
	input [39:0] A1EN;

	// read side of the memory
	input [15:0] B1ADDR;
	output [39:0] B1DATA;
	input [0:0] B1EN;

	// unconnected signals
	wire [39:0] A_DO;
	wire A_ECC_1B_ERR, B_ECC_1B_ERR, A_ECC_2B_ERR, B_ECC_2B_ERR;

	localparam INIT_CHUNK_SIZE = (CFG_DBITS <= 2) ? 256 : 320;

	function [319:0] permute_init;
		input [INIT_CHUNK_SIZE-1:0] chunk;
		integer i;
		begin
			if (CFG_DBITS <= 2) begin
				for (i = 0; i < 64; i = i + 1) begin
					permute_init[i * 5 +: 5] = {1'b0, chunk[i * 4 +: 4]};
				end
			end else begin
				permute_init = chunk;
			end
		end
	endfunction

	generate
		wire [15:0] ADDRA;
		wire [15:0] ADDRB;

		if (CFG_DBITS == 1) begin
			assign ADDRA = {A1ADDR, 1'b0};
			assign ADDRB = {B1ADDR, 1'b0};
		end
		else if (CFG_DBITS == 2) begin
			assign ADDRA = {A1ADDR, 2'b0};
			assign ADDRB = {B1ADDR, 2'b0};
		end
		else if (CFG_DBITS == 5) begin
			assign ADDRA = {A1ADDR, 3'b0};
			assign ADDRB = {B1ADDR, 3'b0};
		end
		else if (CFG_DBITS == 10) begin
			assign ADDRA = {A1ADDR, 4'b0};
			assign ADDRB = {B1ADDR, 4'b0};
		end
		else if (CFG_DBITS == 20) begin
			assign ADDRA = {A1ADDR, 5'b0};
			assign ADDRB = {B1ADDR, 5'b0};
		end
		else if (CFG_DBITS == 40) begin
			assign ADDRA = {A1ADDR, 6'b0};
			assign ADDRB = {B1ADDR, 6'b0};
		end

		CC_BRAM_40K #(
			`define INIT_LOWER
			`include "brams_init_40.vh"
			`undef INIT_LOWER
			.LOC("UNPLACED"),
			.CAS("NONE"),
			.A_RD_WIDTH(0), .B_RD_WIDTH(CFG_DBITS),
			.A_WR_WIDTH(CFG_DBITS), .B_WR_WIDTH(0),
			.RAM_MODE("TDP"),
			.A_WR_MODE("NO_CHANGE"), .B_WR_MODE("NO_CHANGE"),
			.A_CLK_INV(!CLKPOL2), .B_CLK_INV(!CLKPOL3),
			.A_EN_INV(1'b0), .B_EN_INV(1'b0),
			.A_WE_INV(1'b0), .B_WE_INV(1'b0),
			.A_DO_REG(1'b0), .B_DO_REG(1'b0),
			.A_ECC_EN(1'b0), .B_ECC_EN(1'b0)
		) _TECHMAP_REPLACE_ (
			.A_DO(A_DO),
			.B_DO(B1DATA),
			.A_ECC_1B_ERR(A_ECC_1B_ERR),
			.B_ECC_1B_ERR(B_ECC_1B_ERR),
			.A_ECC_2B_ERR(A_ECC_2B_ERR),
			.B_ECC_2B_ERR(B_ECC_2B_ERR),
			.A_CLK(CLK2),
			.B_CLK(CLK3),
			.A_EN(1'b1),
			.B_EN(B1EN),
			.A_WE(|A1EN),
			.B_WE(1'b0),
			.A_ADDR(ADDRA),
			.B_ADDR(ADDRB),
			.A_DI(A1DATA),
			.B_DI(40'b0),
			.A_BM(A1EN),
			.B_BM(40'b0)
		);
	endgenerate

endmodule


module \$__CC_BRAM_CASCADE (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);

	parameter CFG_ABITS = 16;
	parameter CFG_DBITS = 1;
	parameter CFG_ENABLE_A = 1;
	parameter CFG_ENABLE_B = 1;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;

	// 64K x 1
	parameter [65535:0] INIT = 65535'b0;

	input CLK2;
	input CLK3;

	// write side of the memory
	input [15:0] A1ADDR;
	input [39:0] A1DATA;
	input [39:0] A1EN;

	// read side of the memory
	input [15:0] B1ADDR;
	output [39:0] B1DATA;
	input [0:0] B1EN;

	// cascade signals
	wire A_CAS, B_CAS;

	// unconnected signals
	wire [39:0] A_UP_DO;
	wire A_ECC_1B_ERR, B_ECC_1B_ERR, A_ECC_2B_ERR, B_ECC_2B_ERR;

	localparam INIT_CHUNK_SIZE = 256;

	function [319:0] permute_init;
		input [INIT_CHUNK_SIZE-1:0] chunk;
		integer i;
		begin
			for (i = 0; i < 64; i = i + 1) begin
				permute_init[i * 5 +: 5] = {1'b0, chunk[i * 4 +: 4]};
			end
		end
	endfunction

	generate
		CC_BRAM_40K #(
			`define INIT_UPPER
			`include "brams_init_40.vh" // INIT_80 .. INIT_FF
			`undef INIT_UPPER
			.LOC("UNPLACED"),
			.CAS("UPPER"),
			.A_RD_WIDTH(0), .B_RD_WIDTH(CFG_DBITS),
			.A_WR_WIDTH(CFG_DBITS), .B_WR_WIDTH(0),
			.RAM_MODE("TDP"),
			.A_WR_MODE("NO_CHANGE"), .B_WR_MODE("NO_CHANGE"),
			.A_CLK_INV(!CLKPOL2), .B_CLK_INV(!CLKPOL3),
			.A_EN_INV(1'b0), .B_EN_INV(1'b0),
			.A_WE_INV(1'b0), .B_WE_INV(1'b0),
			.A_DO_REG(1'b0), .B_DO_REG(1'b0),
			.A_ECC_EN(1'b0), .B_ECC_EN(1'b0)
		) upper_cell (
			.A_CI(A_CAS),
			.B_CI(B_CAS),
			.A_DO(A_UP_DO),
			.B_DO(B1DATA),
			.A_ECC_1B_ERR(A_ECC_1B_ERR),
			.B_ECC_1B_ERR(B_ECC_1B_ERR),
			.A_ECC_2B_ERR(A_ECC_2B_ERR),
			.B_ECC_2B_ERR(B_ECC_2B_ERR),
			.A_CLK(CLK2),
			.B_CLK(CLK3),
			.A_EN(1'b1),
			.B_EN(B1EN),
			.A_WE(|A1EN),
			.B_WE(1'b0),
			.A_ADDR(A1ADDR),
			.B_ADDR(B1ADDR),
			.A_DI(A1DATA),
			.B_DI(40'b0),
			.A_BM(A1EN),
			.B_BM(40'b0)
		);

		CC_BRAM_40K #(
			`define INIT_LOWER
			`include "brams_init_40.vh" // INIT_00 .. INIT_7F
			`undef INIT_LOWER
			.LOC("UNPLACED"),
			.CAS("LOWER"),
			.A_RD_WIDTH(0), .B_RD_WIDTH(CFG_DBITS),
			.A_WR_WIDTH(CFG_DBITS), .B_WR_WIDTH(0),
			.RAM_MODE("TDP"),
			.A_WR_MODE("NO_CHANGE"), .B_WR_MODE("NO_CHANGE"),
			.A_CLK_INV(!CLKPOL2), .B_CLK_INV(!CLKPOL3),
			.A_EN_INV(1'b0), .B_EN_INV(1'b0),
			.A_WE_INV(1'b0), .B_WE_INV(1'b0),
			.A_DO_REG(1'b0), .B_DO_REG(1'b0),
			.A_ECC_EN(1'b0), .B_ECC_EN(1'b0)
		) lower_cell (
			.A_CI(),
			.B_CI(),
			.A_CO(A_CAS),
			.B_CO(B_CAS),
			.A_CLK(CLK2),
			.B_CLK(CLK3),
			.A_EN(1'b1),
			.B_EN(B1EN),
			.A_WE(|A1EN),
			.B_WE(1'b0),
			.A_ADDR(A1ADDR),
			.B_ADDR(B1ADDR),
			.A_DI(A1DATA),
			.B_DI(40'b0),
			.A_BM(A1EN),
			.B_BM(40'b0)
		);
	endgenerate

endmodule
