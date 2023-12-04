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
`timescale 1ns /10ps

`default_nettype none

module TDP36K (
		RESET_ni,
		WEN_A1_i,
		WEN_B1_i,
		REN_A1_i,
		REN_B1_i,
		CLK_A1_i,
		CLK_B1_i,
		BE_A1_i,
		BE_B1_i,
		ADDR_A1_i,
		ADDR_B1_i,
		WDATA_A1_i,
		WDATA_B1_i,
		RDATA_A1_o,
		RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,
		WEN_B2_i,
		REN_A2_i,
		REN_B2_i,
		CLK_A2_i,
		CLK_B2_i,
		BE_A2_i,
		BE_B2_i,
		ADDR_A2_i,
		ADDR_B2_i,
		WDATA_A2_i,
		WDATA_B2_i,
		RDATA_A2_o,
		RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		// First 18K RAMFIFO (41 bits)
		localparam [ 0:0] SYNC_FIFO1_i  = MODE_BITS[0];
		localparam [ 2:0] RMODE_A1_i    = MODE_BITS[3 : 1];
		localparam [ 2:0] RMODE_B1_i    = MODE_BITS[6 : 4];
		localparam [ 2:0] WMODE_A1_i    = MODE_BITS[9 : 7];
		localparam [ 2:0] WMODE_B1_i    = MODE_BITS[12:10];
		localparam [ 0:0] FMODE1_i      = MODE_BITS[13];
		localparam [ 0:0] POWERDN1_i    = MODE_BITS[14];
		localparam [ 0:0] SLEEP1_i      = MODE_BITS[15];
		localparam [ 0:0] PROTECT1_i    = MODE_BITS[16];
		localparam [11:0] UPAE1_i       = MODE_BITS[28:17];
		localparam [11:0] UPAF1_i       = MODE_BITS[40:29];

		// Second 18K RAMFIFO (39 bits)
		localparam [ 0:0] SYNC_FIFO2_i  = MODE_BITS[41];
		localparam [ 2:0] RMODE_A2_i    = MODE_BITS[44:42];
		localparam [ 2:0] RMODE_B2_i    = MODE_BITS[47:45];
		localparam [ 2:0] WMODE_A2_i    = MODE_BITS[50:48];
		localparam [ 2:0] WMODE_B2_i    = MODE_BITS[53:51];
		localparam [ 0:0] FMODE2_i      = MODE_BITS[54];
		localparam [ 0:0] POWERDN2_i    = MODE_BITS[55];
		localparam [ 0:0] SLEEP2_i      = MODE_BITS[56];
		localparam [ 0:0] PROTECT2_i    = MODE_BITS[57];
		localparam [10:0] UPAE2_i       = MODE_BITS[68:58];
		localparam [10:0] UPAF2_i       = MODE_BITS[79:69];

		// Split (1 bit)
		localparam [ 0:0] SPLIT_i       = MODE_BITS[80];

		parameter [1024*36-1:0] RAM_INIT = 36864'bx;

		input wire RESET_ni;
		input wire WEN_A1_i;
		input wire WEN_B1_i;
		input wire REN_A1_i;
		input wire REN_B1_i;
		(* clkbuf_sink *)
		input wire CLK_A1_i;
		(* clkbuf_sink *)
		input wire CLK_B1_i;
		input wire [1:0] BE_A1_i;
		input wire [1:0] BE_B1_i;
		input wire [14:0] ADDR_A1_i;
		input wire [14:0] ADDR_B1_i;
		input wire [17:0] WDATA_A1_i;
		input wire [17:0] WDATA_B1_i;
		output reg [17:0] RDATA_A1_o;
		output reg [17:0] RDATA_B1_o;
		input wire FLUSH1_i;
		input wire WEN_A2_i;
		input wire WEN_B2_i;
		input wire REN_A2_i;
		input wire REN_B2_i;
		(* clkbuf_sink *)
		input wire CLK_A2_i;
		(* clkbuf_sink *)
		input wire CLK_B2_i;
		input wire [1:0] BE_A2_i;
		input wire [1:0] BE_B2_i;
		input wire [13:0] ADDR_A2_i;
		input wire [13:0] ADDR_B2_i;
		input wire [17:0] WDATA_A2_i;
		input wire [17:0] WDATA_B2_i;
		output reg [17:0] RDATA_A2_o;
		output reg [17:0] RDATA_B2_o;
		input wire FLUSH2_i;

		function [18431:0] split_init;
			input index;
			integer i;
			for (i = 0; i < 1024; i = i + 1) begin
				split_init[i * 18 +: 18] = RAM_INIT[i * 36 + index * 18 +: 18];
			end
		endfunction

		wire EMPTY2;
		wire EPO2;
		wire EWM2;
		wire FULL2;
		wire FMO2;
		wire FWM2;
		wire EMPTY1;
		wire EPO1;
		wire EWM1;
		wire FULL1;
		wire FMO1;
		wire FWM1;
		wire UNDERRUN1;
		wire OVERRUN1;
		wire UNDERRUN2;
		wire OVERRUN2;
		wire UNDERRUN3;
		wire OVERRUN3;
		wire EMPTY3;
		wire EPO3;
		wire EWM3;
		wire FULL3;
		wire FMO3;
		wire FWM3;
		wire ram_fmode1;
		wire ram_fmode2;
		wire [17:0] ram_rdata_a1;
		wire [17:0] ram_rdata_b1;
		wire [17:0] ram_rdata_a2;
		wire [17:0] ram_rdata_b2;
		reg [17:0] ram_wdata_a1;
		reg [17:0] ram_wdata_b1;
		reg [17:0] ram_wdata_a2;
		reg [17:0] ram_wdata_b2;
		reg [14:0] laddr_a1;
		reg [14:0] laddr_b1;
		wire [13:0] ram_addr_a1;
		wire [13:0] ram_addr_b1;
		wire [13:0] ram_addr_a2;
		wire [13:0] ram_addr_b2;
		wire smux_clk_a1;
		wire smux_clk_b1;
		wire smux_clk_a2;
		wire smux_clk_b2;
		reg [1:0] ram_be_a1;
		reg [1:0] ram_be_a2;
		reg [1:0] ram_be_b1;
		reg [1:0] ram_be_b2;
		wire [2:0] ram_rmode_a1;
		wire [2:0] ram_wmode_a1;
		wire [2:0] ram_rmode_b1;
		wire [2:0] ram_wmode_b1;
		wire [2:0] ram_rmode_a2;
		wire [2:0] ram_wmode_a2;
		wire [2:0] ram_rmode_b2;
		wire [2:0] ram_wmode_b2;
		wire ram_ren_a1;
		wire ram_ren_b1;
		wire ram_ren_a2;
		wire ram_ren_b2;
		wire ram_wen_a1;
		wire ram_wen_b1;
		wire ram_wen_a2;
		wire ram_wen_b2;
		wire ren_o;
		wire [11:0] ff_raddr;
		wire [11:0] ff_waddr;
		reg [35:0] fifo_rdata;
		wire [1:0] fifo_rmode;
		wire [1:0] fifo_wmode;
		wire [1:0] bwl;
		wire [17:0] pl_dout0;
		wire [17:0] pl_dout1;
		wire sclk_a1;
		wire sclk_b1;
		wire sclk_a2;
		wire sclk_b2;
		wire sreset;
		wire flush1;
		wire flush2;
		assign sreset = RESET_ni;
		assign flush1 = ~FLUSH1_i;
		assign flush2 = ~FLUSH2_i;
		assign ram_fmode1 = FMODE1_i & SPLIT_i;
		assign ram_fmode2 = FMODE2_i & SPLIT_i;
		assign smux_clk_a1 = CLK_A1_i;
		assign smux_clk_b1 = (FMODE1_i ? (SYNC_FIFO1_i ? CLK_A1_i : CLK_B1_i) : CLK_B1_i);
		assign smux_clk_a2 = (SPLIT_i ? CLK_A2_i : CLK_A1_i);
		assign smux_clk_b2 = (SPLIT_i ? (FMODE2_i ? (SYNC_FIFO2_i ? CLK_A2_i : CLK_B2_i) : CLK_B2_i) : (FMODE1_i ? (SYNC_FIFO1_i ? CLK_A1_i : CLK_B1_i) : CLK_B1_i));
		assign sclk_a1 = smux_clk_a1;
		assign sclk_a2 = smux_clk_a2;
		assign sclk_b1 = smux_clk_b1;
		assign sclk_b2 = smux_clk_b2;
		assign ram_ren_a1 = (SPLIT_i ? REN_A1_i : (FMODE1_i ? 0 : REN_A1_i));
		assign ram_ren_a2 = (SPLIT_i ? REN_A2_i : (FMODE1_i ? 0 : REN_A1_i));
		assign ram_ren_b1 = (SPLIT_i ? REN_B1_i : (FMODE1_i ? ren_o : REN_B1_i));
		assign ram_ren_b2 = (SPLIT_i ? REN_B2_i : (FMODE1_i ? ren_o : REN_B1_i));
		localparam MODE_36 = 3'b011;
		assign ram_wen_a1 = (SPLIT_i ? WEN_A1_i : (FMODE1_i ? ~FULL3 & WEN_A1_i : (WMODE_A1_i == MODE_36 ? WEN_A1_i : WEN_A1_i & ~ADDR_A1_i[4])));
		assign ram_wen_a2 = (SPLIT_i ? WEN_A2_i : (FMODE1_i ? ~FULL3 & WEN_A1_i : (WMODE_A1_i == MODE_36 ? WEN_A1_i : WEN_A1_i & ADDR_A1_i[4])));
		assign ram_wen_b1 = (SPLIT_i ? WEN_B1_i : (WMODE_B1_i == MODE_36 ? WEN_B1_i : WEN_B1_i & ~ADDR_B1_i[4]));
		assign ram_wen_b2 = (SPLIT_i ? WEN_B2_i : (WMODE_B1_i == MODE_36 ? WEN_B1_i : WEN_B1_i & ADDR_B1_i[4]));
		assign ram_addr_a1 = (SPLIT_i ? ADDR_A1_i[13:0] : (FMODE1_i ? {ff_waddr[11:2], ff_waddr[0], 3'b000} : {ADDR_A1_i[14:5], ADDR_A1_i[3:0]}));
		assign ram_addr_b1 = (SPLIT_i ? ADDR_B1_i[13:0] : (FMODE1_i ? {ff_raddr[11:2], ff_raddr[0], 3'b000} : {ADDR_B1_i[14:5], ADDR_B1_i[3:0]}));
		assign ram_addr_a2 = (SPLIT_i ? ADDR_A2_i[13:0] : (FMODE1_i ? {ff_waddr[11:2], ff_waddr[0], 3'b000} : {ADDR_A1_i[14:5], ADDR_A1_i[3:0]}));
		assign ram_addr_b2 = (SPLIT_i ? ADDR_B2_i[13:0] : (FMODE1_i ? {ff_raddr[11:2], ff_raddr[0], 3'b000} : {ADDR_B1_i[14:5], ADDR_B1_i[3:0]}));
		assign bwl = (SPLIT_i ? ADDR_A1_i[4:3] : (FMODE1_i ? ff_waddr[1:0] : ADDR_A1_i[4:3]));
		localparam MODE_18 = 3'b010;
		localparam MODE_9 = 3'b001;
		always @(*) begin : WDATA_SEL
				case (SPLIT_i)
						1: begin
								ram_wdata_a1 = WDATA_A1_i;
								ram_wdata_a2 = WDATA_A2_i;
								ram_wdata_b1 = WDATA_B1_i;
								ram_wdata_b2 = WDATA_B2_i;
								ram_be_a2 = BE_A2_i;
								ram_be_b2 = BE_B2_i;
								ram_be_a1 = BE_A1_i;
								ram_be_b1 = BE_B1_i;
						end
						0: begin
								case (WMODE_A1_i)
										MODE_36: begin
												ram_wdata_a1 = WDATA_A1_i;
												ram_wdata_a2 = WDATA_A2_i;
												ram_be_a2 = (FMODE1_i ? 2'b11 : BE_A2_i);
												ram_be_a1 = (FMODE1_i ? 2'b11 : BE_A1_i);
										end
										MODE_18: begin
												ram_wdata_a1 = WDATA_A1_i;
												ram_wdata_a2 = WDATA_A1_i;
												ram_be_a1 = (FMODE1_i ? (ff_waddr[1] ? 2'b00 : 2'b11) : BE_A1_i);
												ram_be_a2 = (FMODE1_i ? (ff_waddr[1] ? 2'b11 : 2'b00) : BE_A1_i);
										end
										MODE_9: begin
												ram_wdata_a1[7:0] = WDATA_A1_i[7:0];
												ram_wdata_a1[16] = WDATA_A1_i[16];
												ram_wdata_a1[15:8] = WDATA_A1_i[7:0];
												ram_wdata_a1[17] = WDATA_A1_i[16];
												ram_wdata_a2[7:0] = WDATA_A1_i[7:0];
												ram_wdata_a2[16] = WDATA_A1_i[16];
												ram_wdata_a2[15:8] = WDATA_A1_i[7:0];
												ram_wdata_a2[17] = WDATA_A1_i[16];
												case (bwl)
														0: {ram_be_a2, ram_be_a1} = 4'b0001;
														1: {ram_be_a2, ram_be_a1} = 4'b0010;
														2: {ram_be_a2, ram_be_a1} = 4'b0100;
														3: {ram_be_a2, ram_be_a1} = 4'b1000;
												endcase
										end
										default: begin
												ram_wdata_a1 = WDATA_A1_i;
												ram_wdata_a2 = WDATA_A1_i;
												ram_be_a2 = (FMODE1_i ? 2'b11 : BE_A1_i);
												ram_be_a1 = (FMODE1_i ? 2'b11 : BE_A1_i);
										end
								endcase
								case (WMODE_B1_i)
										MODE_36: begin
												ram_wdata_b1 = (FMODE1_i ? 18'b000000000000000000 : WDATA_B1_i);
												ram_wdata_b2 = (FMODE1_i ? 18'b000000000000000000 : WDATA_B2_i);
												ram_be_b2 = BE_B2_i;
												ram_be_b1 = BE_B1_i;
										end
										MODE_18: begin
												ram_wdata_b1 = (FMODE1_i ? 18'b000000000000000000 : WDATA_B1_i);
												ram_wdata_b2 = (FMODE1_i ? 18'b000000000000000000 : WDATA_B1_i);
												ram_be_b1 = BE_B1_i;
												ram_be_b2 = BE_B1_i;
										end
										MODE_9: begin
												ram_wdata_b1[7:0] = WDATA_B1_i[7:0];
												ram_wdata_b1[16] = WDATA_B1_i[16];
												ram_wdata_b1[15:8] = WDATA_B1_i[7:0];
												ram_wdata_b1[17] = WDATA_B1_i[16];
												ram_wdata_b2[7:0] = WDATA_B1_i[7:0];
												ram_wdata_b2[16] = WDATA_B1_i[16];
												ram_wdata_b2[15:8] = WDATA_B1_i[7:0];
												ram_wdata_b2[17] = WDATA_B1_i[16];
												case (ADDR_B1_i[4:3])
														0: {ram_be_b2, ram_be_b1} = 4'b0001;
														1: {ram_be_b2, ram_be_b1} = 4'b0010;
														2: {ram_be_b2, ram_be_b1} = 4'b0100;
														3: {ram_be_b2, ram_be_b1} = 4'b1000;
												endcase
										end
										default: begin
												ram_wdata_b1 = (FMODE1_i ? 18'b000000000000000000 : WDATA_B1_i);
												ram_wdata_b2 = (FMODE1_i ? 18'b000000000000000000 : WDATA_B1_i);
												ram_be_b2 = BE_B1_i;
												ram_be_b1 = BE_B1_i;
										end
								endcase
						end
				endcase
		end
		assign ram_rmode_a1 = (SPLIT_i ? (RMODE_A1_i == MODE_36 ? MODE_18 : RMODE_A1_i) : (RMODE_A1_i == MODE_36 ? MODE_18 : RMODE_A1_i));
		assign ram_rmode_a2 = (SPLIT_i ? (RMODE_A2_i == MODE_36 ? MODE_18 : RMODE_A2_i) : (RMODE_A1_i == MODE_36 ? MODE_18 : RMODE_A1_i));
		assign ram_wmode_a1 = (SPLIT_i ? (WMODE_A1_i == MODE_36 ? MODE_18 : WMODE_A1_i) : (WMODE_A1_i == MODE_36 ? MODE_18 : (FMODE1_i ? MODE_18 : WMODE_A1_i)));
		assign ram_wmode_a2 = (SPLIT_i ? (WMODE_A2_i == MODE_36 ? MODE_18 : WMODE_A2_i) : (WMODE_A1_i == MODE_36 ? MODE_18 : (FMODE1_i ? MODE_18 : WMODE_A1_i)));
		assign ram_rmode_b1 = (SPLIT_i ? (RMODE_B1_i == MODE_36 ? MODE_18 : RMODE_B1_i) : (RMODE_B1_i == MODE_36 ? MODE_18 : (FMODE1_i ? MODE_18 : RMODE_B1_i)));
		assign ram_rmode_b2 = (SPLIT_i ? (RMODE_B2_i == MODE_36 ? MODE_18 : RMODE_B2_i) : (RMODE_B1_i == MODE_36 ? MODE_18 : (FMODE1_i ? MODE_18 : RMODE_B1_i)));
		assign ram_wmode_b1 = (SPLIT_i ? (WMODE_B1_i == MODE_36 ? MODE_18 : WMODE_B1_i) : (WMODE_B1_i == MODE_36 ? MODE_18 : WMODE_B1_i));
		assign ram_wmode_b2 = (SPLIT_i ? (WMODE_B2_i == MODE_36 ? MODE_18 : WMODE_B2_i) : (WMODE_B1_i == MODE_36 ? MODE_18 : WMODE_B1_i));
		always @(*) begin : FIFO_READ_SEL
				case (RMODE_B1_i)
						MODE_36: fifo_rdata = {ram_rdata_b2[17:16], ram_rdata_b1[17:16], ram_rdata_b2[15:0], ram_rdata_b1[15:0]};
						MODE_18: fifo_rdata = (ff_raddr[1] ? {18'b000000000000000000, ram_rdata_b2} : {18'b000000000000000000, ram_rdata_b1});
						MODE_9:
								case (ff_raddr[1:0])
										0: fifo_rdata = {19'b0000000000000000000, ram_rdata_b1[16], 8'b00000000, ram_rdata_b1[7:0]};
										1: fifo_rdata = {19'b0000000000000000000, ram_rdata_b1[17], 8'b00000000, ram_rdata_b1[15:8]};
										2: fifo_rdata = {19'b0000000000000000000, ram_rdata_b2[16], 8'b00000000, ram_rdata_b2[7:0]};
										3: fifo_rdata = {19'b0000000000000000000, ram_rdata_b2[17], 8'b00000000, ram_rdata_b2[15:8]};
								endcase
						default: fifo_rdata = {ram_rdata_b2, ram_rdata_b1};
				endcase
		end
		localparam MODE_1 = 3'b101;
		localparam MODE_2 = 3'b110;
		localparam MODE_4 = 3'b100;
		always @(*) begin : RDATA_SEL
				case (SPLIT_i)
						1: begin
								RDATA_A1_o = (FMODE1_i ? {10'b0000000000, EMPTY1, EPO1, EWM1, UNDERRUN1, FULL1, FMO1, FWM1, OVERRUN1} : ram_rdata_a1);
								RDATA_B1_o = ram_rdata_b1;
								RDATA_A2_o = (FMODE2_i ? {10'b0000000000, EMPTY2, EPO2, EWM2, UNDERRUN2, FULL2, FMO2, FWM2, OVERRUN2} : ram_rdata_a2);
								RDATA_B2_o = ram_rdata_b2;
						end
						0: begin
								if (FMODE1_i) begin
										RDATA_A1_o = {10'b0000000000, EMPTY3, EPO3, EWM3, UNDERRUN3, FULL3, FMO3, FWM3, OVERRUN3};
										RDATA_A2_o = 18'b000000000000000000;
								end
								else
										case (RMODE_A1_i)
												MODE_36: begin
														RDATA_A1_o = {ram_rdata_a1[17:0]};
														RDATA_A2_o = {ram_rdata_a2[17:0]};
												end
												MODE_18: begin
														RDATA_A1_o = (laddr_a1[4] ? ram_rdata_a2 : ram_rdata_a1);
														RDATA_A2_o = 18'b000000000000000000;
												end
												MODE_9: begin
														RDATA_A1_o = (laddr_a1[4] ? {{2 {ram_rdata_a2[16]}}, {2 {ram_rdata_a2[7:0]}}} : {{2 {ram_rdata_a1[16]}}, {2 {ram_rdata_a1[7:0]}}});
														RDATA_A2_o = 18'b000000000000000000;
												end
												MODE_4: begin
														RDATA_A2_o = 18'b000000000000000000;
														RDATA_A1_o[17:4] = 14'b00000000000000;
														RDATA_A1_o[3:0] = (laddr_a1[4] ? ram_rdata_a2[3:0] : ram_rdata_a1[3:0]);
												end
												MODE_2: begin
														RDATA_A2_o = 18'b000000000000000000;
														RDATA_A1_o[17:2] = 16'b0000000000000000;
														RDATA_A1_o[1:0] = (laddr_a1[4] ? ram_rdata_a2[1:0] : ram_rdata_a1[1:0]);
												end
												MODE_1: begin
														RDATA_A2_o = 18'b000000000000000000;
														RDATA_A1_o[17:1] = 17'b00000000000000000;
														RDATA_A1_o[0] = (laddr_a1[4] ? ram_rdata_a2[0] : ram_rdata_a1[0]);
												end
												default: begin
														RDATA_A1_o = {ram_rdata_a2[1:0], ram_rdata_a1[15:0]};
														RDATA_A2_o = {ram_rdata_a2[17:16], ram_rdata_a1[17:16], ram_rdata_a2[15:2]};
												end
										endcase
								case (RMODE_B1_i)
										MODE_36: begin
												RDATA_B1_o = {ram_rdata_b1};
												RDATA_B2_o = {ram_rdata_b2};
										end
										MODE_18: begin
												RDATA_B1_o = (FMODE1_i ? fifo_rdata[17:0] : (laddr_b1[4] ? ram_rdata_b2 : ram_rdata_b1));
												RDATA_B2_o = 18'b000000000000000000;
										end
										MODE_9: begin
												RDATA_B1_o = (FMODE1_i ? {fifo_rdata[17:0]} : (laddr_b1[4] ? {1'b0, ram_rdata_b2[16], 8'b00000000, ram_rdata_b2[7:0]} : {1'b0, ram_rdata_b1[16], 8'b00000000, ram_rdata_b1[7:0]}));
												RDATA_B2_o = 18'b000000000000000000;
										end
										MODE_4: begin
												RDATA_B2_o = 18'b000000000000000000;
												RDATA_B1_o[17:4] = 14'b00000000000000;
												RDATA_B1_o[3:0] = (laddr_b1[4] ? ram_rdata_b2[3:0] : ram_rdata_b1[3:0]);
										end
										MODE_2: begin
												RDATA_B2_o = 18'b000000000000000000;
												RDATA_B1_o[17:2] = 16'b0000000000000000;
												RDATA_B1_o[1:0] = (laddr_b1[4] ? ram_rdata_b2[1:0] : ram_rdata_b1[1:0]);
										end
										MODE_1: begin
												RDATA_B2_o = 18'b000000000000000000;
												RDATA_B1_o[17:1] = 17'b00000000000000000;
												RDATA_B1_o[0] = (laddr_b1[4] ? ram_rdata_b2[0] : ram_rdata_b1[0]);
										end
										default: begin
												RDATA_B1_o = ram_rdata_b1;
												RDATA_B2_o = ram_rdata_b2;
										end
								endcase
						end
				endcase
		end
		always @(posedge sclk_a1 or negedge sreset)
				if (sreset == 0)
						laddr_a1 <= 1'sb0;
				else
						laddr_a1 <= ADDR_A1_i;
		always @(posedge sclk_b1 or negedge sreset)
				if (sreset == 0)
						laddr_b1 <= 1'sb0;
				else
						laddr_b1 <= ADDR_B1_i;
		assign fifo_wmode = ((WMODE_A1_i == MODE_36) ? 2'b00 : ((WMODE_A1_i == MODE_18) ? 2'b01 : ((WMODE_A1_i == MODE_9) ? 2'b10 : 2'b00)));
		assign fifo_rmode = ((RMODE_B1_i == MODE_36) ? 2'b00 : ((RMODE_B1_i == MODE_18) ? 2'b01 : ((RMODE_B1_i == MODE_9) ? 2'b10 : 2'b00)));
		fifo_ctl #(
				.ADDR_WIDTH(12),
				.FIFO_WIDTH(3'd4),
				.DEPTH(7)
		) fifo36_ctl(
				.rclk(sclk_b1),
				.rst_R_n(flush1),
				.wclk(sclk_a1),
				.rst_W_n(flush1),
				.ren(REN_B1_i),
				.wen(ram_wen_a1),
				.sync(SYNC_FIFO1_i),
				.rmode(fifo_rmode),
				.wmode(fifo_wmode),
				.ren_o(ren_o),
				.fflags({FULL3, FMO3, FWM3, OVERRUN3, EMPTY3, EPO3, EWM3, UNDERRUN3}),
				.raddr(ff_raddr),
				.waddr(ff_waddr),
				.upaf(UPAF1_i),
				.upae(UPAE1_i)
		);
		TDP18K_FIFO #(
				.UPAF_i(UPAF1_i[10:0]),
				.UPAE_i(UPAE1_i[10:0]),
				.SYNC_FIFO_i(SYNC_FIFO1_i),
				.POWERDN_i(POWERDN1_i),
				.SLEEP_i(SLEEP1_i),
				.PROTECT_i(PROTECT1_i),
				.INIT_i(split_init(0))
		)u1(
				.RMODE_A_i(ram_rmode_a1),
				.RMODE_B_i(ram_rmode_b1),
				.WMODE_A_i(ram_wmode_a1),
				.WMODE_B_i(ram_wmode_b1),
				.WEN_A_i(ram_wen_a1),
				.WEN_B_i(ram_wen_b1),
				.REN_A_i(ram_ren_a1),
				.REN_B_i(ram_ren_b1),
				.CLK_A_i(sclk_a1),
				.CLK_B_i(sclk_b1),
				.BE_A_i(ram_be_a1),
				.BE_B_i(ram_be_b1),
				.ADDR_A_i(ram_addr_a1),
				.ADDR_B_i(ram_addr_b1),
				.WDATA_A_i(ram_wdata_a1),
				.WDATA_B_i(ram_wdata_b1),
				.RDATA_A_o(ram_rdata_a1),
				.RDATA_B_o(ram_rdata_b1),
				.EMPTY_o(EMPTY1),
				.EPO_o(EPO1),
				.EWM_o(EWM1),
				.UNDERRUN_o(UNDERRUN1),
				.FULL_o(FULL1),
				.FMO_o(FMO1),
				.FWM_o(FWM1),
				.OVERRUN_o(OVERRUN1),
				.FLUSH_ni(flush1),
				.FMODE_i(ram_fmode1)
		);
		TDP18K_FIFO #(
				.UPAF_i(UPAF2_i),
				.UPAE_i(UPAE2_i),
				.SYNC_FIFO_i(SYNC_FIFO2_i),
				.POWERDN_i(POWERDN2_i),
				.SLEEP_i(SLEEP2_i),
				.PROTECT_i(PROTECT2_i),
				.INIT_i(split_init(1))
		)u2(
				.RMODE_A_i(ram_rmode_a2),
				.RMODE_B_i(ram_rmode_b2),
				.WMODE_A_i(ram_wmode_a2),
				.WMODE_B_i(ram_wmode_b2),
				.WEN_A_i(ram_wen_a2),
				.WEN_B_i(ram_wen_b2),
				.REN_A_i(ram_ren_a2),
				.REN_B_i(ram_ren_b2),
				.CLK_A_i(sclk_a2),
				.CLK_B_i(sclk_b2),
				.BE_A_i(ram_be_a2),
				.BE_B_i(ram_be_b2),
				.ADDR_A_i(ram_addr_a2),
				.ADDR_B_i(ram_addr_b2),
				.WDATA_A_i(ram_wdata_a2),
				.WDATA_B_i(ram_wdata_b2),
				.RDATA_A_o(ram_rdata_a2),
				.RDATA_B_o(ram_rdata_b2),
				.EMPTY_o(EMPTY2),
				.EPO_o(EPO2),
				.EWM_o(EWM2),
				.UNDERRUN_o(UNDERRUN2),
				.FULL_o(FULL2),
				.FMO_o(FMO2),
				.FWM_o(FWM2),
				.OVERRUN_o(OVERRUN2),
				.FLUSH_ni(flush2),
				.FMODE_i(ram_fmode2)
		);
endmodule

module RAM_18K_X2_BLK (
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
assign BE_B1_i = 2'h0;
assign REN_B2_i = REN2_i;
assign WEN_B2_i = 1'b0;
assign BE_B2_i = 2'h0;

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
(* is_split = 1 *)
(* port_a1_dwidth = WR1_DATA_WIDTH *)
(* port_a2_dwidth = WR2_DATA_WIDTH *)
(* port_b1_dwidth = RD1_DATA_WIDTH *)
(* port_b2_dwidth = RD2_DATA_WIDTH *)
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
assign BE_B1_i = 2'h0;
assign REN_B2_i = REN2_i;
assign WEN_B2_i = 1'b0;
assign BE_B2_i = 2'h0;

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
(* port_a_dwidth = WR1_DATA_WIDTH *)
(* port_b_dwidth = RD1_DATA_WIDTH *)
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

module RAM_18K_BLK (
		WEN_i,
		REN_i,
		WR_CLK_i,
		RD_CLK_i,
		WR_BE_i,
		WR_ADDR_i,
		RD_ADDR_i,
		WDATA_i,
		RDATA_o
);

parameter WR_ADDR_WIDTH = 10;
parameter RD_ADDR_WIDTH = 10;
parameter WR_DATA_WIDTH = 18;
parameter RD_DATA_WIDTH = 18;
parameter BE_WIDTH = 2;

input wire WEN_i;
input wire REN_i;
input wire WR_CLK_i;
input wire RD_CLK_i;
input wire [BE_WIDTH-1:0] WR_BE_i;
input wire [WR_ADDR_WIDTH-1 :0] WR_ADDR_i;
input wire [RD_ADDR_WIDTH-1 :0] RD_ADDR_i;
input wire [WR_DATA_WIDTH-1 :0] WDATA_i;
output wire [RD_DATA_WIDTH-1 :0] RDATA_o;

	(* is_inferred = 0 *)
	(* is_split = 0 *)
	BRAM2x18_SP  #(
			.WR1_ADDR_WIDTH(WR_ADDR_WIDTH),
			.RD1_ADDR_WIDTH(RD_ADDR_WIDTH),
			.WR1_DATA_WIDTH(WR_DATA_WIDTH),
			.RD1_DATA_WIDTH(RD_DATA_WIDTH),
			.BE1_WIDTH(BE_WIDTH),
			.WR2_ADDR_WIDTH(),
			.RD2_ADDR_WIDTH(),
			.WR2_DATA_WIDTH(),
			.RD2_DATA_WIDTH(),
			.BE2_WIDTH()
			 ) U1
			(
			.RESET_ni(1'b1),

			.WEN1_i(WEN_i),
			.REN1_i(REN_i),
			.WR1_CLK_i(WR_CLK_i),
			.RD1_CLK_i(RD_CLK_i),
			.WR1_BE_i(WR_BE_i),
			.WR1_ADDR_i(WR_ADDR_i),
			.RD1_ADDR_i(RD_ADDR_i),
			.WDATA1_i(WDATA_i),
			.RDATA1_o(RDATA_o),

			.WEN2_i(1'b0),
			.REN2_i(1'b0),
			.WR2_CLK_i(1'b0),
			.RD2_CLK_i(1'b0),
			.WR2_BE_i(2'b00),
			.WR2_ADDR_i(14'h0),
			.RD2_ADDR_i(14'h0),
			.WDATA2_i(18'h0),
			.RDATA2_o()
			);

endmodule

module RAM_36K_BLK (
		WEN_i,
		REN_i,
		WR_CLK_i,
		RD_CLK_i,
		WR_BE_i,
		WR_ADDR_i,
		RD_ADDR_i,
		WDATA_i,
		RDATA_o
);

parameter WR_ADDR_WIDTH = 10;
parameter RD_ADDR_WIDTH = 10;
parameter WR_DATA_WIDTH = 36;
parameter RD_DATA_WIDTH = 36;
parameter BE_WIDTH = 4;

parameter INIT = 0;

input wire WEN_i;
input wire REN_i;
input wire WR_CLK_i;
input wire RD_CLK_i;
input wire [BE_WIDTH-1:0] WR_BE_i;
input wire [WR_ADDR_WIDTH-1 :0] WR_ADDR_i;
input wire [RD_ADDR_WIDTH-1 :0] RD_ADDR_i;
input wire [WR_DATA_WIDTH-1 :0] WDATA_i;
output wire [RD_DATA_WIDTH-1 :0] RDATA_o;

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

wire [3:0] WR_BE;

wire [35:0] PORT_B_RDATA;
wire [35:0] PORT_A_WDATA;

wire [14:0] WR_ADDR_INT;
wire [14:0] RD_ADDR_INT;

wire [14:0] PORT_A_ADDR;
wire [14:0] PORT_B_ADDR;

wire PORT_A_CLK;
wire PORT_B_CLK;

// Set port width mode (In non-split mode A2/B2 is not active. Set same values anyway to match previous behavior.)
localparam [ 2:0] RMODE_A1_i    = mode(WR_DATA_WIDTH);
localparam [ 2:0] WMODE_A1_i    = mode(WR_DATA_WIDTH);
localparam [ 2:0] RMODE_A2_i    = mode(WR_DATA_WIDTH);
localparam [ 2:0] WMODE_A2_i    = mode(WR_DATA_WIDTH);

localparam [ 2:0] RMODE_B1_i    = mode(RD_DATA_WIDTH);
localparam [ 2:0] WMODE_B1_i    = mode(RD_DATA_WIDTH);
localparam [ 2:0] RMODE_B2_i    = mode(RD_DATA_WIDTH);
localparam [ 2:0] WMODE_B2_i    = mode(RD_DATA_WIDTH);

assign PORT_A_CLK = WR_CLK_i;
assign PORT_B_CLK = RD_CLK_i;

generate
	if (WR_ADDR_WIDTH == 15) begin
		assign WR_ADDR_INT = WR_ADDR_i;
	end else begin
		assign WR_ADDR_INT[14:WR_ADDR_WIDTH] = 0;
		assign WR_ADDR_INT[WR_ADDR_WIDTH-1:0] = WR_ADDR_i;
	end
endgenerate

case (WR_DATA_WIDTH)
	1: begin
		assign PORT_A_ADDR = WR_ADDR_INT;
	end
	2: begin
		assign PORT_A_ADDR = WR_ADDR_INT << 1;
	end
	4: begin
		assign PORT_A_ADDR = WR_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_A_ADDR = WR_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_A_ADDR = WR_ADDR_INT << 4;
	end
	32, 36: begin
		assign PORT_A_ADDR = WR_ADDR_INT << 5;
	end
	default: begin
		assign PORT_A_ADDR = WR_ADDR_INT;
	end
endcase

generate
	if (RD_ADDR_WIDTH == 15) begin
		assign RD_ADDR_INT = RD_ADDR_i;
	end else begin
		assign RD_ADDR_INT[14:RD_ADDR_WIDTH] = 0;
		assign RD_ADDR_INT[RD_ADDR_WIDTH-1:0] = RD_ADDR_i;
	end
endgenerate

case (RD_DATA_WIDTH)
	1: begin
		assign PORT_B_ADDR = RD_ADDR_INT;
	end
	2: begin
		assign PORT_B_ADDR = RD_ADDR_INT << 1;
	end
	4: begin
		assign PORT_B_ADDR = RD_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_B_ADDR = RD_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_B_ADDR = RD_ADDR_INT << 4;
	end
	32, 36: begin
		assign PORT_B_ADDR = RD_ADDR_INT << 5;
	end
	default: begin
		assign PORT_B_ADDR = RD_ADDR_INT;
	end
endcase

case (BE_WIDTH)
	4: begin
		assign WR_BE = WR_BE_i[BE_WIDTH-1 :0];
	end
	default: begin
		assign WR_BE[3:BE_WIDTH] = 0;
		assign WR_BE[BE_WIDTH-1 :0] = WR_BE_i[BE_WIDTH-1 :0];
	end
endcase

assign REN_A1_i = 1'b0;
assign WEN_A1_i = WEN_i;
assign {BE_A2_i, BE_A1_i} = WR_BE;

assign REN_B1_i = REN_i;
assign WEN_B1_i = 1'b0;
assign {BE_B2_i, BE_B1_i} = 4'h0;

generate
	if (WR_DATA_WIDTH == 36) begin
		assign PORT_A_WDATA[WR_DATA_WIDTH-1:0] = WDATA_i[WR_DATA_WIDTH-1:0];
	end else if (WR_DATA_WIDTH > 18 && WR_DATA_WIDTH < 36) begin
		assign PORT_A_WDATA[WR_DATA_WIDTH+1:18]  = WDATA_i[WR_DATA_WIDTH-1:16];
		assign PORT_A_WDATA[17:0] = {2'b00,WDATA_i[15:0]};
	end else if (WR_DATA_WIDTH == 9) begin
		assign PORT_A_WDATA = {19'h0, WDATA_i[8], 8'h0, WDATA_i[7:0]};
	end else begin
		assign PORT_A_WDATA[35:WR_DATA_WIDTH] = 0;
		assign PORT_A_WDATA[WR_DATA_WIDTH-1:0] = WDATA_i[WR_DATA_WIDTH-1:0];
	end
endgenerate

assign WDATA_A1_i = PORT_A_WDATA[17:0];
assign WDATA_A2_i = PORT_A_WDATA[35:18];

assign WDATA_B1_i = 18'h0;
assign WDATA_B2_i = 18'h0;

generate
	if (RD_DATA_WIDTH == 36) begin
		assign PORT_B_RDATA = {RDATA_B2_o, RDATA_B1_o};
	end else if (RD_DATA_WIDTH > 18 && RD_DATA_WIDTH < 36) begin
		assign PORT_B_RDATA  = {2'b00,RDATA_B2_o[17:0],RDATA_B1_o[15:0]};
	end else if (RD_DATA_WIDTH == 9) begin
		assign PORT_B_RDATA = { 27'h0, RDATA_B1_o[16], RDATA_B1_o[7:0]};
	end else begin
		assign PORT_B_RDATA = {18'h0, RDATA_B1_o};
	end
endgenerate

assign RDATA_o = PORT_B_RDATA[RD_DATA_WIDTH-1:0];

defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b0,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
};

(* is_inferred = 1 *)
(* is_split = 0 *)
(* port_a_width = WR_DATA_WIDTH *)
(* port_b_width = RD_DATA_WIDTH *)
TDP36K _TECHMAP_REPLACE_ (
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


module DPRAM_18K_X2_BLK (
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


input wire PORT_A1_CLK_i;
input wire [PORT_A1_AWIDTH-1:0] PORT_A1_ADDR_i;
input wire [PORT_A1_DWIDTH-1:0] PORT_A1_WR_DATA_i;
input wire PORT_A1_WEN_i;
input wire [PORT_A1_WR_BE_WIDTH-1:0] PORT_A1_WR_BE_i;
input wire PORT_A1_REN_i;
output wire [PORT_A1_DWIDTH-1:0] PORT_A1_RD_DATA_o;

input wire PORT_B1_CLK_i;
input wire [PORT_B1_AWIDTH-1:0] PORT_B1_ADDR_i;
input wire [PORT_B1_DWIDTH-1:0] PORT_B1_WR_DATA_i;
input wire PORT_B1_WEN_i;
input wire [PORT_B1_WR_BE_WIDTH-1:0] PORT_B1_WR_BE_i;
input wire PORT_B1_REN_i;
output wire [PORT_B1_DWIDTH-1:0] PORT_B1_RD_DATA_o;

input wire PORT_A2_CLK_i;
input wire [PORT_A2_AWIDTH-1:0] PORT_A2_ADDR_i;
input wire [PORT_A2_DWIDTH-1:0] PORT_A2_WR_DATA_i;
input wire PORT_A2_WEN_i;
input wire [PORT_A2_WR_BE_WIDTH-1:0] PORT_A2_WR_BE_i;
input wire PORT_A2_REN_i;
output wire [PORT_A2_DWIDTH-1:0] PORT_A2_RD_DATA_o;

input wire PORT_B2_CLK_i;
input wire [PORT_B2_AWIDTH-1:0] PORT_B2_ADDR_i;
input wire [PORT_B2_DWIDTH-1:0] PORT_B2_WR_DATA_i;
input wire PORT_B2_WEN_i;
input wire [PORT_B2_WR_BE_WIDTH-1:0] PORT_B2_WR_BE_i;
input wire PORT_B2_REN_i;
output wire [PORT_B2_DWIDTH-1:0] PORT_B2_RD_DATA_o;


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
(* is_split = 1 *)
(* port_a1_dwidth = PORT_A1_DWIDTH *)
(* port_a2_dwidth = PORT_A2_DWIDTH *)
(* port_b1_dwidth = PORT_B1_DWIDTH *)
(* port_b2_dwidth = PORT_B2_DWIDTH *)
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

input wire PORT_A1_CLK_i;
input wire [PORT_A1_AWIDTH-1:0] PORT_A1_ADDR_i;
input wire [PORT_A1_DWIDTH-1:0] PORT_A1_WR_DATA_i;
input wire PORT_A1_WEN_i;
input wire [PORT_A1_WR_BE_WIDTH-1:0] PORT_A1_WR_BE_i;
input wire PORT_A1_REN_i;
output wire [PORT_A1_DWIDTH-1:0] PORT_A1_RD_DATA_o;

input wire PORT_B1_CLK_i;
input wire [PORT_B1_AWIDTH-1:0] PORT_B1_ADDR_i;
input wire [PORT_B1_DWIDTH-1:0] PORT_B1_WR_DATA_i;
input wire PORT_B1_WEN_i;
input wire [PORT_B1_WR_BE_WIDTH-1:0] PORT_B1_WR_BE_i;
input wire PORT_B1_REN_i;
output wire [PORT_B1_DWIDTH-1:0] PORT_B1_RD_DATA_o;

input wire PORT_A2_CLK_i;
input wire [PORT_A2_AWIDTH-1:0] PORT_A2_ADDR_i;
input wire [PORT_A2_DWIDTH-1:0] PORT_A2_WR_DATA_i;
input wire PORT_A2_WEN_i;
input wire [PORT_A2_WR_BE_WIDTH-1:0] PORT_A2_WR_BE_i;
input wire PORT_A2_REN_i;
output wire [PORT_A2_DWIDTH-1:0] PORT_A2_RD_DATA_o;

input wire PORT_B2_CLK_i;
input wire [PORT_B2_AWIDTH-1:0] PORT_B2_ADDR_i;
input wire [PORT_B2_DWIDTH-1:0] PORT_B2_WR_DATA_i;
input wire PORT_B2_WEN_i;
input wire [PORT_B2_WR_BE_WIDTH-1:0] PORT_B2_WR_BE_i;
input wire PORT_B2_REN_i;
output wire [PORT_B2_DWIDTH-1:0] PORT_B2_RD_DATA_o;


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
(* port_a_dwidth = PORT_A1_DWIDTH *)
(* port_b_dwidth = PORT_B1_DWIDTH *)
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

module DPRAM_18K_BLK (
		PORT_A_CLK_i,
		PORT_A_WEN_i,
		PORT_A_WR_BE_i,
		PORT_A_REN_i,
		PORT_A_ADDR_i,
		PORT_A_WR_DATA_i,
		PORT_A_RD_DATA_o,

		PORT_B_CLK_i,
		PORT_B_WEN_i,
		PORT_B_WR_BE_i,
		PORT_B_REN_i,
		PORT_B_ADDR_i,
		PORT_B_WR_DATA_i,
		PORT_B_RD_DATA_o
);

parameter PORT_A_AWIDTH = 10;
parameter PORT_A_DWIDTH = 36;
parameter PORT_A_WR_BE_WIDTH = 4;

parameter PORT_B_AWIDTH = 10;
parameter PORT_B_DWIDTH = 36;
parameter PORT_B_WR_BE_WIDTH = 4;

input wire PORT_A_CLK_i;
input wire [PORT_A_AWIDTH-1:0] PORT_A_ADDR_i;
input wire [PORT_A_DWIDTH-1:0] PORT_A_WR_DATA_i;
input wire PORT_A_WEN_i;
input wire [PORT_A_WR_BE_WIDTH-1:0] PORT_A_WR_BE_i;
input wire PORT_A_REN_i;
output wire [PORT_A_DWIDTH-1:0] PORT_A_RD_DATA_o;

input wire PORT_B_CLK_i;
input wire [PORT_B_AWIDTH-1:0] PORT_B_ADDR_i;
input wire [PORT_B_DWIDTH-1:0] PORT_B_WR_DATA_i;
input wire PORT_B_WEN_i;
input wire [PORT_B_WR_BE_WIDTH-1:0] PORT_B_WR_BE_i;
input wire PORT_B_REN_i;
output wire [PORT_B_DWIDTH-1:0] PORT_B_RD_DATA_o;


(* is_inferred = 0 *)
(* is_split = 0 *)
BRAM2x18_dP #(
	.PORT_A1_AWIDTH(PORT_A_AWIDTH),
	.PORT_A1_DWIDTH(PORT_A_DWIDTH),
	.PORT_A1_WR_BE_WIDTH(PORT_A_WR_BE_WIDTH),
	.PORT_B1_AWIDTH(PORT_B_AWIDTH),
	.PORT_B1_DWIDTH(PORT_B_DWIDTH),
	.PORT_B1_WR_BE_WIDTH(PORT_B_WR_BE_WIDTH),
	.PORT_A2_AWIDTH(),
	.PORT_A2_DWIDTH(),
	.PORT_A2_WR_BE_WIDTH(),
	.PORT_B2_AWIDTH(),
	.PORT_B2_DWIDTH(),
	.PORT_B2_WR_BE_WIDTH()
) U1 (
		.PORT_A1_CLK_i(PORT_A_CLK_i),
		.PORT_A1_WEN_i(PORT_A_WEN_i),
		.PORT_A1_WR_BE_i(PORT_A_WR_BE_i),
		.PORT_A1_REN_i(PORT_A_REN_i),
		.PORT_A1_ADDR_i(PORT_A_ADDR_i),
		.PORT_A1_WR_DATA_i(PORT_A_WR_DATA_i),
		.PORT_A1_RD_DATA_o(PORT_A_RD_DATA_o),

		.PORT_B1_CLK_i(PORT_B_CLK_i),
		.PORT_B1_WEN_i(PORT_B_WEN_i),
		.PORT_B1_WR_BE_i(PORT_B_WR_BE_i),
		.PORT_B1_REN_i(PORT_B_REN_i),
		.PORT_B1_ADDR_i(PORT_B_ADDR_i),
		.PORT_B1_WR_DATA_i(PORT_B_WR_DATA_i),
		.PORT_B1_RD_DATA_o(PORT_B_RD_DATA_o),

		.PORT_A2_CLK_i(1'b0),
		.PORT_A2_WEN_i(1'b0),
		.PORT_A2_WR_BE_i(2'b00),
		.PORT_A2_REN_i(1'b0),
		.PORT_A2_ADDR_i(14'h0),
		.PORT_A2_WR_DATA_i(18'h0),
		.PORT_A2_RD_DATA_o(),

		.PORT_B2_CLK_i(1'b0),
		.PORT_B2_WEN_i(1'b0),
		.PORT_B2_WR_BE_i(2'b00),
		.PORT_B2_REN_i(1'b0),
		.PORT_B2_ADDR_i(14'h0),
		.PORT_B2_WR_DATA_i(18'h0),
		.PORT_B2_RD_DATA_o()
);

endmodule

module DPRAM_36K_BLK (
		PORT_A_CLK_i,
		PORT_A_WEN_i,
		PORT_A_WR_BE_i,
		PORT_A_REN_i,
		PORT_A_ADDR_i,
		PORT_A_WR_DATA_i,
		PORT_A_RD_DATA_o,

		PORT_B_CLK_i,
		PORT_B_WEN_i,
		PORT_B_WR_BE_i,
		PORT_B_REN_i,
		PORT_B_ADDR_i,
		PORT_B_WR_DATA_i,
		PORT_B_RD_DATA_o
);

parameter PORT_A_AWIDTH = 10;
parameter PORT_A_DWIDTH = 36;
parameter PORT_A_WR_BE_WIDTH = 4;

parameter PORT_B_AWIDTH = 10;
parameter PORT_B_DWIDTH = 36;
parameter PORT_B_WR_BE_WIDTH = 4;

input wire PORT_A_CLK_i;
input wire [PORT_A_AWIDTH-1:0] PORT_A_ADDR_i;
input wire [PORT_A_DWIDTH-1:0] PORT_A_WR_DATA_i;
input wire PORT_A_WEN_i;
input wire [PORT_A_WR_BE_WIDTH-1:0] PORT_A_WR_BE_i;
input wire PORT_A_REN_i;
output wire [PORT_A_DWIDTH-1:0] PORT_A_RD_DATA_o;

input wire PORT_B_CLK_i;
input wire [PORT_B_AWIDTH-1:0] PORT_B_ADDR_i;
input wire [PORT_B_DWIDTH-1:0] PORT_B_WR_DATA_i;
input wire PORT_B_WEN_i;
input wire [PORT_B_WR_BE_WIDTH-1:0] PORT_B_WR_BE_i;
input wire PORT_B_REN_i;
output wire [PORT_B_DWIDTH-1:0] PORT_B_RD_DATA_o;


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

wire [3:0] PORT_A_WR_BE;
wire [3:0] PORT_B_WR_BE;

wire [35:0] PORT_B_WDATA;
wire [35:0] PORT_B_RDATA;
wire [35:0] PORT_A_WDATA;
wire [35:0] PORT_A_RDATA;

wire [14:0] PORT_A_ADDR_INT;
wire [14:0] PORT_B_ADDR_INT;

wire [14:0] PORT_A_ADDR;
wire [14:0] PORT_B_ADDR;

wire PORT_A_CLK;
wire PORT_B_CLK;

// Set port width mode (In non-split mode A2/B2 is not active. Set same values anyway to match previous behavior.)
localparam [ 2:0] RMODE_A1_i    = mode(PORT_A_DWIDTH);
localparam [ 2:0] WMODE_A1_i    = mode(PORT_A_DWIDTH);
localparam [ 2:0] RMODE_A2_i    = mode(PORT_A_DWIDTH);
localparam [ 2:0] WMODE_A2_i    = mode(PORT_A_DWIDTH);

localparam [ 2:0] RMODE_B1_i    = mode(PORT_B_DWIDTH);
localparam [ 2:0] WMODE_B1_i    = mode(PORT_B_DWIDTH);
localparam [ 2:0] RMODE_B2_i    = mode(PORT_B_DWIDTH);
localparam [ 2:0] WMODE_B2_i    = mode(PORT_B_DWIDTH);

assign PORT_A_CLK = PORT_A_CLK_i;
assign PORT_B_CLK = PORT_B_CLK_i;

generate
	if (PORT_A_AWIDTH == 15) begin
		assign PORT_A_ADDR_INT = PORT_A_ADDR_i;
	end else begin
		assign PORT_A_ADDR_INT[14:PORT_A_AWIDTH] = 0;
		assign PORT_A_ADDR_INT[PORT_A_AWIDTH-1:0] = PORT_A_ADDR_i;
	end
endgenerate

case (PORT_A_DWIDTH)
	1: begin
		assign PORT_A_ADDR = PORT_A_ADDR_INT;
	end
	2: begin
		assign PORT_A_ADDR = PORT_A_ADDR_INT << 1;
	end
	4: begin
		assign PORT_A_ADDR = PORT_A_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_A_ADDR = PORT_A_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_A_ADDR = PORT_A_ADDR_INT << 4;
	end
	32, 36: begin
		assign PORT_A_ADDR = PORT_A_ADDR_INT << 5;
	end
	default: begin
		assign PORT_A_ADDR = PORT_A_ADDR_INT;
	end
endcase

generate
	if (PORT_B_AWIDTH == 15) begin
		assign PORT_B_ADDR_INT = PORT_B_ADDR_i;
	end else begin
		assign PORT_B_ADDR_INT[14:PORT_B_AWIDTH] = 0;
		assign PORT_B_ADDR_INT[PORT_B_AWIDTH-1:0] = PORT_B_ADDR_i;
	end
endgenerate

case (PORT_B_DWIDTH)
	1: begin
		assign PORT_B_ADDR = PORT_B_ADDR_INT;
	end
	2: begin
		assign PORT_B_ADDR = PORT_B_ADDR_INT << 1;
	end
	4: begin
		assign PORT_B_ADDR = PORT_B_ADDR_INT << 2;
	end
	8, 9: begin
		assign PORT_B_ADDR = PORT_B_ADDR_INT << 3;
	end
	16, 18: begin
		assign PORT_B_ADDR = PORT_B_ADDR_INT << 4;
	end
	32, 36: begin
		assign PORT_B_ADDR = PORT_B_ADDR_INT << 5;
	end
	default: begin
		assign PORT_B_ADDR = PORT_B_ADDR_INT;
	end
endcase

case (PORT_A_WR_BE_WIDTH)
	4: begin
		assign PORT_A_WR_BE = PORT_A_WR_BE_i[PORT_A_WR_BE_WIDTH-1 :0];
	end
	default: begin
		assign PORT_A_WR_BE[3:PORT_A_WR_BE_WIDTH] = 0;
		assign PORT_A_WR_BE[PORT_A_WR_BE_WIDTH-1 :0] = PORT_A_WR_BE_i[PORT_A_WR_BE_WIDTH-1 :0];
	end
endcase

case (PORT_B_WR_BE_WIDTH)
	4: begin
		assign PORT_B_WR_BE = PORT_B_WR_BE_i[PORT_B_WR_BE_WIDTH-1 :0];
	end
	default: begin
		assign PORT_B_WR_BE[3:PORT_B_WR_BE_WIDTH] = 0;
		assign PORT_B_WR_BE[PORT_B_WR_BE_WIDTH-1 :0] = PORT_B_WR_BE_i[PORT_B_WR_BE_WIDTH-1 :0];
	end
endcase

assign REN_A1_i = PORT_A_REN_i;
assign WEN_A1_i = PORT_A_WEN_i;
assign {BE_A2_i, BE_A1_i} = PORT_A_WR_BE;

assign REN_B1_i = PORT_B_REN_i;
assign WEN_B1_i = PORT_B_WEN_i;
assign {BE_B2_i, BE_B1_i} = PORT_B_WR_BE;

generate
	if (PORT_A_DWIDTH == 36) begin
		assign PORT_A_WDATA[PORT_A_DWIDTH-1:0] = PORT_A_WR_DATA_i[PORT_A_DWIDTH-1:0];
	end else if (PORT_A_DWIDTH > 18 && PORT_A_DWIDTH < 36) begin
		assign PORT_A_WDATA[PORT_A_DWIDTH+1:18]  = PORT_A_WR_DATA_i[PORT_A_DWIDTH-1:16];
		assign PORT_A_WDATA[17:0] = {2'b00,PORT_A_WR_DATA_i[15:0]};
	end else if (PORT_A_DWIDTH == 9) begin
		assign PORT_A_WDATA = {19'h0, PORT_A_WR_DATA_i[8], 8'h0, PORT_A_WR_DATA_i[7:0]};
	end else begin
		assign PORT_A_WDATA[35:PORT_A_DWIDTH] = 0;
		assign PORT_A_WDATA[PORT_A_DWIDTH-1:0] = PORT_A_WR_DATA_i[PORT_A_DWIDTH-1:0];
	end
endgenerate

assign WDATA_A1_i = PORT_A_WDATA[17:0];
assign WDATA_A2_i = PORT_A_WDATA[35:18];

generate
	if (PORT_A_DWIDTH == 36) begin
		assign PORT_A_RDATA = {RDATA_A2_o, RDATA_A1_o};
	end else if (PORT_A_DWIDTH > 18 && PORT_A_DWIDTH < 36) begin
		assign PORT_A_RDATA  = {2'b00,RDATA_A2_o[17:0],RDATA_A1_o[15:0]};
	end else if (PORT_A_DWIDTH == 9) begin
		assign PORT_A_RDATA = { 27'h0, RDATA_A1_o[16], RDATA_A1_o[7:0]};
	end else begin
		assign PORT_A_RDATA = {18'h0, RDATA_A1_o};
	end
endgenerate

assign PORT_A_RD_DATA_o = PORT_A_RDATA[PORT_A_DWIDTH-1:0];

generate
	if (PORT_B_DWIDTH == 36) begin
		assign PORT_B_WDATA[PORT_B_DWIDTH-1:0] = PORT_B_WR_DATA_i[PORT_B_DWIDTH-1:0];
	end else if (PORT_B_DWIDTH > 18 && PORT_B_DWIDTH < 36) begin
		assign PORT_B_WDATA[PORT_B_DWIDTH+1:18]  = PORT_B_WR_DATA_i[PORT_B_DWIDTH-1:16];
		assign PORT_B_WDATA[17:0] = {2'b00,PORT_B_WR_DATA_i[15:0]};
	end else if (PORT_B_DWIDTH == 9) begin
		assign PORT_B_WDATA = {19'h0, PORT_B_WR_DATA_i[8], 8'h0, PORT_B_WR_DATA_i[7:0]};
	end else begin
		assign PORT_B_WDATA[35:PORT_B_DWIDTH] = 0;
		assign PORT_B_WDATA[PORT_B_DWIDTH-1:0] = PORT_B_WR_DATA_i[PORT_B_DWIDTH-1:0];
	end
endgenerate

assign WDATA_B1_i = PORT_B_WDATA[17:0];
assign WDATA_B2_i = PORT_B_WDATA[35:18];

generate
	if (PORT_B_DWIDTH == 36) begin
		assign PORT_B_RDATA = {RDATA_B2_o, RDATA_B1_o};
	end else if (PORT_B_DWIDTH > 18 && PORT_B_DWIDTH < 36) begin
		assign PORT_B_RDATA  = {2'b00,RDATA_B2_o[17:0],RDATA_B1_o[15:0]};
	end else if (PORT_B_DWIDTH == 9) begin
		assign PORT_B_RDATA = { 27'h0, RDATA_B1_o[16], RDATA_B1_o[7:0]};
	end else begin
		assign PORT_B_RDATA = {18'h0, RDATA_B1_o};
	end
endgenerate

assign PORT_B_RD_DATA_o = PORT_B_RDATA[PORT_B_DWIDTH-1:0];

defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b0,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
};

(* is_inferred = 1 *)
(* is_split = 0 *)
(* port_a_width = PORT_A_DWIDTH *)
(* port_b_width = PORT_B_DWIDTH *)
TDP36K _TECHMAP_REPLACE_ (
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

	input wire CLK1;
	input wire PUSH1, POP1;
	input wire [WR1_DATA_WIDTH-1:0] DIN1;
	input wire Async_Flush1;
	output wire [RD1_DATA_WIDTH-1:0] DOUT1;
	output wire Almost_Full1, Almost_Empty1;
	output wire Full1, Empty1;
	output wire Full_Watermark1, Empty_Watermark1;
	output wire Overrun_Error1, Underrun_Error1;

	input wire CLK2;
	input wire PUSH2, POP2;
	input wire [WR2_DATA_WIDTH-1:0] DIN2;
	input wire Async_Flush2;
	output wire [RD2_DATA_WIDTH-1:0] DOUT2;
	output wire Almost_Full2, Almost_Empty2;
	output wire Full2, Empty2;
	output wire Full_Watermark2, Empty_Watermark2;
	output wire Overrun_Error2, Underrun_Error2;

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
	(* port_a_dwidth = WR1_DATA_WIDTH *)
	(* port_b_dwidth = RD1_DATA_WIDTH *)
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

module SFIFO_18K_BLK (
		DIN,
		PUSH,
		POP,
		CLK,
		Async_Flush,
		Overrun_Error,
		Full_Watermark,
		Almost_Full,
		Full,
		Underrun_Error,
		Empty_Watermark,
		Almost_Empty,
		Empty,
		DOUT
);

	parameter WR_DATA_WIDTH = 18;
	parameter RD_DATA_WIDTH = 18;
	parameter UPAE_DBITS = 11'd10;
	parameter UPAF_DBITS = 11'd10;

	input wire CLK;
	input wire PUSH, POP;
	input wire [WR_DATA_WIDTH-1:0] DIN;
	input wire Async_Flush;
	output wire [RD_DATA_WIDTH-1:0] DOUT;
	output wire Almost_Full, Almost_Empty;
	output wire Full, Empty;
	output wire Full_Watermark, Empty_Watermark;
	output wire Overrun_Error, Underrun_Error;

 	BRAM2x18_SFIFO  #(
			.WR1_DATA_WIDTH(WR_DATA_WIDTH),
			.RD1_DATA_WIDTH(RD_DATA_WIDTH),
			.UPAE_DBITS1(UPAE_DBITS),
			.UPAF_DBITS1(UPAF_DBITS),
			.WR2_DATA_WIDTH(),
			.RD2_DATA_WIDTH(),
			.UPAE_DBITS2(),
			.UPAF_DBITS2()
			 ) U1
			(
			.DIN1(DIN),
			.PUSH1(PUSH),
			.POP1(POP),
			.CLK1(CLK),
			.Async_Flush1(Async_Flush),
			.Overrun_Error1(Overrun_Error),
			.Full_Watermark1(Full_Watermark),
			.Almost_Full1(Almost_Full),
			.Full1(Full),
			.Underrun_Error1(Underrun_Error),
			.Empty_Watermark1(Empty_Watermark),
			.Almost_Empty1(Almost_Empty),
			.Empty1(Empty),
			.DOUT1(DOUT),

			.DIN2(18'h0),
			.PUSH2(1'b0),
			.POP2(1'b0),
			.CLK2(1'b0),
			.Async_Flush2(1'b0),
			.Overrun_Error2(),
			.Full_Watermark2(),
			.Almost_Full2(),
			.Full2(),
			.Underrun_Error2(),
			.Empty_Watermark2(),
			.Almost_Empty2(),
			.Empty2(),
			.DOUT2()
	);

endmodule

module SFIFO_18K_X2_BLK (
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

	input wire CLK1;
	input wire PUSH1, POP1;
	input wire [WR1_DATA_WIDTH-1:0] DIN1;
	input wire Async_Flush1;
	output wire [RD1_DATA_WIDTH-1:0] DOUT1;
	output wire Almost_Full1, Almost_Empty1;
	output wire Full1, Empty1;
	output wire Full_Watermark1, Empty_Watermark1;
	output wire Overrun_Error1, Underrun_Error1;

	input wire CLK2;
	input wire PUSH2, POP2;
	input wire [WR2_DATA_WIDTH-1:0] DIN2;
	input wire Async_Flush2;
	output wire [RD2_DATA_WIDTH-1:0] DOUT2;
	output wire Almost_Full2, Almost_Empty2;
	output wire Full2, Empty2;
	output wire Full_Watermark2, Empty_Watermark2;
	output wire Overrun_Error2, Underrun_Error2;

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
	(* is_split = 1 *)
	(* is_inferred = 0 *)
	(* port_a1_dwidth = WR1_DATA_WIDTH *)
	(* port_a2_dwidth = WR2_DATA_WIDTH *)
	(* port_b1_dwidth = RD1_DATA_WIDTH *)
	(* port_b2_dwidth = RD2_DATA_WIDTH *)
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

	input wire Push_Clk1, Pop_Clk1;
	input wire PUSH1, POP1;
	input wire [WR1_DATA_WIDTH-1:0] DIN1;
	input wire Async_Flush1;
	output wire [RD1_DATA_WIDTH-1:0] DOUT1;
	output wire Almost_Full1, Almost_Empty1;
	output wire Full1, Empty1;
	output wire Full_Watermark1, Empty_Watermark1;
	output wire Overrun_Error1, Underrun_Error1;

	input wire Push_Clk2, Pop_Clk2;
	input wire PUSH2, POP2;
	input wire [WR2_DATA_WIDTH-1:0] DIN2;
	input wire Async_Flush2;
	output wire [RD2_DATA_WIDTH-1:0] DOUT2;
	output wire Almost_Full2, Almost_Empty2;
	output wire Full2, Empty2;
	output wire Full_Watermark2, Empty_Watermark2;
	output wire Overrun_Error2, Underrun_Error2;

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

	wire [17:0] in_reg1;
	wire [17:0] out_reg1;
	wire [17:0] fifo1_flags;

	wire [17:0] in_reg2;
	wire [17:0] out_reg2;
	wire [17:0] fifo2_flags;

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
	(* port_a_dwidth = WR1_DATA_WIDTH *)
	(* port_b_dwidth = RD1_DATA_WIDTH *)
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

module AFIFO_18K_BLK (
		DIN,
		PUSH,
		POP,
		Push_Clk,
		Pop_Clk,
		Async_Flush,
		Overrun_Error,
		Full_Watermark,
		Almost_Full,
		Full,
		Underrun_Error,
		Empty_Watermark,
		Almost_Empty,
		Empty,
		DOUT
);

	parameter WR_DATA_WIDTH = 18;
	parameter RD_DATA_WIDTH = 18;
	parameter UPAE_DBITS = 11'd10;
	parameter UPAF_DBITS = 11'd10;

	input wire Push_Clk, Pop_Clk;
	input wire PUSH, POP;
	input wire [WR_DATA_WIDTH-1:0] DIN;
	input wire Async_Flush;
	output wire [RD_DATA_WIDTH-1:0] DOUT;
	output wire Almost_Full, Almost_Empty;
	output wire Full, Empty;
	output wire Full_Watermark, Empty_Watermark;
	output wire Overrun_Error, Underrun_Error;

 	BRAM2x18_AFIFO  #(
			.WR1_DATA_WIDTH(WR_DATA_WIDTH),
			.RD1_DATA_WIDTH(RD_DATA_WIDTH),
			.UPAE_DBITS1(UPAE_DBITS),
			.UPAF_DBITS1(UPAF_DBITS),
			.WR2_DATA_WIDTH(),
			.RD2_DATA_WIDTH(),
			.UPAE_DBITS2(),
			.UPAF_DBITS2()
			 ) U1
			(
			.DIN1(DIN),
			.PUSH1(PUSH),
			.POP1(POP),
			.Push_Clk1(Push_Clk),
			.Pop_Clk1(Pop_Clk),
			.Async_Flush1(Async_Flush),
			.Overrun_Error1(Overrun_Error),
			.Full_Watermark1(Full_Watermark),
			.Almost_Full1(Almost_Full),
			.Full1(Full),
			.Underrun_Error1(Underrun_Error),
			.Empty_Watermark1(Empty_Watermark),
			.Almost_Empty1(Almost_Empty),
			.Empty1(Empty),
			.DOUT1(DOUT),

			.DIN2(18'h0),
			.PUSH2(1'b0),
			.POP2(1'b0),
			.Push_Clk2(1'b0),
			.Pop_Clk2(1'b0),
			.Async_Flush2(1'b0),
			.Overrun_Error2(),
			.Full_Watermark2(),
			.Almost_Full2(),
			.Full2(),
			.Underrun_Error2(),
			.Empty_Watermark2(),
			.Almost_Empty2(),
			.Empty2(),
			.DOUT2()
	);

endmodule

module AFIFO_18K_X2_BLK (
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

	input wire Push_Clk1, Pop_Clk1;
	input wire PUSH1, POP1;
	input wire [WR1_DATA_WIDTH-1:0] DIN1;
	input wire Async_Flush1;
	output wire [RD1_DATA_WIDTH-1:0] DOUT1;
	output wire Almost_Full1, Almost_Empty1;
	output wire Full1, Empty1;
	output wire Full_Watermark1, Empty_Watermark1;
	output wire Overrun_Error1, Underrun_Error1;

	input wire Push_Clk2, Pop_Clk2;
	input wire PUSH2, POP2;
	input wire [WR2_DATA_WIDTH-1:0] DIN2;
	input wire Async_Flush2;
	output wire [RD2_DATA_WIDTH-1:0] DOUT2;
	output wire Almost_Full2, Almost_Empty2;
	output wire Full2, Empty2;
	output wire Full_Watermark2, Empty_Watermark2;
	output wire Overrun_Error2, Underrun_Error2;

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

	wire [17:0] in_reg1;
	wire [17:0] out_reg1;
	wire [17:0] fifo1_flags;

	wire [17:0] in_reg2;
	wire [17:0] out_reg2;
	wire [17:0] fifo2_flags;

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
	(* is_split = 1 *)
	(* is_inferred = 0 *)
	(* port_a1_dwidth = WR1_DATA_WIDTH *)
	(* port_a2_dwidth = WR2_DATA_WIDTH *)
	(* port_b1_dwidth = RD1_DATA_WIDTH *)
	(* port_b2_dwidth = RD2_DATA_WIDTH *)
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

module SFIFO_36K_BLK (
		DIN,
		PUSH,
		POP,
		CLK,
		Async_Flush,
		Overrun_Error,
		Full_Watermark,
		Almost_Full,
		Full,
		Underrun_Error,
		Empty_Watermark,
		Almost_Empty,
		Empty,
		DOUT
);

	parameter WR_DATA_WIDTH = 36;
	parameter RD_DATA_WIDTH = 36;
	parameter UPAE_DBITS = 12'd10;
	parameter UPAF_DBITS = 12'd10;

	input wire CLK;
	input wire PUSH, POP;
	input wire [WR_DATA_WIDTH-1:0] DIN;
	input wire Async_Flush;
	output wire [RD_DATA_WIDTH-1:0] DOUT;
	output wire Almost_Full, Almost_Empty;
	output wire Full, Empty;
	output wire Full_Watermark, Empty_Watermark;
	output wire Overrun_Error, Underrun_Error;

	// Fixed mode settings
	localparam [ 0:0] SYNC_FIFO1_i  = 1'd1;
	localparam [ 0:0] FMODE1_i      = 1'd1;
	localparam [ 0:0] POWERDN1_i    = 1'd0;
	localparam [ 0:0] SLEEP1_i      = 1'd0;
	localparam [ 0:0] PROTECT1_i    = 1'd0;
	localparam [11:0] UPAE1_i       = UPAE_DBITS;
	localparam [11:0] UPAF1_i       = UPAF_DBITS;

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

	wire [35:0] in_reg;
	wire [35:0] out_reg;
	wire [17:0] fifo_flags;

	wire [35:0] RD_DATA_INT;

	wire Push_Clk, Pop_Clk;

	assign Push_Clk = CLK;
	assign Pop_Clk = CLK;

	assign Overrun_Error = fifo_flags[0];
	assign Full_Watermark = fifo_flags[1];
	assign Almost_Full = fifo_flags[2];
	assign Full = fifo_flags[3];
	assign Underrun_Error = fifo_flags[4];
	assign Empty_Watermark = fifo_flags[5];
	assign Almost_Empty = fifo_flags[6];
	assign Empty = fifo_flags[7];

	localparam [ 2:0] RMODE_A1_i    = mode(WR_DATA_WIDTH);
	localparam [ 2:0] WMODE_A1_i    = mode(WR_DATA_WIDTH);
	localparam [ 2:0] RMODE_A2_i    = mode(WR_DATA_WIDTH);
	localparam [ 2:0] WMODE_A2_i    = mode(WR_DATA_WIDTH);

	localparam [ 2:0] RMODE_B1_i    = mode(RD_DATA_WIDTH);
	localparam [ 2:0] WMODE_B1_i    = mode(RD_DATA_WIDTH);
	localparam [ 2:0] RMODE_B2_i    = mode(RD_DATA_WIDTH);
	localparam [ 2:0] WMODE_B2_i    = mode(RD_DATA_WIDTH);

	generate
		if (WR_DATA_WIDTH == 36) begin
			assign in_reg[WR_DATA_WIDTH-1:0] = DIN[WR_DATA_WIDTH-1:0];
		end else if (WR_DATA_WIDTH > 18 && WR_DATA_WIDTH < 36) begin
			assign in_reg[WR_DATA_WIDTH+1:18] = DIN[WR_DATA_WIDTH-1:16];
			assign in_reg[17:0] = {2'b00,DIN[15:0]};
		end else if (WR_DATA_WIDTH == 9) begin
			assign in_reg[35:0] = {19'h0, DIN[8], 8'h0, DIN[7:0]};
		end else begin
			assign in_reg[35:WR_DATA_WIDTH]  = 0;
			assign in_reg[WR_DATA_WIDTH-1:0] = DIN[WR_DATA_WIDTH-1:0];
		end
	endgenerate

	generate
		if (RD_DATA_WIDTH == 36) begin
			assign RD_DATA_INT = out_reg;
		end else if (RD_DATA_WIDTH > 18 && RD_DATA_WIDTH < 36) begin
			assign RD_DATA_INT  = {2'b00,out_reg[35:18],out_reg[15:0]};
		end else if (RD_DATA_WIDTH == 9) begin
			assign RD_DATA_INT = { 27'h0, out_reg[16], out_reg[7:0]};
		end else begin
			assign RD_DATA_INT = {18'h0, out_reg[17:0]};
		end
	endgenerate

	assign DOUT[RD_DATA_WIDTH-1 : 0] = RD_DATA_INT[RD_DATA_WIDTH-1 : 0];

	defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b0,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
	};

	(* is_fifo = 1 *)
	(* sync_fifo = 1 *)
	(* is_inferred = 0 *)
	(* is_split = 0 *)
	(* port_a_dwidth = WR_DATA_WIDTH *)
	(* port_b_dwidth = RD_DATA_WIDTH *)
	 TDP36K _TECHMAP_REPLACE_ (
		.RESET_ni(1'b1),
		.WDATA_A1_i(in_reg[17:0]),
		.WDATA_A2_i(in_reg[35:18]),
		.RDATA_A1_o(fifo_flags),
		.RDATA_A2_o(),
		.ADDR_A1_i(14'h0),
		.ADDR_A2_i(14'h0),
		.CLK_A1_i(Push_Clk),
		.CLK_A2_i(1'b0),
		.REN_A1_i(1'b1),
		.REN_A2_i(1'b0),
		.WEN_A1_i(PUSH),
		.WEN_A2_i(1'b0),
		.BE_A1_i(2'b11),
		.BE_A2_i(2'b11),

		.WDATA_B1_i(18'h0),
		.WDATA_B2_i(18'h0),
		.RDATA_B1_o(out_reg[17:0]),
		.RDATA_B2_o(out_reg[35:18]),
		.ADDR_B1_i(14'h0),
		.ADDR_B2_i(14'h0),
		.CLK_B1_i(Pop_Clk),
		.CLK_B2_i(1'b0),
		.REN_B1_i(POP),
		.REN_B2_i(1'b0),
		.WEN_B1_i(1'b0),
		.WEN_B2_i(1'b0),
		.BE_B1_i(2'b11),
		.BE_B2_i(2'b11),

		.FLUSH1_i(Async_Flush),
		.FLUSH2_i(1'b0)
	);

endmodule


module AFIFO_36K_BLK (
		DIN,
		PUSH,
		POP,
		Push_Clk,
		Pop_Clk,
		Async_Flush,
		Overrun_Error,
		Full_Watermark,
		Almost_Full,
		Full,
		Underrun_Error,
		Empty_Watermark,
		Almost_Empty,
		Empty,
		DOUT
);

	parameter WR_DATA_WIDTH = 36;
	parameter RD_DATA_WIDTH = 36;
	parameter UPAE_DBITS = 12'd10;
	parameter UPAF_DBITS = 12'd10;

	input wire Push_Clk, Pop_Clk;
	input wire PUSH, POP;
	input wire [WR_DATA_WIDTH-1:0] DIN;
	input wire Async_Flush;
	output wire [RD_DATA_WIDTH-1:0] DOUT;
	output wire Almost_Full, Almost_Empty;
	output wire Full, Empty;
	output wire Full_Watermark, Empty_Watermark;
	output wire Overrun_Error, Underrun_Error;

	// Fixed mode settings
	localparam [ 0:0] SYNC_FIFO1_i  = 1'd0;
	localparam [ 0:0] FMODE1_i      = 1'd1;
	localparam [ 0:0] POWERDN1_i    = 1'd0;
	localparam [ 0:0] SLEEP1_i      = 1'd0;
	localparam [ 0:0] PROTECT1_i    = 1'd0;
	localparam [11:0] UPAE1_i       = UPAE_DBITS;
	localparam [11:0] UPAF1_i       = UPAF_DBITS;

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

	wire [35:0] in_reg;
	wire [35:0] out_reg;
	wire [17:0] fifo_flags;

	wire [35:0] RD_DATA_INT;
	wire [35:WR_DATA_WIDTH] WR_DATA_CMPL;

	assign Overrun_Error = fifo_flags[0];
	assign Full_Watermark = fifo_flags[1];
	assign Almost_Full = fifo_flags[2];
	assign Full = fifo_flags[3];
	assign Underrun_Error = fifo_flags[4];
	assign Empty_Watermark = fifo_flags[5];
	assign Almost_Empty = fifo_flags[6];
	assign Empty = fifo_flags[7];

	localparam [ 2:0] RMODE_A1_i    = mode(WR_DATA_WIDTH);
	localparam [ 2:0] WMODE_A1_i    = mode(WR_DATA_WIDTH);
	localparam [ 2:0] RMODE_A2_i    = mode(WR_DATA_WIDTH);
	localparam [ 2:0] WMODE_A2_i    = mode(WR_DATA_WIDTH);

	localparam [ 2:0] RMODE_B1_i    = mode(RD_DATA_WIDTH);
	localparam [ 2:0] WMODE_B1_i    = mode(RD_DATA_WIDTH);
	localparam [ 2:0] RMODE_B2_i    = mode(RD_DATA_WIDTH);
	localparam [ 2:0] WMODE_B2_i    = mode(RD_DATA_WIDTH);

	generate
		if (WR_DATA_WIDTH == 36) begin
			assign in_reg[WR_DATA_WIDTH-1:0] = DIN[WR_DATA_WIDTH-1:0];
		end else if (WR_DATA_WIDTH > 18 && WR_DATA_WIDTH < 36) begin
			assign in_reg[WR_DATA_WIDTH+1:18] = DIN[WR_DATA_WIDTH-1:16];
			assign in_reg[17:0] = {2'b00,DIN[15:0]};
		end else if (WR_DATA_WIDTH == 9) begin
			assign in_reg[35:0] = {19'h0, DIN[8], 8'h0, DIN[7:0]};
		end else begin
			assign in_reg[35:WR_DATA_WIDTH]  = 0;
			assign in_reg[WR_DATA_WIDTH-1:0] = DIN[WR_DATA_WIDTH-1:0];
		end
	endgenerate

	generate
		if (RD_DATA_WIDTH == 36) begin
			assign RD_DATA_INT = out_reg;
		end else if (RD_DATA_WIDTH > 18 && RD_DATA_WIDTH < 36) begin
			assign RD_DATA_INT  = {2'b00,out_reg[35:18],out_reg[15:0]};
		end else if (RD_DATA_WIDTH == 9) begin
			assign RD_DATA_INT = { 27'h0, out_reg[16], out_reg[7:0]};
		end else begin
			assign RD_DATA_INT = {18'h0, out_reg[17:0]};
		end
	endgenerate

	assign DOUT[RD_DATA_WIDTH-1 : 0] = RD_DATA_INT[RD_DATA_WIDTH-1 : 0];

	defparam _TECHMAP_REPLACE_.MODE_BITS = { 1'b0,
	UPAF2_i, UPAE2_i, PROTECT2_i, SLEEP2_i, POWERDN2_i, FMODE2_i, WMODE_B2_i, WMODE_A2_i, RMODE_B2_i, RMODE_A2_i, SYNC_FIFO2_i,
	UPAF1_i, UPAE1_i, PROTECT1_i, SLEEP1_i, POWERDN1_i, FMODE1_i, WMODE_B1_i, WMODE_A1_i, RMODE_B1_i, RMODE_A1_i, SYNC_FIFO1_i
	};

	(* is_fifo = 1 *)
	(* sync_fifo = 0 *)
	(* is_inferred = 0 *)
	(* is_split = 0 *)
	(* port_a_dwidth = WR_DATA_WIDTH *)
	(* port_b_dwidth = RD_DATA_WIDTH *)
 	TDP36K _TECHMAP_REPLACE_ (
		.RESET_ni(1'b1),
		.WDATA_A1_i(in_reg[17:0]),
		.WDATA_A2_i(in_reg[35:18]),
		.RDATA_A1_o(fifo_flags),
		.RDATA_A2_o(),
		.ADDR_A1_i(14'h0),
		.ADDR_A2_i(14'h0),
		.CLK_A1_i(Push_Clk),
		.CLK_A2_i(1'b0),
		.REN_A1_i(1'b1),
		.REN_A2_i(1'b0),
		.WEN_A1_i(PUSH),
		.WEN_A2_i(1'b0),
		.BE_A1_i(2'b11),
		.BE_A2_i(2'b11),

		.WDATA_B1_i(18'h0),
		.WDATA_B2_i(18'h0),
		.RDATA_B1_o(out_reg[17:0]),
		.RDATA_B2_o(out_reg[35:18]),
		.ADDR_B1_i(14'h0),
		.ADDR_B2_i(14'h0),
		.CLK_B1_i(Pop_Clk),
		.CLK_B2_i(1'b0),
		.REN_B1_i(POP),
		.REN_B2_i(1'b0),
		.WEN_B1_i(1'b0),
		.WEN_B2_i(1'b0),
		.BE_B1_i(2'b11),
		.BE_B2_i(2'b11),

		.FLUSH1_i(Async_Flush),
		.FLUSH2_i(1'b0)
	);

endmodule

//===============================================================================
module TDP36K_FIFO_ASYNC_A_X9_B_X9_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A_X9_B_X18_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A_X9_B_X36_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A_X18_B_X9_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A_X18_B_X18_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A_X18_B_X36_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A_X36_B_X9_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A_X36_B_X18_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A_X36_B_X36_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X18_B1_X18_A2_X18_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X18_B1_X18_A2_X18_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X18_B1_X18_A2_X9_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X18_B1_X18_A2_X9_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X18_B1_X9_A2_X18_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X18_B1_X9_A2_X18_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X18_B1_X9_A2_X9_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X18_B1_X9_A2_X9_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X9_B1_X18_A2_X18_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X9_B1_X18_A2_X18_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X9_B1_X18_A2_X9_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X9_B1_X18_A2_X9_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X9_B1_X9_A2_X18_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X9_B1_X9_A2_X18_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X9_B1_X9_A2_X9_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_ASYNC_A1_X9_B1_X9_A2_X9_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X9_B_X9_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X9_B_X18_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X9_B_X36_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X18_B_X9_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X18_B_X18_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X18_B_X36_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X36_B_X9_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X36_B_X18_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A_X36_B_X36_nonsplit (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X18_B1_X18_A2_X18_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X18_B1_X18_A2_X18_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X18_B1_X18_A2_X9_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X18_B1_X18_A2_X9_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X18_B1_X9_A2_X18_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X18_B1_X9_A2_X18_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X18_B1_X9_A2_X9_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X18_B1_X9_A2_X9_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X9_B1_X18_A2_X18_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X9_B1_X18_A2_X18_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X9_B1_X18_A2_X9_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X9_B1_X18_A2_X9_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X9_B1_X9_A2_X18_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X9_B1_X9_A2_X18_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X9_B1_X9_A2_X9_B2_X18_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule

module TDP36K_FIFO_SYNC_A1_X9_B1_X9_A2_X9_B2_X9_split (
		RESET_ni,
		WEN_A1_i,   WEN_B1_i,
		REN_A1_i,   REN_B1_i,
		CLK_A1_i,   CLK_B1_i,
		BE_A1_i,    BE_B1_i,
		ADDR_A1_i,  ADDR_B1_i,
		WDATA_A1_i, WDATA_B1_i,
		RDATA_A1_o, RDATA_B1_o,
		FLUSH1_i,
		WEN_A2_i,   WEN_B2_i,
		REN_A2_i,   REN_B2_i,
		CLK_A2_i,   CLK_B2_i,
		BE_A2_i,    BE_B2_i,
		ADDR_A2_i,  ADDR_B2_i,
		WDATA_A2_i, WDATA_B2_i,
		RDATA_A2_o, RDATA_B2_o,
		FLUSH2_i
);
		parameter [80:0] MODE_BITS = 81'd0;

		input wire  RESET_ni;
		input wire  WEN_A1_i, WEN_B1_i;
		input wire  REN_A1_i, REN_B1_i;
		input wire  WEN_A2_i, WEN_B2_i;
		input wire  REN_A2_i, REN_B2_i;

		(* clkbuf_sink *)
		input wire  CLK_A1_i;
		(* clkbuf_sink *)
		input wire  CLK_B1_i;
		(* clkbuf_sink *)
		input wire  CLK_A2_i;
		(* clkbuf_sink *)
		input wire  CLK_B2_i;

		input wire  [ 1:0] BE_A1_i,    BE_B1_i;
		input wire  [14:0] ADDR_A1_i,  ADDR_B1_i;
		input wire  [17:0] WDATA_A1_i, WDATA_B1_i;
		output wire [17:0] RDATA_A1_o, RDATA_B1_o;

		input wire  FLUSH1_i;

		input wire  [ 1:0] BE_A2_i,    BE_B2_i;
		input wire  [13:0] ADDR_A2_i,  ADDR_B2_i;
		input wire  [17:0] WDATA_A2_i, WDATA_B2_i;
		output wire [17:0] RDATA_A2_o, RDATA_B2_o;

		input wire  FLUSH2_i;

		TDP36K #(.MODE_BITS(MODE_BITS)) bram (
				.RESET_ni   (RESET_ni),
				.WEN_A1_i   (WEN_A1_i),   .WEN_B1_i   (WEN_B1_i),
				.REN_A1_i   (REN_A1_i),   .REN_B1_i   (REN_B1_i),
				.CLK_A1_i   (CLK_A1_i),   .CLK_B1_i   (CLK_B1_i),
				.BE_A1_i    (BE_A1_i),    .BE_B1_i    (BE_B1_i),
				.ADDR_A1_i  (ADDR_A1_i),  .ADDR_B1_i  (ADDR_B1_i),
				.WDATA_A1_i (WDATA_A1_i), .WDATA_B1_i (WDATA_B1_i),
				.RDATA_A1_o (RDATA_A1_o), .RDATA_B1_o (RDATA_B1_o),
				.FLUSH1_i   (FLUSH1_i),
				.WEN_A2_i   (WEN_A2_i),   .WEN_B2_i   (WEN_B2_i),
				.REN_A2_i   (REN_A2_i),   .REN_B2_i   (REN_B2_i),
				.CLK_A2_i   (CLK_A2_i),   .CLK_B2_i   (CLK_B2_i),
				.BE_A2_i    (BE_A2_i),    .BE_B2_i    (BE_B2_i),
				.ADDR_A2_i  (ADDR_A2_i),  .ADDR_B2_i  (ADDR_B2_i),
				.WDATA_A2_i (WDATA_A2_i), .WDATA_B2_i (WDATA_B2_i),
				.RDATA_A2_o (RDATA_A2_o), .RDATA_B2_o (RDATA_B2_o),
				.FLUSH2_i   (FLUSH2_i)
		);

`ifdef SDF_SIM
	specify
		(FLUSH1_i => RDATA_A1_o[0]) = 0;
		(FLUSH1_i => RDATA_A1_o[1]) = 0;
		(FLUSH1_i => RDATA_A1_o[2]) = 0;
		(FLUSH1_i => RDATA_A1_o[3]) = 0;
		(FLUSH1_i => RDATA_A1_o[4]) = 0;
		(FLUSH1_i => RDATA_A1_o[5]) = 0;
		(FLUSH1_i => RDATA_A1_o[6]) = 0;
		(FLUSH1_i => RDATA_A1_o[7]) = 0;
		(FLUSH2_i => RDATA_A2_o[0]) = 0;
		(FLUSH2_i => RDATA_A2_o[1]) = 0;
		(FLUSH2_i => RDATA_A2_o[2]) = 0;
		(FLUSH2_i => RDATA_A2_o[3]) = 0;
		(FLUSH2_i => RDATA_A2_o[4]) = 0;
		(FLUSH2_i => RDATA_A2_o[5]) = 0;
		(FLUSH2_i => RDATA_A2_o[6]) = 0;
		(FLUSH2_i => RDATA_A2_o[7]) = 0;
		(negedge RESET_ni => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(negedge RESET_ni => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(negedge RESET_ni => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(negedge RESET_ni => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		(posedge CLK_A1_i => (RDATA_A1_o +: WDATA_A1_i)) = 0;
		(posedge CLK_B1_i => (RDATA_B1_o +: WDATA_B1_i)) = 0;
		(posedge CLK_A2_i => (RDATA_A2_o +: WDATA_A2_i)) = 0;
		(posedge CLK_B2_i => (RDATA_B2_o +: WDATA_B2_i)) = 0;
		$setuphold(posedge CLK_A1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A1_i, FLUSH1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WEN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, REN_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, BE_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, ADDR_A1_i, 0, 0);
		$setuphold(posedge CLK_A1_i, WDATA_A1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B1_i, WEN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, REN_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, BE_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, ADDR_B1_i, 0, 0);
		$setuphold(posedge CLK_B1_i, WDATA_B1_i, 0, 0);
		$setuphold(posedge CLK_A2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_A2_i, FLUSH2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WEN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, REN_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, BE_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, ADDR_A2_i, 0, 0);
		$setuphold(posedge CLK_A2_i, WDATA_A2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, RESET_ni, 0, 0);
		$setuphold(posedge CLK_B2_i, WEN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, REN_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, BE_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, ADDR_B2_i, 0, 0);
		$setuphold(posedge CLK_B2_i, WDATA_B2_i, 0, 0);
	endspecify
`endif

endmodule