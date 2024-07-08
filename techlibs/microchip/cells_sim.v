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

// Macro Library for PolarFire https://coredocs.s3.amazonaws.com/Libero/2021_2/Tool/pf_mlg.pdf

module AND2 (
	input A, B,
	output Y
);
	assign Y = A & B;
endmodule

module AND3 (
	input A, B, C,
	output Y
);
	assign Y = A & B & C;
endmodule

module AND4 (
	input A, B, C, D,
	output Y
);
	assign Y = A & B & C & D;
endmodule

(* abc9_lut=1 *)
module CFG1 (
	output Y,
	input A
);
	parameter [1:0] INIT = 2'h0;
	assign Y = INIT >> A;
	specify
		(A => Y) = 127;
	endspecify
endmodule

(* abc9_lut=1 *)
module CFG2 (
	output Y,
	input A,
	input B
);
	parameter [3:0] INIT = 4'h0;
	assign Y = INIT >> {B, A};
	specify
		(A => Y) = 238;
		(B => Y) = 127;
	endspecify
endmodule

(* abc9_lut=1 *)
module CFG3 (
	output Y,
	input A,
	input B,
	input C
);
	parameter [7:0] INIT = 8'h0;
	assign Y = INIT >> {C, B, A};
	specify
		(A => Y) = 407;
		(B => Y) = 238;
		(C => Y) = 127;
	endspecify
endmodule

(* abc9_lut=1 *)
module CFG4 (
	output Y,
	input A,
	input B,
	input C,
	input D
);
	parameter [15:0] INIT = 16'h0;
	assign Y = INIT >> {D, C, B, A};
	specify
		(A => Y) = 472;
		(B => Y) = 407;
		(C => Y) = 238;
		(D => Y) = 127;
	endspecify
endmodule

module BUFF (
	input A,
	output Y
);
	assign Y = A;
endmodule

module BUFD (
	input A,
	output Y
);
	assign Y = A;
endmodule

module CLKINT (
	input A,
	(* clkbuf_driver *)
	output Y
);
	assign Y = A;
endmodule

module CLKINT_PRESERVE (
	input A,
	(* clkbuf_driver *)
	output Y
);
	assign Y = A;
endmodule

module GCLKINT (
	input A, EN,
	(* clkbuf_driver *)
	output Y
);
	assign Y = A & EN;
endmodule

module RCLKINT (
	input A,
	(* clkbuf_driver *)
	output Y
);
	assign Y = A;
endmodule

module RGCLKINT (
	input A, EN,
	(* clkbuf_driver *)
	output Y
);
	assign Y = A & EN;
endmodule

// sequential elements

// MICROCHIP_SYNC_SET_DFF and MICROCHIP_SYNC_RESET_DFF are intermediate cell types to implement the simplification idiom for abc9 flow 
//	see: https://yosyshq.readthedocs.io/projects/yosys/en/latest/yosys_internals/extending_yosys/abc_flow.html

(* abc9_flop, lib_whitebox *)
module MICROCHIP_SYNC_SET_DFF(
	input D,
	input CLK,
	input Set,
	input En,
	output reg Q);
	parameter [0:0] INIT = 1'b0; // unused

	always @(posedge CLK) begin
		if (En == 1) begin
			if (Set == 0)
				Q <= 1;
			else
				Q <= D;
		end
	end

	specify
		$setup(D , posedge CLK &&& En && Set, 0); // neg setup not supported?
		$setup(En, posedge CLK, 109);
		$setup(Set, posedge CLK &&& En, 404);
		if (En && !Set) (posedge CLK => (Q : 1'b1)) = 303;
		if (En && Set) (posedge CLK => (Q : D)) = 303;
	endspecify
endmodule

(* abc9_flop, lib_whitebox *)
module MICROCHIP_SYNC_RESET_DFF(
	input D,
	input CLK,
	input Reset,
	input En,
	output reg Q);
	parameter [0:0] INIT = 1'b0; // unused

	always @(posedge CLK) begin
		if (En == 1) begin
			if (Reset == 0) 
				Q <= 0;
			else
				Q <= D;
		end
	end

	specify
		$setup(D , posedge CLK &&& En && Reset, 0); // neg setup not supported?
		$setup(En, posedge CLK, 109);
		$setup(Reset, posedge CLK &&& En, 404);
		if (En && !Reset) (posedge CLK => (Q : 1'b0)) = 303;
		if (En && Reset) (posedge CLK => (Q : D)) = 303;
	endspecify
endmodule

module SLE (
	output Q,
	input ADn,
	input ALn,
	(* clkbuf_sink *)
	input CLK,
	input D,
	input LAT,
	input SD,
	input EN,
	input SLn
);
	reg q_latch, q_ff;

	always @(posedge CLK, negedge ALn) begin
		if (!ALn) begin
			q_ff <= !ADn;
		end else if (EN) begin
			if (!SLn)
				q_ff <= SD;
			else
				q_ff <= D;
		end
	end

	always @* begin
		if (!ALn) begin
			q_latch <= !ADn;
		end else if (CLK && EN) begin
			if (!SLn)
				q_ff <= SD;
			else
				q_ff <= D;
		end
	end

	assign Q = LAT ? q_latch : q_ff;
endmodule

(* abc9_box, lib_whitebox *)
module ARI1 (
	(* abc9_carry *)
	input FCI,
	(* abc9_carry *)
	output FCO,

	input A, B, C, D, 
	output Y, S
);
	parameter [19:0] INIT = 20'h0;
	wire [2:0] Fsel = {D, C, B};
	wire F0 = INIT[Fsel];
	wire F1 = INIT[8 + Fsel];
	wire Yout = A ? F1 : F0;
	assign Y = Yout;
	assign S = FCI ^ Yout;
	wire G = INIT[16] ? (INIT[17] ? F1 : F0) : INIT[17];
	wire P = INIT[19] ? 1'b1 : (INIT[18] ? Yout : 1'b0);
	assign FCO = P ? FCI : G;
	
	specify
		//pin to pin path delay 
		(A => Y )	= 472;
		(B => Y )	= 407;
		(C => Y )	= 238;
		(D => Y )	= 127;
		(A => S )	= 572;
		(B => S )	= 507;
		(C => S )	= 338;
		(D => S )	= 227;
		(FCI => S ) = 100;
		(A => FCO ) = 522;
		(B => FCO ) = 457;
		(C => FCO ) = 288;
		(D => FCO ) = 177;
		(FCI => FCO ) = 50;
	endspecify
endmodule

(* blackbox *)
module GCLKBUF (
	(* iopad_external_pin *)
	input PAD,
	input EN,
	(* clkbuf_driver *)
	output Y
);
endmodule

(* blackbox *)
module GCLKBUF_DIFF (
	(* iopad_external_pin *)
	input PADP,
	(* iopad_external_pin *)
	input PADN,
	input EN,
	(* clkbuf_driver *)
	output Y
);
endmodule

module INV (
	input A,
	output Y
);
	assign Y = !A;
endmodule

module INVD (
	input A,
	output Y
);
	assign Y = !A;
endmodule

module MX2 (
	input A, B, S,
	output Y
);
	assign Y = S ? B : A;
endmodule

module MX4 (
	input D0, D1, D2, D3, S0, S1,
	output Y
);
	assign Y = S1 ? (S0 ? D3 : D2) : (S0 ? D1 : D0);
endmodule

module NAND2 (
	input A, B,
	output Y
);
	assign Y = !(A & B);
endmodule

module NAND3 (
	input A, B, C,
	output Y
);
	assign Y = !(A & B & C);
endmodule

module NAND4 (
	input A, B, C, D,
	output Y
);
	assign Y = !(A & B & C & D);
endmodule

module NOR2 (
	input A, B,
	output Y
);
	assign Y = !(A | B);
endmodule

module NOR3 (
	input A, B, C,
	output Y
);
	assign Y = !(A | B | C);
endmodule

module NOR4 (
	input A, B, C, D,
	output Y
);
	assign Y = !(A | B | C | D);
endmodule

module OR2 (
	input A, B,
	output Y
);
	assign Y = A | B;
endmodule

module OR3 (
	input A, B, C,
	output Y
);
	assign Y = A | B | C;
endmodule

module OR4 (
	input A, B, C, D,
	output Y
);
	assign Y = A | B | C | D;
endmodule

module XOR2 (
	input A, B,
	output Y
);
	assign Y = A ^ B;
endmodule

module XOR3 (
	input A, B, C,
	output Y
);
	assign Y = A ^ B ^ C;
endmodule

module XOR4 (
	input A, B, C, D,
	output Y
);
	assign Y = A ^ B ^ C ^ D;
endmodule

module XOR8 (
	input A, B, C, D, E, F, G, H,
	output Y
);
	assign Y = A ^ B ^ C ^ D ^ E ^ F ^ G ^ H;
endmodule

// module UJTAG

module BIBUF (
	input D,
	input E,
	(* iopad_external_pin *)
	inout PAD,
	output Y
);
	parameter IOSTD = "";
	assign PAD = E ? D : 1'bz;
	assign Y = PAD;
endmodule

(* blackbox *)
module BIBUF_DIFF (
	input D,
	input E,
	(* iopad_external_pin *)
	inout PADP,
	(* iopad_external_pin *)
	inout PADN,
	output Y
);
	parameter IOSTD = "";
endmodule

module CLKBIBUF (
	input D,
	input E,
	(* iopad_external_pin *)
	inout PAD,
	(* clkbuf_driver *)
	output Y
);
	parameter IOSTD = "";
	assign PAD = E ? D : 1'bz;
	assign Y = PAD;
endmodule

module CLKBUF (
	(* iopad_external_pin *)
	input PAD,
	(* clkbuf_driver *)
	output Y
);
	parameter IOSTD = "";
	assign Y = PAD;
	specify
	 	(PAD => Y) = 50;
	endspecify
endmodule

(* blackbox *)
module CLKBUF_DIFF (
	(* iopad_external_pin *)
	input PADP,
	(* iopad_external_pin *)
	input PADN,
	(* clkbuf_driver *)
	output Y
);
	parameter IOSTD = "";
endmodule

module INBUF (
	(* iopad_external_pin *)
	input PAD,
	output Y
);
	parameter IOSTD = "";
	assign Y = PAD;
endmodule

(* blackbox *)
module INBUF_DIFF (
	(* iopad_external_pin *)
	input PADP,
	(* iopad_external_pin *)
	input PADN,
	output Y
);
	parameter IOSTD = "";
endmodule

module OUTBUF (
	input D,
	(* iopad_external_pin *)
	output PAD
);
	parameter IOSTD = "";
	assign PAD = D;
endmodule

(* blackbox *)
module OUTBUF_DIFF (
	input D,
	(* iopad_external_pin *)
	output PADP,
	(* iopad_external_pin *)
	output PADN
);
	parameter IOSTD = "";
endmodule

module TRIBUFF (
	input D,
	input E,
	(* iopad_external_pin *)
	output PAD
);
	parameter IOSTD = "";
	assign PAD = E ? D : 1'bz;
endmodule

(* blackbox *)
module TRIBUFF_DIFF (
	input D,
	input E,
	(* iopad_external_pin *)
	output PADP,
	(* iopad_external_pin *)
	output PADN
);
	parameter IOSTD = "";
endmodule

(* blackbox *)
module MACC_PA (
	input DOTP,
	input SIMD,
	input OVFL_CARRYOUT_SEL,
	input CLK,
	input AL_N,
	input [17:0] A,
	input A_BYPASS,
	input A_SRST_N,
	input A_EN,
	input [17:0] B,
	input B_BYPASS,
	input B_SRST_N,
	input B_EN,
	input [17:0] D,
	input D_BYPASS,
	input D_ARST_N,
	input D_SRST_N,
	input D_EN,
	input CARRYIN,
	input [47:0] C,
	input C_BYPASS,
	input C_ARST_N,
	input C_SRST_N,
	input C_EN,
	input [47:0] CDIN,
	output [47:0] P,
	output OVFL_CARRYOUT,
	input P_BYPASS,
	input P_SRST_N,
	input P_EN,
	output [47:0] CDOUT,
	input PASUB,
	input PASUB_BYPASS,
	input PASUB_AD_N,
	input PASUB_SL_N,
	input PASUB_SD_N,
	input PASUB_EN,
	input [1:0] CDIN_FDBK_SEL,
	input CDIN_FDBK_SEL_BYPASS,
	input [1:0] CDIN_FDBK_SEL_AD_N,
	input CDIN_FDBK_SEL_SL_N,
	input [1:0] CDIN_FDBK_SEL_SD_N,
	input CDIN_FDBK_SEL_EN,
	input ARSHFT17,
	input ARSHFT17_BYPASS,
	input ARSHFT17_AD_N,
	input ARSHFT17_SL_N,
	input ARSHFT17_SD_N,
	input ARSHFT17_EN,
	input SUB,
	input SUB_BYPASS,
	input SUB_AD_N,
	input SUB_SL_N,
	input SUB_SD_N,
	input SUB_EN
);
endmodule

(* blackbox *)
module RAM1K20 (
	input 	[13:0] 	A_ADDR,
	input 	[2:0]	A_BLK_EN,
	input			A_CLK,
	input 	[19:0]	A_DIN,
	output	[19:0]	A_DOUT,
	input 	[1:0]	A_WEN,
	input			A_REN,
	input 	[2:0]	A_WIDTH,
	input 	[1:0]	A_WMODE,
	input 			A_BYPASS,
	input 			A_DOUT_EN,
	input 			A_DOUT_SRST_N,
	input 			A_DOUT_ARST_N,
	input 	[13:0]	B_ADDR,
	input 	[2:0]	B_BLK_EN,
	input			B_CLK,
	input 	[19:0] 	B_DIN,
	output	[19:0]	B_DOUT,
	input 	[1:0]	B_WEN,
	input			B_REN,
	input 	[2:0]	B_WIDTH,
	input 	[1:0]	B_WMODE,
	input			B_BYPASS,
	input			B_DOUT_EN,
	input			B_DOUT_SRST_N,
	input			B_DOUT_ARST_N,
	input			ECC_EN, 
	input			ECC_BYPASS,
	output			SB_CORRECT,
	output			DB_DETECT,
	input			BUSY_FB,
	output			ACCESS_BUSY
);
parameter INIT0 = 1024'h0;
parameter INIT1 = 1024'h0;
parameter INIT2 = 1024'h0;
parameter INIT3 = 1024'h0;
parameter INIT4 = 1024'h0;
parameter INIT5 = 1024'h0;
parameter INIT6 = 1024'h0;
parameter INIT7 = 1024'h0;
parameter INIT8 = 1024'h0;
parameter INIT9 = 1024'h0;
parameter INIT10 = 1024'h0;
parameter INIT11 = 1024'h0;
parameter INIT12 = 1024'h0;
parameter INIT13 = 1024'h0;
parameter INIT14 = 1024'h0;
parameter INIT15 = 1024'h0;
parameter INIT16 = 1024'h0;
parameter INIT17 = 1024'h0;
parameter INIT18 = 1024'h0;
parameter INIT19 = 1024'h0;
endmodule

(* blackbox *)
module RAM64x12 (
	input			R_CLK,
	input [5:0]		R_ADDR,
	input			R_ADDR_BYPASS,
	input			R_ADDR_EN,
	input 			R_ADDR_SL_N,
	input			R_ADDR_SD,
	input			R_ADDR_AL_N, 
	input			R_ADDR_AD_N,
	input			BLK_EN,
	output [11:0]	R_DATA,
	input			R_DATA_BYPASS,
	input	 		R_DATA_EN,
	input	 		R_DATA_SL_N,
	input	 		R_DATA_SD,
	input	 		R_DATA_AL_N,
	input	 		R_DATA_AD_N,

	input		W_CLK,
	input [5:0]	W_ADDR,
	input [11:0]W_DATA,
	input		W_EN,

	input		BUSY_FB,
	output		ACCESS_BUSY
);
parameter INIT0 = 64'h0;
parameter INIT1 = 64'h0;
parameter INIT2 = 64'h0;
parameter INIT3 = 64'h0;
parameter INIT4 = 64'h0;
parameter INIT5 = 64'h0;
parameter INIT6 = 64'h0;
parameter INIT7 = 64'h0;
parameter INIT8 = 64'h0;
parameter INIT9 = 64'h0;
parameter INIT10 = 64'h0;
parameter INIT11 = 64'h0;

endmodule