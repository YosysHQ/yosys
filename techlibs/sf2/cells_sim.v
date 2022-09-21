// https://coredocs.s3.amazonaws.com/Libero/12_0_0/Tool/sf2_mlg.pdf

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

module CFG1 (
	output Y,
	input A
);
	parameter [1:0] INIT = 2'h0;
	assign Y = INIT >> A;
endmodule

module CFG2 (
	output Y,
	input A,
	input B
);
	parameter [3:0] INIT = 4'h0;
	assign Y = INIT >> {B, A};
endmodule

module CFG3 (
	output Y,
	input A,
	input B,
	input C
);
	parameter [7:0] INIT = 8'h0;
	assign Y = INIT >> {C, B, A};
endmodule

module CFG4 (
	output Y,
	input A,
	input B,
	input C,
	input D
);
	parameter [15:0] INIT = 16'h0;
	assign Y = INIT >> {D, C, B, A};
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

module ARI1 (
	input A, B, C, D, FCI,
	output Y, S, FCO
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
endmodule

// module FCEND_BUFF
// module FCINIT_BUFF
// module FLASH_FREEZE
// module OSCILLATOR
// module SYSCTRL_RESET_STATUS
// module LIVE_PROBE_FB

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

(* blackbox *)
module GCLKBIBUF (
	input D,
	input E,
	input EN,
	(* iopad_external_pin *)
	inout PAD,
	(* clkbuf_driver *)
	output Y
);
endmodule

// module DFN1
// module DFN1C0
// module DFN1E1
// module DFN1E1C0
// module DFN1E1P0
// module DFN1P0
// module DLN1
// module DLN1C0
// module DLN1P0

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

// module DDR_IN
// module DDR_OUT
// module RAM1K18
// module RAM64x18
// module MACC

(* blackbox *)
module SYSRESET (
	(* iopad_external_pin *)
	input  DEVRST_N,
	output POWER_ON_RESET_N);
endmodule


(* blackbox *)
module XTLOSC (
	(* iopad_external_pin *)
	input  XTL,
	output CLKOUT);
	parameter [1:0] MODE = 2'h3;
	parameter real FREQUENCY = 20.0;
endmodule

(* blackbox *)
module RAM1K18 (
	input [13:0]  A_ADDR,
	input [2:0]   A_BLK,
	(* clkbuf_sink *)
	input	      A_CLK,
	input [17:0]  A_DIN,
	output [17:0] A_DOUT,
	input [1:0]   A_WEN,
	input [2:0]   A_WIDTH,
	input	      A_WMODE,
	input	      A_ARST_N,
	input	      A_DOUT_LAT,
	input	      A_DOUT_ARST_N,
	(* clkbuf_sink *)
	input	      A_DOUT_CLK,
	input	      A_DOUT_EN,
	input	      A_DOUT_SRST_N,

	input [13:0]  B_ADDR,
	input [2:0]   B_BLK,
	(* clkbuf_sink *)
	input	      B_CLK,
	input [17:0]  B_DIN,
	output [17:0] B_DOUT,
	input [1:0]   B_WEN,
	input [2:0]   B_WIDTH,
	input	      B_WMODE,
	input	      B_ARST_N,
	input	      B_DOUT_LAT,
	input	      B_DOUT_ARST_N,
	(* clkbuf_sink *)
	input	      B_DOUT_CLK,
	input	      B_DOUT_EN,
	input	      B_DOUT_SRST_N,

	input	      A_EN,
	input	      B_EN,
	input	      SII_LOCK,
	output	      BUSY);
endmodule

(* blackbox *)
module RAM64x18 (
	input [9:0]   A_ADDR,
	input [1:0]   A_BLK,
	input [2:0]   A_WIDTH,
	output [17:0] A_DOUT,
	input	      A_DOUT_ARST_N,
	(* clkbuf_sink *)
	input	      A_DOUT_CLK,
	input	      A_DOUT_EN,
	input	      A_DOUT_LAT,
	input	      A_DOUT_SRST_N,
	(* clkbuf_sink *)
	input	      A_ADDR_CLK,
	input	      A_ADDR_EN,
	input	      A_ADDR_LAT,
	input	      A_ADDR_SRST_N,
	input	      A_ADDR_ARST_N,

	input [9:0]   B_ADDR,
	input [1:0]   B_BLK,
	input [2:0]   B_WIDTH,
	output [17:0] B_DOUT,
	input	      B_DOUT_ARST_N,
	(* clkbuf_sink *)
	input	      B_DOUT_CLK,
	input	      B_DOUT_EN,
	input	      B_DOUT_LAT,
	input	      B_DOUT_SRST_N,
	(* clkbuf_sink *)
	input	      B_ADDR_CLK,
	input	      B_ADDR_EN,
	input	      B_ADDR_LAT,
	input	      B_ADDR_SRST_N,
	input	      B_ADDR_ARST_N,

	input [9:0]   C_ADDR,
	(* clkbuf_sink *)
	input	      C_CLK,
	input [17:0]  C_DIN,
	input	      C_WEN,
	input [1:0]   C_BLK,
	input [2:0]   C_WIDTH,

	input	      A_EN,
	input	      B_EN,
	input	      C_EN,
	input	      SII_LOCK,
	output	      BUSY);
endmodule
