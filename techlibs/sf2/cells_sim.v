// https://coredocs.s3.amazonaws.com/Libero/12_0_0/Tool/sf2_mlg.pdf

module ADD2 (

	input A, B,
	output Y
);
	assign Y = A & B;
endmodule

module ADD3 (
	input A, B, C,
	output Y
);
	assign Y = A & B & C;
endmodule

module ADD4 (
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
	output Y
);
	assign Y = A;
endmodule

module CLKINT_PRESERVE (
	input A,
	output Y
);
	assign Y = A;
endmodule

module GCLKINT (
	input A, EN,
	output Y
);
	assign Y = A & EN;
endmodule

module RCLKINT (
	input A,
	output Y
);
	assign Y = A;
endmodule

module RGCLKINT (
	input A, EN,
	output Y
);
	assign Y = A & EN;
endmodule

module SLE (
	output Q,
	input ADn,
	input ALn,
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

// module AR1
// module FCEND_BUFF
// module FCINIT_BUFF
// module FLASH_FREEZE
// module OSCILLATOR
// module SYSRESET
// module SYSCTRL_RESET_STATUS
// module LIVE_PROBE_FB
// module GCLKBUF
// module GCLKBUF_DIFF
// module GCLKBIBUF
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
// module BIBUF
// module BIBUF_DIFF
// module CLKBIBUF

module CLKBUF (
	input PAD,
	output Y
);
	assign Y = PAD;
endmodule

// module CLKBUF_DIFF

module INBUF (
	input PAD,
	output Y
);
	assign Y = PAD;
endmodule

// module INBUF_DIFF

module OUTBUF (
	input D,
	output PAD
);
	assign PAD = D;
endmodule

// module OUTBUF_DIFF
// module TRIBUFF
// module TRIBUFF_DIFF
// module DDR_IN
// module DDR_OUT
// module RAM1K18
// module RAM64x18
// module MACC
