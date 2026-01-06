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

// Based on Macro Library for PolarFire https://coredocs.s3.amazonaws.com/Libero/2021_2/Tool/pf_mlg.pdf
// NOTE: prefix module names with \$__ so that mapping prioritizes these cells over internal Yosys cells


(* techmap_celltype = "$_MUX4_" *)
module \$__microchip_MUX4_ (A, B, C, D, S, T, Y);
	input A, B, C, D, S, T;
	output Y;
	MX4 _TECHMAP_REPLACE_.MUX4(.D3(D), .D2(C), .D1(B), .D0(A), .S1(T), .S0(S), .Y(Y));

endmodule


(* techmap_celltype = "$reduce_xor" *)
module \$__microchip_XOR8_ (A, Y);
	parameter A_SIGNED = 1;
	parameter A_WIDTH = 8;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	output [Y_WIDTH-1:0] Y;

	// check if mapping should proceed
	generate
		if (A_WIDTH != 8 || A_SIGNED || Y_WIDTH != 1) begin
			wire _TECHMAP_FAIL_ = 1;
		end
	endgenerate


	XOR8 _TECHMAP_REPLACE_.XOR8 (.A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]), .E(A[4]), .F(A[5]), .G(A[6]), .H(A[7]), .Y(Y));

	
endmodule

(* techmap_celltype = "$alu" *)
module \$__SF2_ALU (A, B, CI, BI, X, Y, CO);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	(* force_downto *)
	output [Y_WIDTH-1:0] CO;

	wire _TECHMAP_FAIL_ = Y_WIDTH <= 2;

	(* force_downto *)
	wire [Y_WIDTH-1:0] AA, BB;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(AA));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(BB));

	(* force_downto *)
	wire [Y_WIDTH-1:0] C = {CO, CI};

	genvar i;
	generate for (i = 0; i < Y_WIDTH; i = i + 1) begin:slice
		ARI1 #(
			// See section 1.4 of PolarFire Macro Library

			// G = F1 = A[i] & (B[i]^BI)
			// Y = F0 = A[i]^B[i]^BI
			// P = Y
			//		 ADCB
			.INIT(20'b 01_11_0010_1000_1001_0110)
		) carry (
			.A(1'b0),
			.B(AA[i]),
			.C(BB[i]),
			.D(BI),
			.FCI(C[i]),
			.Y(X[i]),
			.S(Y[i]),
			.FCO(CO[i])
		);
	end endgenerate
endmodule

