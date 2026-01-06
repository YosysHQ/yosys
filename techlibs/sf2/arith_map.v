/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

