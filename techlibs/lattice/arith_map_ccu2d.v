/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018  gatecat <gatecat@ds0.me>
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
module _80_ccu2d_alu (A, B, CI, BI, X, Y, CO);
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

	wire _TECHMAP_FAIL_ = Y_WIDTH <= 4;

	(* force_downto *)
	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	function integer round_up2;
		input integer N;
		begin
			round_up2 = ((N + 1) / 2) * 2;
		end
	endfunction

	localparam Y_WIDTH2 = round_up2(Y_WIDTH);

	(* force_downto *)
	wire [Y_WIDTH2-1:0] AA = A_buf;
	(* force_downto *)
	wire [Y_WIDTH2-1:0] BB = BI ? ~B_buf : B_buf;
	(* force_downto *)
	wire [Y_WIDTH2-1:0] BX = B_buf;
	(* force_downto *)
	wire [Y_WIDTH2-1:0] C = {CO, CI};
	(* force_downto *)
	wire [Y_WIDTH2-1:0] FCO, Y1;

	genvar i;
	generate for (i = 0; i < Y_WIDTH2; i = i + 2) begin:slice
		CCU2D #(
			.INIT0(16'b0101_1010_1001_0110),
			.INIT1(16'b0101_1010_1001_0110),
			.INJECT1_0("NO"),
			.INJECT1_1("NO")
		) ccu2d_i (
			.CIN(C[i]),
			.A0(AA[i]), .B0(BX[i]), .C0(BI), .D0(1'b0),
			.A1(AA[i+1]), .B1(BX[i+1]), .C1(BI), .D1(1'b0),
			.S0(Y[i]), .S1(Y1[i]),
			.COUT(FCO[i])
		);

		assign CO[i] = (AA[i] && BB[i]) || (C[i] && (AA[i] || BB[i]));
		if (i+1 < Y_WIDTH) begin
			assign CO[i+1] = FCO[i];
			assign Y[i+1] = Y1[i];
		end
	end endgenerate

	assign X = AA ^ BB;
endmodule
