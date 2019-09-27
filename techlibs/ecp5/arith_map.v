/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2018  David Shah <dave@ds0.me>
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
module _80_ecp5_alu (A, B, CI, BI, X, Y, CO);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	output [Y_WIDTH-1:0] CO;

	wire _TECHMAP_FAIL_ = Y_WIDTH <= 4;

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

	wire [Y_WIDTH2-1:0] AA = A_buf;
	wire [Y_WIDTH2-1:0] BB = BI ? ~B_buf : B_buf;
	wire [Y_WIDTH2-1:0] BX = B_buf;
	wire [Y_WIDTH2-1:0] C = {CO, CI};
	wire [Y_WIDTH2-1:0] FCO, Y1;

	genvar i;
	generate for (i = 0; i < Y_WIDTH2; i = i + 2) begin:slice
		CCU2C #(
			.INIT0(16'b1001011010101010),
			.INIT1(16'b1001011010101010),
			.INJECT1_0("NO"),
			.INJECT1_1("NO")
	   ) ccu2c_i (
			.CIN(C[i]),
			.A0(AA[i]), .B0(BX[i]), .C0(BI), .D0(1'b1),
			.A1(AA[i+1]), .B1(BX[i+1]), .C1(BI), .D1(1'b1),
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
