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
module _80_gw1n_alu(A, B, CI, BI, X, Y, CO);
   parameter A_SIGNED = 0;
   parameter B_SIGNED = 0;
   parameter A_WIDTH = 1;
   parameter B_WIDTH = 1;
   parameter Y_WIDTH = 1;

   input [A_WIDTH-1:0] A;
   input [B_WIDTH-1:0] B;
   output [Y_WIDTH-1:0] X, Y;

   input 		CI, BI;
   output [Y_WIDTH-1:0] CO;

   wire 		_TECHMAP_FAIL_ = Y_WIDTH <= 2;

   wire [Y_WIDTH-1:0] 	A_buf, B_buf;
   \$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
   \$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

   wire [Y_WIDTH-1:0] 	AA = A_buf;
   wire [Y_WIDTH-1:0] 	BB = B_buf;
   wire [Y_WIDTH-1:0] 	C = {CO, CI};

   genvar 		i;
   generate for (i = 0; i < Y_WIDTH; i = i + 1) begin:slice
      ALU #(.ALU_MODE(2)) // ADDSUB I3 ? add : sub
      alu(.I0(AA[i]),
	  .I1(BB[i]),
	  .I3(~BI),
	  .CIN(C[i]),
	  .COUT(CO[i]),
	  .SUM(Y[i])
	  );
   end endgenerate
   assign X = AA ^ BB;
endmodule

