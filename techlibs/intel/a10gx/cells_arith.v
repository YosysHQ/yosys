/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

// NOTE: This is still WIP.
(* techmap_celltype = "$alu" *)
module _80_altera_a10gx_alu (A, B, CI, BI, X, Y, CO);
   parameter A_SIGNED = 0;
   parameter B_SIGNED = 0;
   parameter A_WIDTH  = 1;
   parameter B_WIDTH  = 1;
   parameter Y_WIDTH  = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	//output [Y_WIDTH-1:0] CO;
        output                 CO;

	wire _TECHMAP_FAIL_ = Y_WIDTH <= 4;

	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	wire [Y_WIDTH-1:0] AA = A_buf;
	wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;
	//wire [Y_WIDTH:0] C = {CO, CI};
        wire [Y_WIDTH+1:0] COx;
        wire [Y_WIDTH+1:0] C = {COx, CI};

	/* Start implementation */
	(* keep *) fiftyfivenm_lcell_comb #(.lut_mask(16'b0000_0000_1010_1010), .sum_lutc_input("cin")) carry_start (.cout(COx[0]), .dataa(C[0]), .datab(1'b1), .datac(1'b1), .datad(1'b1));

	genvar i;
	generate for (i = 0; i < Y_WIDTH; i = i + 1) begin: slice
	  if(i==Y_WIDTH-1) begin
	    (* keep *) fiftyfivenm_lcell_comb #(.lut_mask(16'b1111_0000_1110_0000), .sum_lutc_input("cin")) carry_end (.combout(COx[Y_WIDTH]), .dataa(1'b1), .datab(1'b1), .datac(1'b1), .datad(1'b1), .cin(C[Y_WIDTH]));
            assign CO = COx[Y_WIDTH];
          end
	  else
	    fiftyfivenm_lcell_comb #(.lut_mask(16'b1001_0110_1110_1000), .sum_lutc_input("cin")) arith_cell (.combout(Y[i]), .cout(COx[i+1]), .dataa(AA[i]), .datab(BB[i]), .datac(1'b1), .datad(1'b1), .cin(C[i+1]));
	  end: slice
	endgenerate
	/* End implementation */
	assign X = AA ^ BB;

endmodule
