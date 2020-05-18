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
/* Uncomment this for LCU????
module _80_cycloneiv_alu (A, B, CI, BI, X, Y, CO);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	//output [Y_WIDTH-1:0] CO;
        output                 CO;

	wire _TECHMAP_FAIL_ = Y_WIDTH <= 2;

	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	wire [Y_WIDTH-1:0] AA = A_buf;
	wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;
	//wire [Y_WIDTH:0] C = {CO, CI};
        wire [Y_WIDTH+1:0] COx;
        wire [Y_WIDTH+1:0] C = {COx, CI};

	/* Start implementation */
	//cycloneiv_lcell_comb #(.lut_mask(16'b0000_0000_1010_1010), .sum_lutc_input("cin")) carry_start (.cout(COx[0]), .dataa(C[0]), .datab(1'b1), .datac(1'b1), .datad(1'b1));
	/*
	genvar i;
	generate for (i = 0; i < Y_WIDTH; i = i + 1) begin: slice
	  if(i==Y_WIDTH-1)
	    (* keep *) cycloneiv_lcell_comb #(.lut_mask(16'b1111_0000_1110_0000), .sum_lutc_input("cin")) carry_end (.combout(CO), .dataa(1'b1), .datab(1'b1), .datac(1'b1), .datad(1'b1), .cin(C[Y_WIDTH]));
            //assign CO = COx[Y_WIDTH];
	  else
	    cycloneiv_lcell_comb #(.lut_mask(16'b1001_0110_1110_1000), .sum_lutc_input("cin")) arith_cell (.combout(Y[i]), .cout(COx[i+1]), .dataa(AA[i]), .datab(BB[i]), .datac(1'b1), .datad(1'b1), .cin(C[i+1]));
	  end: slice
	endgenerate
	/* End implementation */
	/*assign X = AA ^ BB;

endmodule*/
module _80_cycloneiv_alu (A, B, CI, BI, X, Y, CO);
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
	output [Y_WIDTH:0] CO;

	wire _TECHMAP_FAIL_ = Y_WIDTH < 6;

	(* force_downto *)
	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	(* force_downto *)
	wire [Y_WIDTH-1:0] AA = A_buf;
	(* force_downto *)
	wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;
	wire [Y_WIDTH:0] C = {CO, CI};

        cycloneiv_lcell_comb #(.lut_mask(16'b0110_0110_1000_1000), .sum_lutc_input("cin")) carry_start  (.cout(CO[0]), .dataa(BB[0]), .datab(1'b1), .datac(1'b1), .datad(1'b1));
	genvar i;
	generate for (i = 1; i < Y_WIDTH; i = i + 1) begin:slice
	    cycloneiv_lcell_comb #(.lut_mask(16'b0101_1010_0101_0000), .sum_lutc_input("cin")) arith_cell (.combout(Y[i]), .cout(CO[i]), .dataa(BB[i]), .datab(1'b1), .datac(1'b1), .datad(1'b1), .cin(C[i]));
	end endgenerate

	assign X = AA ^ BB;
endmodule
