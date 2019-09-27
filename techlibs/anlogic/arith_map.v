/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018  Miodrag Milanovic <miodrag@symbioticeda.com>
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

(* techmap_celltype = "$alu" *)
module _80_anlogic_alu (A, B, CI, BI, X, Y, CO);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH  = 1;
	parameter B_WIDTH  = 1;
	parameter Y_WIDTH  = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	output [Y_WIDTH-1:0] CO;
   
	wire CIx;
	wire [Y_WIDTH-1:0] COx;

	wire _TECHMAP_FAIL_ = Y_WIDTH <= 2;

	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	wire [Y_WIDTH-1:0] AA = A_buf;
	wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;
	wire [Y_WIDTH-1:0] C = { COx, CIx };

    wire dummy;
    AL_MAP_ADDER #(
    	.ALUTYPE("ADD_CARRY"))
    adder_cin  (
        .a(CI),
		.b(1'b0),
		.c(1'b0),
        .o({CIx, dummy})
	);

	genvar i;
	generate for (i = 0; i < Y_WIDTH; i = i + 1) begin: slice
	    AL_MAP_ADDER #(
            .ALUTYPE("ADD")
        ) adder_i (
            .a(AA[i]),
            .b(BB[i]),
            .c(C[i]),
            .o({COx[i],Y[i]})
        );

		wire cout;
		AL_MAP_ADDER #(
			.ALUTYPE("ADD"))
		adder_cout  (
			.a(1'b0),
			.b(1'b0),
			.c(COx[i]),
			.o({cout, CO[i]})
		);
	  end: slice	  
	endgenerate

   /* End implementation */
   assign X = AA ^ BB;
endmodule
