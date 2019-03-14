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
/* TODO: Describe the following mode */
module fa
  (input  a_c,
   input  b_c,
   input  cin_c,
   output cout_t,
   output sum_x);

   wire   a_c;
   wire   b_c;
   wire   cout_t;
   wire   cin_c;
   wire   sum_x;
   wire   VCC;

   assign VCC = 1'b1;

   cycloneiv_lcell_comb gen_sum_0 (.combout(sum_x),
                                   .dataa(a_c),
                                   .datab(b_c),
                                   .datac(cin_c),
                                   .datad(VCC));
   defparam syn__05_.lut_mask = 16'b1001011010010110;
   defparam syn__05_.sum_lutc_input = "datac";

   cycloneiv_lcell_comb gen_cout_0 (.combout(cout_t),
                                    .dataa(cin_c),
                                    .datab(b_c),
                                    .datac(a_c),
                                    .datad(VCC));
   defparam syn__06_.lut_mask = 16'b1110000011100000;
   defparam syn__06_.sum_lutc_input = "datac";

endmodule // fa

module f_stage();

endmodule // f_stage

module f_end();

endmodule // f_end

module _80_cycloneive_alu (A, B, CI, BI, X, Y, CO);
   parameter A_SIGNED = 0;
   parameter B_SIGNED = 0;
   parameter A_WIDTH = 1;
   parameter B_WIDTH = 1;
   parameter Y_WIDTH = 1;

   input [A_WIDTH-1:0] A;
   input [B_WIDTH-1:0] B;
   output [Y_WIDTH-1:0] X, Y;

   input                CI, BI;
   output [Y_WIDTH:0]   CO;

   wire                 _TECHMAP_FAIL_ = Y_WIDTH < 5;

   wire [Y_WIDTH-1:0]   A_buf, B_buf;
   \$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
   \$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

   wire [Y_WIDTH-1:0]   AA = A_buf;
   wire [Y_WIDTH-1:0]   BB = BI ? ~B_buf : B_buf;
   wire [Y_WIDTH:0]     C = {CO, CI};

   fa f0 (.a_c(AA[0]),
          .b_c(BB[0]),
          .cin_c(C[0]),
          .cout_t(C0[1]),
          .sum_x(Y[0]));

   genvar i;
   generate for (i = 1; i < Y_WIDTH; i = i + 1) begin:slice
      cycloneive_lcell_comb #(.lut_mask(16'b0101_1010_0101_0000), .sum_lutc_input("cin")) arith_cell (.combout(Y[i]), .cout(CO[i]), .dataa(BB[i]), .datab(1'b1), .datac(1'b1), .datad(1'b1), .cin(C[i]));
   end endgenerate

   assign X = AA ^ BB;

endmodule
