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
module  \$_DFF_N_ (input D, C, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .clrn(1'b1), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFF_P_ (input D, C, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .clrn(1'b1), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module \$_DFFE_NN_ (input D, C, E, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .clrn(1'b1), .prn(1'b1), .ena(~E), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFFE_NP_ (input D, C, E, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .clrn(1'b1), .prn(1'b1), .ena(E), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFFE_PN_ (input D, C, E, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .clrn(1'b1), .prn(1'b1), .ena(~E), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .clrn(1'b1), .prn(1'b1), .ena(E), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFF_NN0_ (input D, C, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .clrn(R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFF_NN1_ (input D, C, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   wire Q_n;
   fiftyfivenm_lcell_comb QH0 (.combout(Q), .dataa(Q_n), .datab(1'b1), .datac(1'b1), .datad(1'b1));
   defparam QH0.lut_mask = 16'b0101010101010101;
   defparam QH0.sum_lutc_input = "datac";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(~D), .q(Q_n), .clk(~C), .clrn(R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .clrn(R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module \$_DFF_PN1_ (input D, C, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   wire Q_n;
   fiftyfivenm_lcell_comb QH0 (.combout(Q), .dataa(Q_n), .datab(1'b1), .datac(1'b1), .datad(1'b1));
   defparam QH0.lut_mask = 16'b0101010101010101;
   defparam QH0.sum_lutc_input = "datac";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(~D), .q(Q_n), .clk(C), .clrn(R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFF_NP0_ (input D, C, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(~C), .clrn(~R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   wire Q_n;
   fiftyfivenm_lcell_comb QH0 (.combout(Q), .dataa(Q_n), .datab(1'b1), .datac(1'b1), .datad(1'b1));
   defparam QH0.lut_mask = 16'b0101010101010101;
   defparam QH0.sum_lutc_input = "datac";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(~D), .q(Q_n), .clk(~C), .clrn(~R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .clrn(~R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   wire Q_n;
   fiftyfivenm_lcell_comb QH0 (.combout(Q), .dataa(Q_n), .datab(1'b1), .datac(1'b1), .datad(1'b1));
   defparam QH0.lut_mask = 16'b0101010101010101;
   defparam QH0.sum_lutc_input = "datac";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(~D), .q(Q_n), .clk(C), .clrn(~R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(1'b0), .sload(1'b0));
endmodule
module  \$__DFFE_PP0 (input D, C, E, R, output Q);
   parameter _TECHMAP_WIREINIT_Q_ = 1'b0;
   wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
   parameter WYSIWYG="TRUE";
   dffeas #(.is_wysiwyg(WYSIWYG), .power_up(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.d(D), .q(Q), .clk(C), .clrn(R), .prn(1'b1), .ena(1'b1), .asdata(1'b0), .aload(1'b0), .sclr(~E), .sload(1'b0));
endmodule

// Input buffer map
module \$__inpad (input I, output O);
    twentynm_io_ibuf _TECHMAP_REPLACE_ (.o(O), .i(I), .ibar(1'b0));
endmodule

// Output buffer map
module \$__outpad (input I, output O);
    twentynm_io_obuf _TECHMAP_REPLACE_ (.o(O), .i(I), .oe(1'b1));
endmodule

// LUT Map
module \$lut (A, Y);
   parameter WIDTH  = 0;
   parameter LUT    = 0;
   input [WIDTH-1:0] A;
   output            Y;
   generate
      if (WIDTH == 1) begin
	   twentynm_lcell_comb #(.lut_mask({32{LUT}}), .shared_arith("off"), .extended_lut("off"))
           _TECHMAP_REPLACE_ (.combout(Y), .dataa(A[0]), .datab(1'b1), .datac(1'b1), .datad(1'b1), .datae(1'b1), .dataf(1'b1), .datag(1'b1));
      end else
      if (WIDTH == 2) begin
           twentynm_lcell_comb #(.lut_mask({16{LUT}}), .shared_arith("off"), .extended_lut("off"))
           _TECHMAP_REPLACE_ (.combout(Y), .dataa(A[0]), .datab(A[1]), .datac(1'b1),.datad(1'b1), .datae(1'b1), .dataf(1'b1), .datag(1'b1));
      end /*else
      if(WIDTH == 3) begin
	   fiftyfivenm_lcell_comb #(.lut_mask({2{LUT}}), .sum_lutc_input("datac")) _TECHMAP_REPLACE_ (.combout(Y), .dataa(A[0]), .datab(A[1]), .datac(A[2]),.datad(1'b1));
      end else
      if(WIDTH == 4) begin
	   fiftyfivenm_lcell_comb #(.lut_mask(LUT), .sum_lutc_input("datac")) _TECHMAP_REPLACE_ (.combout(Y), .dataa(A[0]), .datab(A[1]), .datac(A[2]),.datad(A[3]));
      end*/ else
	   wire _TECHMAP_FAIL_ = 1;
   endgenerate
endmodule //


