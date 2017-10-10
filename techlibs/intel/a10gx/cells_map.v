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
	   assign Y = ~A[0]; // Not need to spend 1 logic cell for such an easy function
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


