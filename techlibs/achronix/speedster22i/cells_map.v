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
// > c60k28 (Viacheslav, VT) [at] yandex [dot] com
// > Achronix eFPGA technology mapping. User must first simulate the generated \
// > netlist before going to test it on board/custom chip.

// > Input/Output buffers <
// Input buffer map
module \$__inpad (input I, output O);
    PADIN _TECHMAP_REPLACE_ (.padout(O), .padin(I));
endmodule
// Output buffer map
module \$__outpad (input I, output O);
    PADOUT _TECHMAP_REPLACE_ (.padout(O), .padin(I), .oe(1'b1));
endmodule
// > end buffers <

// > Look-Up table <
// > VT: I still think Achronix folks would have chosen a better \
// >     logic architecture.
// LUT Map
module \$lut (A, Y);
   parameter WIDTH  = 0;
   parameter LUT    = 0;
   input [WIDTH-1:0] A;
   output 	     Y;
   generate
      if (WIDTH == 1) begin
	   // VT: This is not consistent and ACE will complain: assign Y = ~A[0];
         LUT4 #(.lut_function({4{LUT}})) _TECHMAP_REPLACE_
           (.dout(Y), .din0(A[0]), .din1(1'b0), .din2(1'b0), .din3(1'b0));
      end else
      if (WIDTH == 2) begin
              LUT4 #(.lut_function({4{LUT}})) _TECHMAP_REPLACE_
                (.dout(Y), .din0(A[0]), .din1(A[1]), .din2(1'b0), .din3(1'b0));
      end else
      if(WIDTH == 3) begin
	      LUT4 #(.lut_function({2{LUT}})) _TECHMAP_REPLACE_
                (.dout(Y), .din0(A[0]), .din1(A[1]), .din2(A[2]), .din3(1'b0));
      end else
      if(WIDTH == 4) begin
             LUT4 #(.lut_function(LUT)) _TECHMAP_REPLACE_
               (.dout(Y), .din0(A[0]), .din1(A[1]), .din2(A[2]), .din3(A[3]));
      end else
	   wire _TECHMAP_FAIL_ = 1;
   endgenerate
endmodule
// > end LUT <

// > Flops <
// DFF flop
module  \$_DFF_P_ (input D, C, output Q);
   DFF _TECHMAP_REPLACE_
     (.q(Q), .d(D), .ck(C));
endmodule

