/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

`ifndef _NO_FFS

// Async reset, enable.

module  \$_DFFE_NP0P_ (input D, C, E, R, output Q);
  FFCE_N #(.INIT(1'b0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFFE_PP0P_ (input D, C, E, R, output Q);
  FFCE   #(.INIT(1'b0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$_DFFE_NP1P_ (input D, C, E, R, output Q);
  FFPE_N #(.INIT(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .PRE(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFFE_PP1P_ (input D, C, E, R, output Q);
  FFPE   #(.INIT(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .PRE(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Sync reset, enable.

module  \$_SDFFE_NP0P_ (input D, C, E, R, output Q);
  FFRE_N #(.INIT(1'b0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_SDFFE_PP0P_ (input D, C, E, R, output Q);
  FFRE   #(.INIT(1'b0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$_SDFFE_NP1P_ (input D, C, E, R, output Q);
  FFSE_N #(.INIT(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .S(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_SDFFE_PP1P_ (input D, C, E, R, output Q);
  FFSE   #(.INIT(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .S(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

`endif

