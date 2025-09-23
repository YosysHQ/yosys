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
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDCE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFFE_PP0P_ (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$_DFFE_NP1P_ (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDPE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .PRE(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFFE_PP1P_ (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .PRE(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Async set and reset, enable.

module  \$_DFFSRE_NPPP_ (input D, C, E, S, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDCPE #(.INIT(_TECHMAP_WIREINIT_Q_), .IS_C_INVERTED(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR(R), .PRE(S));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFFSRE_PPPP_ (input D, C, E, S, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDCPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR(R), .PRE(S));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Sync reset, enable.

module  \$_SDFFE_NP0P_ (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_SDFFE_PP0P_ (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$_SDFFE_NP1P_ (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .S(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_SDFFE_PP1P_ (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .S(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Latches with reset.

module  \$_DLATCH_NP0_ (input E, R, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  LDCE #(.INIT(_TECHMAP_WIREINIT_Q_), .IS_G_INVERTED(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .CLR(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DLATCH_PP0_ (input E, R, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  LDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .CLR(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DLATCH_NP1_ (input E, R, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  LDPE #(.INIT(_TECHMAP_WIREINIT_Q_), .IS_G_INVERTED(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .PRE(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DLATCH_PP1_ (input E, R, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  LDPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .PRE(R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Latches with set and reset.

module  \$_DLATCH_NPP_ (input E, S, R, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  LDCPE #(.INIT(_TECHMAP_WIREINIT_Q_), .IS_G_INVERTED(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .CLR(R), .PRE(S));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DLATCH_PPP_ (input E, S, R, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  LDCPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .CLR(R), .PRE(S));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

`endif

