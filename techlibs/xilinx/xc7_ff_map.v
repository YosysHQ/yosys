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

// ============================================================================
// FF mapping for Virtex 6, Series 7 and Ultrascale.  These families support
// the following features:
//
// - a CLB flip-flop can be used as a latch or as a flip-flop
// - a CLB flip-flop has the following pins:
//
//   - data input
//   - clock (or gate for latches) (with optional inversion)
//   - clock enable (or gate enable, which is just ANDed with gate — unused by
//     synthesis)
//   - either a set or a reset input, which (for FFs) can be either
//     synchronous or asynchronous (with optional inversion)
//   - data output
//
// - a flip-flop also has an initial value, which is set at device
//   initialization (or whenever GSR is asserted)

`ifndef _NO_FFS

// No reset.

module  \$_DFF_N_   (input D, C, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFF_P_   (input D, C, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// No reset, enable.

module  \$_DFFE_NP_ (input D, C, E, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .R(1'b0));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .R(1'b0));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Async reset.

module  \$_DFF_NP0_ (input D, C, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDCE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$_DFF_NP1_ (input D, C, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDPE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Async reset, enable.

module  \$__DFFE_NP0 (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDCE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFE_PP0 (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$__DFFE_NP1 (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDPE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .PRE( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFE_PP1 (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .PRE( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Sync reset.

module  \$__DFFS_NP0_ (input D, C, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFS_PP0_ (input D, C, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$__DFFS_NP1_ (input D, C, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .S( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFS_PP1_ (input D, C, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .S( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Sync reset, enable.

module  \$__DFFSE_NP0 (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFSE_PP0 (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$__DFFSE_NP1 (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .S( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFSE_PP1 (input D, C, E, R, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .S( R));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Latches (no reset).

module  \$_DLATCH_N_ (input E, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  LDCE #(.INIT(_TECHMAP_WIREINIT_Q_), .IS_G_INVERTED(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .CLR(1'b0));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DLATCH_P_ (input E, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  LDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .CLR(1'b0));
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Latches with reset (TODO).

`endif

