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
// FF mapping for Spartan 6.  The primitives used are the same as Series 7,
// but with one major difference: the initial value is implied by the
// primitive type used (FFs with reset pin must have INIT set to 0 or x, FFs
// with set pin must have INIT set to 1 or x).  For Yosys primitives without
// set/reset, this means we have to pick the primitive type based on the INIT
// value.

`ifndef _NO_FFS

// No reset.

module  \$_DFF_N_   (input D, C, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .S(1'b0));
  else
    FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFF_P_   (input D, C, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .S(1'b0));
  else
    FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// No reset, enable.

module  \$_DFFE_NP_ (input D, C, E, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .S(1'b0));
  else
    FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .R(1'b0));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .S(1'b0));
  else
    FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .R(1'b0));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Async reset.

module  \$_DFF_NP0_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with asynchronous reset initialized to 1");
  else
    FDCE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with asynchronous reset initialized to 1");
  else
    FDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$_DFF_NP1_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with asynchronous set initialized to 0");
  else
    FDPE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with asynchronous set initialized to 0");
  else
    FDPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Async reset, enable.

module  \$__DFFE_NP0 (input D, C, E, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with asynchronous reset initialized to 1");
  else
    FDCE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFE_PP0 (input D, C, E, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with asynchronous reset initialized to 1");
  else
    FDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .CLR( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$__DFFE_NP1 (input D, C, E, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with asynchronous set initialized to 0");
  else
    FDPE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .PRE( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFE_PP1 (input D, C, E, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with asynchronous set initialized to 0");
  else
    FDPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .PRE( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Sync reset.

module  \$__DFFS_NP0_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with reset initialized to 1");
  else
    FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFS_PP0_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with reset initialized to 1");
  else
    FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$__DFFS_NP1_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with set initialized to 0");
  else
    FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .S( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFS_PP1_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with set initialized to 0");
  else
    FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .S( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Sync reset, enable.

module  \$__DFFSE_NP0 (input D, C, E, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with reset initialized to 1");
  else
    FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFSE_PP0 (input D, C, E, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with reset initialized to 1");
  else
    FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

module  \$__DFFSE_NP1 (input D, C, E, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with set initialized to 0");
  else
    FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .S( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$__DFFSE_PP1 (input D, C, E, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with set initialized to 0");
  else
    FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .S( R));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Latches (no reset).

module  \$_DLATCH_N_ (input E, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    LDPE #(.INIT(_TECHMAP_WIREINIT_Q_), .IS_G_INVERTED(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .PRE(1'b0));
  else
    LDCE #(.INIT(_TECHMAP_WIREINIT_Q_), .IS_G_INVERTED(1'b1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .CLR(1'b0));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
module  \$_DLATCH_P_ (input E, D, output Q);
  parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    LDPE #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .PRE(1'b0));
  else
    LDCE #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .G(E), .GE(1'b1), .CLR(1'b0));
  endgenerate
  wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// Latches with reset (TODO).

`endif

