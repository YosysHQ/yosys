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
// FF mapping

`ifndef _NO_FFS

module  \$_DFF_N_   (input D, C, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .S(1'b0));
  else
    FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0));
  endgenerate
endmodule
module  \$_DFF_P_   (input D, C, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .S(1'b0));
  else
    FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0));
  endgenerate
endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    FDSE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .S(1'b0));
  else
    FDRE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .R(1'b0));
  endgenerate
endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    FDSE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .S(1'b0));
  else
    FDRE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .R(1'b0));
  endgenerate
endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with asynchronous reset initialized to 1");
  else
    FDCE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR(!R));
  endgenerate
endmodule
module  \$_DFF_NP0_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with asynchronous reset initialized to 1");
  else
    FDCE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR( R));
  endgenerate
endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with asynchronous reset initialized to 1");
  else
    FDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR(!R));
  endgenerate
endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b1)
    $error("Spartan 6 doesn't support FFs with asynchronous reset initialized to 1");
  else
    FDCE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR( R));
  endgenerate
endmodule

module  \$_DFF_NN1_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with asynchronous set initialized to 0");
  else
    FDPE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE(!R));
  endgenerate
endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with asynchronous set initialized to 0");
  else
    FDPE_1 #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE( R));
  endgenerate
endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with asynchronous set initialized to 0");
  else
    FDPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE(!R));
  endgenerate
endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q);
  parameter [0:0] _TECHMAP_WIREINIT_Q_ = 1'bx;
  generate if (_TECHMAP_WIREINIT_Q_ === 1'b0)
    $error("Spartan 6 doesn't support FFs with asynchronous set initialized to 0");
  else
    FDPE   #(.INIT(_TECHMAP_WIREINIT_Q_)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE( R));
  endgenerate
endmodule

`endif

