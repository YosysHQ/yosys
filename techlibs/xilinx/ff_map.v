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

module  \$_DFF_N_   (input D, C, output Q);    FDRE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0)); endmodule
module  \$_DFF_P_   (input D, C, output Q);    FDRE   #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0)); endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q); FDRE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .R(1'b0)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); FDRE   #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E),    .R(1'b0)); endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q); FDCE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR(!R)); endmodule
module  \$_DFF_NP0_ (input D, C, R, output Q); FDCE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR( R)); endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q); FDCE   #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR(!R)); endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); FDCE   #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR( R)); endmodule

module  \$_DFF_NN1_ (input D, C, R, output Q); FDPE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE(!R)); endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); FDPE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE( R)); endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q); FDPE   #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE(!R)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); FDPE   #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE( R)); endmodule

`endif

