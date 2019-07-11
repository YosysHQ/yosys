/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung    <eddie@fpgeh.com>
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

module FDRE (output reg Q, input C, CE, D, R);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  wire \$nextQ ;
  \$__ABC_FDRE #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .R(R));
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(Q));
endmodule
module FDRE_1 (output reg Q, input C, CE, D, R);
  parameter [0:0] INIT = 1'b0;
  wire \$nextQ ;
  \$__ABC_FDRE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .R(R));
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(Q));
endmodule

module FDCE (output reg Q, input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  wire \$nextQ , \$currQ ;
  \$__ABC_FDCE #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .CLR(CLR));
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(Q));
  \$__ABC_MUX_ abc_async_mux (.A(\$currQ ), .B(1'b0), .S(CLR), .Y(Q));
endmodule
module FDCE_1 (output reg Q, input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  wire \$nextQ , \$currQ ;
  \$__ABC_FDCE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .CLR(CLR));
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(\$currQ ));
  \$__ABC_MUX_ abc_async_mux (.A(\$currQ ), .B(1'b0), .S(CLR), .Y(Q));
endmodule

module FDPE (output reg Q, input C, CE, D, PRE);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_PRE_INVERTED = 1'b0;
  wire \$nextQ , \$currQ ;
  \$__ABC_FDCE #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .PRE(PRE));
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(Q));
  generate
    if (IS_PRE_INVERTED)
      \$__ABC_MUX_ abc_async_mux (.A(\$currQ ), .B(1'b1), .S(PRE), .Y(Q));
    else
      \$__ABC_MUX_ abc_async_mux (.A(1'b1), .B(\$currQ ), .S(PRE), .Y(Q));
  endgenerate
endmodule
module FDPE_1 (output reg Q, input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  wire \$nextQ , \$currQ ;
  \$__ABC_FDCE_1 #(.INIT(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .PRE(PRE));
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(Q));
  \$__ABC_MUX_ abc_async_mux (.A(\$currQ ), .B(1'b1), .S(PRE), .Y(Q));
endmodule

`ifndef _ABC
module \$__ABC_FF_ (input C, D, output Q);
endmodule

(* abc_box_id = 1000 *)
module \$__ABC_FD_ASYNC_MUX_ (input A, B, S, output Q);
//  assign Q = S ? B : A;
endmodule

(* abc_box_id = 1001, lib_whitebox, abc_flop = "FDRE,D,Q,\\$pastQ" *)
module \$__ABC_FDRE (output Q, input C, CE, D, R, \$pastQ );
  parameter [0:0] INIT = 1'b0;
  //parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_R_INVERTED = 1'b0;
  assign Q = (R ^ IS_R_INVERTED) ? 1'b0 : (CE ? (D ^ IS_D_INVERTED) : \$pastQ );
endmodule

(* abc_box_id = 1002, lib_whitebox, abc_flop = "FDRE_1,D,Q,\\$pastQ" *)
module \$__ABC_FDRE_1 (output Q, input C, CE, D, R, \$pastQ );
  parameter [0:0] INIT = 1'b0;
  //parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_R_INVERTED = 1'b0;
  assign Q = (R ^ IS_R_INVERTED) ? 1'b0 : (CE ? (D ^ IS_D_INVERTED) : \$pastQ );
endmodule

(* abc_box_id = 1003, lib_whitebox, abc_flop = "FDCE,D,Q,\\$pastQ" *)
module \$__ABC_FDCE (output Q, input C, CE, D, CLR, \$pastQ );
  parameter [0:0] INIT = 1'b0;
  //parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  //parameter [0:0] IS_CLR_INVERTED = 1'b0;
  assign Q = CE ? (D ^ IS_D_INVERTED) : \$pastQ ;
endmodule

(* abc_box_id = 1004, lib_whitebox, abc_flop = "FDCE_1,D,Q,\\$pastQ" *)
module \$__ABC_FDCE_1 (output Q, input C, CE, D, CLR, \$pastQ );
  parameter [0:0] INIT = 1'b0;
  //parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  //parameter [0:0] IS_CLR_INVERTED = 1'b0;
  assign Q = CE ? (D ^ IS_D_INVERTED) : \$pastQ ;
endmodule

(* abc_box_id = 1005, lib_whitebox, abc_flop = "FDPE,D,Q,\\$pastQ" *)
module \$__ABC_FDPE (output Q, input C, CE, D, PRE, \$pastQ );
  parameter [0:0] INIT = 1'b0;
  //parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  //parameter [0:0] IS_PRE_INVERTED = 1'b0;
  assign Q = CE ? (D ^ IS_D_INVERTED) : \$pastQ ;
endmodule

(* abc_box_id = 1006, lib_whitebox, abc_flop = "FDPE_1,D,Q,\\$pastQ" *)
module \$__ABC_FDPE_1 (output Q, input C, CE, D, PRE, \$pastQ );
  parameter [0:0] INIT = 1'b0;
  //parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  //parameter [0:0] IS_PRE_INVERTED = 1'b0;
  assign Q = CE ? (D ^ IS_D_INVERTED) : \$pastQ ;
endmodule

`endif
