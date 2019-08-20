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

// Max delays from https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L237-L251

module FDRE (output reg Q, input C, CE, D, R);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_R_INVERTED = 1'b0;
  wire \$nextQ ;
  \$__ABC_FDRE #(
    .INIT(INIT),
    .IS_C_INVERTED(IS_C_INVERTED),
    .IS_D_INVERTED(IS_D_INVERTED),
    .IS_R_INVERTED(IS_R_INVERTED),
    .CLK_POLARITY(!IS_C_INVERTED),
    .EN_POLARITY(1'b1)
  ) _TECHMAP_REPLACE_ (
    .D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .R(R)
  );
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(Q));
endmodule
module FDRE_1 (output reg Q, input C, CE, D, R);
  parameter [0:0] INIT = 1'b0;
  wire \$nextQ ;
  \$__ABC_FDRE_1 #(
      .INIT(|0),
    .CLK_POLARITY(1'b0),
    .EN_POLARITY(1'b1)
  ) _TECHMAP_REPLACE_ (
    .D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .R(R)
  );
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(Q));
endmodule

module FDCE (output reg Q, input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  wire \$nextQ , \$currQ ;
  \$__ABC_FDCE #(
    .INIT(INIT),
    .IS_C_INVERTED(IS_C_INVERTED),
    .IS_D_INVERTED(IS_D_INVERTED),
    .IS_CLR_INVERTED(IS_CLR_INVERTED),
    .CLK_POLARITY(!IS_C_INVERTED),
    .EN_POLARITY(1'b1)
  ) _TECHMAP_REPLACE_ (
    .D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .CLR(CLR)
  );
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(\$currQ ));
  \$__ABC_ASYNC abc_async (.A(\$currQ ), .S(CLR), .Y(Q));
endmodule
module FDCE_1 (output reg Q, input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  wire \$nextQ , \$currQ ;
  \$__ABC_FDCE_1 #(
    .INIT(INIT),
    .CLK_POLARITY(1'b0),
    .EN_POLARITY(1'b1)
  ) _TECHMAP_REPLACE_ (
    .D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .CLR(CLR)
  );
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(\$currQ ));
  \$__ABC_ASYNC abc_async (.A(\$currQ ), .S(CLR), .Y(Q));
endmodule

module FDPE (output reg Q, input C, CE, D, PRE);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_PRE_INVERTED = 1'b0;
  wire \$nextQ , \$currQ ;
  \$__ABC_FDPE #(
    .INIT(INIT),
    .IS_C_INVERTED(IS_C_INVERTED),
    .IS_D_INVERTED(IS_D_INVERTED),
    .IS_PRE_INVERTED(IS_PRE_INVERTED),
    .CLK_POLARITY(!IS_C_INVERTED),
    .EN_POLARITY(1'b1)
  ) _TECHMAP_REPLACE_ (
    .D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .PRE(PRE)
  );
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(\$currQ ));
  \$__ABC_ASYNC abc_async (.A(\$currQ ), .S(PRE), .Y(Q));
endmodule
module FDPE_1 (output reg Q, input C, CE, D, PRE);
  parameter [0:0] INIT = 1'b0;
  wire \$nextQ , \$currQ ;
  \$__ABC_FDPE_1 #(
    .INIT(INIT),
    .CLK_POLARITY(1'b0),
    .EN_POLARITY(1'b1)
  ) _TECHMAP_REPLACE_ (
    .D(D), .Q(\$nextQ ), .\$pastQ (Q), .C(C), .CE(CE), .PRE(PRE)
  );
  \$__ABC_FF_ abc_dff (.D(\$nextQ ), .Q(\$currQ ));
  \$__ABC_ASYNC abc_async (.A(\$currQ ), .S(PRE), .Y(Q));
endmodule
