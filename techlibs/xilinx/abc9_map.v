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

// The following techmapping rules are intended to be run (with -max_iter 1)
//   before invoking the `abc9` pass in order to transform the design into
//   a format that it understands.

`ifdef DFF_MODE
// For example, (complex) flip-flops are expected to be described as an
//   combinatorial box (containing all control logic such as clock enable
//   or synchronous resets) followed by a basic D-Q flop.
// Yosys will automatically analyse the simulation model (described in
//   cells_sim.v) and detach any $_DFF_P_ or $_DFF_N_ cells present in
//   order to extract the combinatorial control logic left behind.
//   Specifically, a simulation model similar to the one below:
//
//                ++===================================++
//                ||                        Sim model  ||
//                ||      /\/\/\/\                     ||
//            D -->>-----<        >     +------+       ||
//            R -->>-----<  Comb. >     |$_DFF_|       ||
//           CE -->>-----<  logic >-----| [NP]_|---+---->>-- Q
//                ||  +--<        >     +------+   |   ||
//                ||  |   \/\/\/\/                 |   ||
//                ||  |                            |   ||
//                ||  +----------------------------+   ||
//                ||                                   ||
//                ++===================================++
//
//   is transformed into:
//
//                ++==================++
//                ||         Comb box ||
//                ||                  ||
//                ||      /\/\/\/\    ||
//           D  -->>-----<        >   ||
//           R  -->>-----<  Comb. >   ||        +-----------+
//          CE  -->>-----<  logic >--->>-- $Q --|$__ABC9_FF_|--+-->> Q
//   abc9_ff.Q +-->>-----<        >   ||        +-----------+  |
//             |  ||      \/\/\/\/    ||                       |
//             |  ||                  ||                       |
//             |  ++==================++                       |
//             |                                               |
//             +-----------------------------------------------+
//
// The purpose of the following FD* rules are to wrap the flop with:
// (a) a special $__ABC9_FF_ in front of the FD*'s output, indicating to abc9
//     the connectivity of its basic D-Q flop
// (b) an optional $__ABC9_ASYNC_ cell in front of $__ABC_FF_'s output to
//     capture asynchronous behaviour
// (c) a special abc9_ff.clock wire to capture its clock domain and polarity
//     (indicated to `abc9' so that it only performs sequential synthesis
//     (with reachability analysis) correctly on one domain at a time)
// (d) an (* abc9_init *) attribute on the $__ABC9_FF_ cell capturing its
//     initial state
//     NOTE: in order to perform sequential synthesis, `abc9' requires that
//     the initial value of all flops be zero
// (e) a special _TECHMAP_REPLACE_.abc9_ff.Q wire that will be used for feedback
//     into the (combinatorial) FD* cell to facilitate clock-enable behaviour

module FDRE (output Q, (* techmap_autopurge *) input C, CE, D, R);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_R_INVERTED = 1'b0;
  wire QQ, $Q;
  generate if (INIT == 1'b1) begin
    assign Q = ~QQ;
    FDSE #(
      .INIT(1'b0),
      .IS_C_INVERTED(IS_C_INVERTED),
      .IS_D_INVERTED(IS_D_INVERTED),
      .IS_S_INVERTED(IS_R_INVERTED)
    ) _TECHMAP_REPLACE_ (
      .D(~D), .Q($Q), .C(C), .CE(CE), .S(R)
    );
  end
  else begin
    assign Q = QQ;
    FDRE #(
      .INIT(1'b0),
      .IS_C_INVERTED(IS_C_INVERTED),
      .IS_D_INVERTED(IS_D_INVERTED),
      .IS_R_INVERTED(IS_R_INVERTED)
    ) _TECHMAP_REPLACE_ (
      .D(D), .Q($Q), .C(C), .CE(CE), .R(R)
    );
  end
  endgenerate
  (* abc9_init = 1'b0 *)
  $__ABC9_FF_ abc9_ff (.D($Q), .Q(QQ));

  // Special signals
  wire [1:0] abc9_ff.clock = {C, IS_C_INVERTED};
  wire [0:0] _TECHMAP_REPLACE_.abc9_ff.Q = QQ;
endmodule
module FDRE_1 (output Q, (* techmap_autopurge *) input C, CE, D, R);
  parameter [0:0] INIT = 1'b0;
  wire QQ, $Q;
  generate if (INIT == 1'b1) begin
    assign Q = ~QQ;
    FDSE_1 #(
      .INIT(1'b0)
    ) _TECHMAP_REPLACE_ (
      .D(~D), .Q($Q), .C(C), .CE(CE), .S(R)
    );
  end
  else begin
    assign Q = QQ;
    FDRE_1 #(
      .INIT(1'b0)
    ) _TECHMAP_REPLACE_ (
      .D(D), .Q($Q), .C(C), .CE(CE), .R(R)
    );
  end
  endgenerate
  (* abc9_init = 1'b0 *)
  $__ABC9_FF_ abc9_ff (.D($Q), .Q(QQ));

  // Special signals
  wire [1:0] abc9_ff.clock = {C, 1'b1 /* IS_C_INVERTED */};
  wire [0:0] _TECHMAP_REPLACE_.abc9_ff.Q = QQ;
endmodule

module FDSE (output Q, (* techmap_autopurge *) input C, CE, D, S);
  parameter [0:0] INIT = 1'b1;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_S_INVERTED = 1'b0;
  wire QQ, $Q;
  generate if (INIT == 1'b1) begin
    assign Q = ~QQ;
    FDRE #(
      .INIT(1'b0),
      .IS_C_INVERTED(IS_C_INVERTED),
      .IS_D_INVERTED(IS_D_INVERTED),
      .IS_R_INVERTED(IS_S_INVERTED)
    ) _TECHMAP_REPLACE_ (
      .D(~D), .Q($Q), .C(C), .CE(CE), .R(S)
    );
  end
  else begin
    assign Q = QQ;
    FDSE #(
      .INIT(1'b0),
      .IS_C_INVERTED(IS_C_INVERTED),
      .IS_D_INVERTED(IS_D_INVERTED),
      .IS_S_INVERTED(IS_S_INVERTED)
    ) _TECHMAP_REPLACE_ (
      .D(D), .Q($Q), .C(C), .CE(CE), .S(S)
    );
  end endgenerate
  (* abc9_init = 1'b0 *)
  $__ABC9_FF_ abc9_ff (.D($Q), .Q(QQ));

  // Special signals
  wire [1:0] abc9_ff.clock = {C, IS_C_INVERTED};
  wire [0:0] _TECHMAP_REPLACE_.abc9_ff.Q = QQ;
endmodule
module FDSE_1 (output Q, (* techmap_autopurge *) input C, CE, D, S);
  parameter [0:0] INIT = 1'b1;
  wire QQ, $Q;
  generate if (INIT == 1'b1) begin
    assign Q = ~QQ;
    FDRE_1 #(
      .INIT(1'b0)
    ) _TECHMAP_REPLACE_ (
      .D(~D), .Q($Q), .C(C), .CE(CE), .R(S)
    );
  end
  else begin
    assign Q = QQ;
    FDSE_1 #(
      .INIT(1'b0)
    ) _TECHMAP_REPLACE_ (
      .D(D), .Q($Q), .C(C), .CE(CE), .S(S)
    );
  end endgenerate
  (* abc9_init = 1'b0 *)
  $__ABC9_FF_ abc9_ff (.D($Q), .Q(QQ));

  // Special signals
  wire [1:0] abc9_ff.clock = {C, 1'b1 /* IS_C_INVERTED */};
  wire [0:0] _TECHMAP_REPLACE_.abc9_ff.Q = QQ;
endmodule

module FDCE (output Q, (* techmap_autopurge *) input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  wire QQ, $Q, $QQ;
  generate if (INIT == 1'b1) begin
    assign Q = ~QQ;
    FDPE #(
      .INIT(1'b0),
      .IS_C_INVERTED(IS_C_INVERTED),
      .IS_D_INVERTED(IS_D_INVERTED),
      .IS_PRE_INVERTED(IS_CLR_INVERTED)
    ) _TECHMAP_REPLACE_ (
      .D(~D), .Q($Q), .C(C), .CE(CE), .PRE(CLR)
                                        // ^^^ Note that async
                                        //     control is not directly
                                        //     supported by abc9 but its
                                        //     behaviour is captured by
                                        //     $__ABC9_ASYNC1 below
    );
    // Since this is an async flop, async behaviour is dealt with here
    $__ABC9_ASYNC1 abc_async (.A($QQ), .S(CLR ^ IS_CLR_INVERTED), .Y(QQ));
  end
  else begin
    assign Q = QQ;
    FDCE #(
      .INIT(1'b0),
      .IS_C_INVERTED(IS_C_INVERTED),
      .IS_D_INVERTED(IS_D_INVERTED),
      .IS_CLR_INVERTED(IS_CLR_INVERTED)
    ) _TECHMAP_REPLACE_ (
      .D(D), .Q($Q), .C(C), .CE(CE), .CLR(CLR)
                                       // ^^^ Note that async
                                       //     control is not directly
                                       //     supported by abc9 but its
                                       //     behaviour is captured by
                                       //     $__ABC9_ASYNC0 below
    );
    // Since this is an async flop, async behaviour is dealt with here
    $__ABC9_ASYNC0 abc_async (.A($QQ), .S(CLR ^ IS_CLR_INVERTED), .Y(QQ));
  end endgenerate
  (* abc9_init = 1'b0 *)
  $__ABC9_FF_ abc9_ff (.D($Q), .Q($QQ));

  // Special signals
  wire [1:0] abc9_ff.clock = {C, IS_C_INVERTED};
  wire [0:0] _TECHMAP_REPLACE_.abc9_ff.Q = $QQ;
endmodule
module FDCE_1 (output Q, (* techmap_autopurge *) input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  wire QQ, $Q, $QQ;
  generate if (INIT == 1'b1) begin
    assign Q = ~QQ;
    FDPE_1 #(
      .INIT(1'b0)
    ) _TECHMAP_REPLACE_ (
      .D(~D), .Q($Q), .C(C), .CE(CE), .PRE(CLR)
                                        // ^^^ Note that async
                                        //     control is not directly
                                        //     supported by abc9 but its
                                        //     behaviour is captured by
                                        //     $__ABC9_ASYNC1 below
    );
    $__ABC9_ASYNC1 abc_async (.A($QQ), .S(CLR), .Y(QQ));
  end
  else begin
    assign Q = QQ;
    FDCE_1 #(
      .INIT(1'b0)
    ) _TECHMAP_REPLACE_ (
      .D(D), .Q($Q), .C(C), .CE(CE), .CLR(CLR)
                                       // ^^^ Note that async
                                       //     control is not directly
                                       //     supported by abc9 but its
                                       //     behaviour is captured by
                                       //     $__ABC9_ASYNC0 below
    );
    $__ABC9_ASYNC0 abc_async (.A($QQ), .S(CLR), .Y(QQ));
  end endgenerate
  (* abc9_init = 1'b0 *)
  $__ABC9_FF_ abc9_ff (.D($Q), .Q($QQ));

  // Special signals
  wire [1:0] abc9_ff.clock = {C, 1'b1 /* IS_C_INVERTED */};
  wire [0:0] _TECHMAP_REPLACE_.abc9_ff.Q = $QQ;
endmodule

module FDPE (output Q, (* techmap_autopurge *) input C, CE, D, PRE);
  parameter [0:0] INIT = 1'b1;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_PRE_INVERTED = 1'b0;
  wire QQ, $Q, $QQ;
  generate if (INIT == 1'b1) begin
    assign Q = ~QQ;
    FDCE #(
      .INIT(1'b0),
      .IS_C_INVERTED(IS_C_INVERTED),
      .IS_D_INVERTED(IS_D_INVERTED),
      .IS_CLR_INVERTED(IS_PRE_INVERTED),
    ) _TECHMAP_REPLACE_ (
      .D(~D), .Q($Q), .C(C), .CE(CE), .CLR(PRE)
                                        // ^^^ Note that async
                                        //     control is not directly
                                        //     supported by abc9 but its
                                        //     behaviour is captured by
                                        //     $__ABC9_ASYNC0 below
    );
    $__ABC9_ASYNC0 abc_async (.A($QQ), .S(PRE ^ IS_PRE_INVERTED), .Y(QQ));
  end
  else begin
    assign Q = QQ;
    FDPE #(
      .INIT(1'b0),
      .IS_C_INVERTED(IS_C_INVERTED),
      .IS_D_INVERTED(IS_D_INVERTED),
      .IS_PRE_INVERTED(IS_PRE_INVERTED),
    ) _TECHMAP_REPLACE_ (
      .D(D), .Q($Q), .C(C), .CE(CE), .PRE(PRE)
                                       // ^^^ Note that async
                                       //     control is not directly
                                       //     supported by abc9 but its
                                       //     behaviour is captured by
                                       //     $__ABC9_ASYNC1 below
    );
    $__ABC9_ASYNC1 abc_async (.A($QQ), .S(PRE ^ IS_PRE_INVERTED), .Y(QQ));
  end endgenerate
  (* abc9_init = 1'b0 *)
  $__ABC9_FF_ abc9_ff (.D($Q), .Q($QQ));

  // Special signals
  wire [1:0] abc9_ff.clock = {C, IS_C_INVERTED};
  wire [0:0] _TECHMAP_REPLACE_.abc9_ff.Q = $QQ;
endmodule
module FDPE_1 (output Q, (* techmap_autopurge *) input C, CE, D, PRE);
  parameter [0:0] INIT = 1'b1;
  wire QQ, $Q, $QQ;
  generate if (INIT == 1'b1) begin
    assign Q = ~QQ;
    FDCE_1 #(
      .INIT(1'b0)
    ) _TECHMAP_REPLACE_ (
      .D(~D), .Q($Q), .C(C), .CE(CE), .CLR(PRE)
                                        // ^^^ Note that async
                                        //     control is not directly
                                        //     supported by abc9 but its
                                        //     behaviour is captured by
                                        //     $__ABC9_ASYNC0 below
    );
    $__ABC9_ASYNC0 abc_async (.A($QQ), .S(PRE), .Y(QQ));
  end
  else begin
    assign Q = QQ;
    FDPE_1 #(
      .INIT(1'b0)
    ) _TECHMAP_REPLACE_ (
      .D(D), .Q($Q), .C(C), .CE(CE), .PRE(PRE)
                                       // ^^^ Note that async
                                       //     control is not directly
                                       //     supported by abc9 but its
                                       //     behaviour is captured by
                                       //     $__ABC9_ASYNC1 below
    );
    $__ABC9_ASYNC1 abc_async (.A($QQ), .S(PRE), .Y(QQ));
  end endgenerate
  (* abc9_init = 1'b0 *)
  $__ABC9_FF_ abc9_ff (.D($Q), .Q($QQ));

  // Special signals
  wire [1:0] abc9_ff.clock = {C, 1'b1 /* IS_C_INVERTED */};
  wire [0:0] _TECHMAP_REPLACE_.abc9_ff.Q = $QQ;
endmodule
`endif

// Attach a (combinatorial) black-box onto the output
//   of thes LUTRAM primitives to capture their
//   asynchronous read behaviour
module RAM32X1D (
  output DPO, SPO,
  (* techmap_autopurge *) input  D,
  (* techmap_autopurge *) input  WCLK,
  (* techmap_autopurge *) input  WE,
  (* techmap_autopurge *) input  A0, A1, A2, A3, A4,
  (* techmap_autopurge *) input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4
);
  parameter INIT = 32'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire $DPO, $SPO;
  RAM32X1D #(
    .INIT(INIT), .IS_WCLK_INVERTED(IS_WCLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .DPO($DPO), .SPO($SPO),
    .D(D), .WCLK(WCLK), .WE(WE),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .A4(A4),
    .DPRA0(DPRA0), .DPRA1(DPRA1), .DPRA2(DPRA2), .DPRA3(DPRA3), .DPRA4(DPRA4)
  );
  $__ABC9_RAM6 spo (.A($SPO), .S({1'b1, A4, A3, A2, A1, A0}), .Y(SPO));
  $__ABC9_RAM6 dpo (.A($DPO), .S({1'b1, DPRA4, DPRA3, DPRA2, DPRA1, DPRA0}), .Y(DPO));
endmodule

module RAM64X1D (
  output DPO, SPO,
  (* techmap_autopurge *) input  D,
  (* techmap_autopurge *) input  WCLK,
  (* techmap_autopurge *) input  WE,
  (* techmap_autopurge *) input  A0, A1, A2, A3, A4, A5,
  (* techmap_autopurge *) input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4, DPRA5
);
  parameter INIT = 64'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire $DPO, $SPO;
  RAM64X1D #(
    .INIT(INIT), .IS_WCLK_INVERTED(IS_WCLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .DPO($DPO), .SPO($SPO),
    .D(D), .WCLK(WCLK), .WE(WE),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .A4(A4), .A5(A5),
    .DPRA0(DPRA0), .DPRA1(DPRA1), .DPRA2(DPRA2), .DPRA3(DPRA3), .DPRA4(DPRA4), .DPRA5(DPRA5)
  );
  $__ABC9_RAM6 spo (.A($SPO), .S({A5, A4, A3, A2, A1, A0}), .Y(SPO));
  $__ABC9_RAM6 dpo (.A($DPO), .S({DPRA5, DPRA4, DPRA3, DPRA2, DPRA1, DPRA0}), .Y(DPO));
endmodule

module RAM128X1D (
  output       DPO, SPO,
  (* techmap_autopurge *) input        D,
  (* techmap_autopurge *) input        WCLK,
  (* techmap_autopurge *) input        WE,
  (* techmap_autopurge *) input  [6:0] A, DPRA
);
  parameter INIT = 128'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire $DPO, $SPO;
  RAM128X1D #(
    .INIT(INIT), .IS_WCLK_INVERTED(IS_WCLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .DPO($DPO), .SPO($SPO),
    .D(D), .WCLK(WCLK), .WE(WE),
    .A(A),
    .DPRA(DPRA)
  );
  $__ABC9_RAM7 spo (.A($SPO), .S(A), .Y(SPO));
  $__ABC9_RAM7 dpo (.A($DPO), .S(DPRA), .Y(DPO));
endmodule

module RAM32M (
  output [1:0] DOA,
  output [1:0] DOB,
  output [1:0] DOC,
  output [1:0] DOD,
  (* techmap_autopurge *) input [4:0] ADDRA,
  (* techmap_autopurge *) input [4:0] ADDRB,
  (* techmap_autopurge *) input [4:0] ADDRC,
  (* techmap_autopurge *) input [4:0] ADDRD,
  (* techmap_autopurge *) input [1:0] DIA,
  (* techmap_autopurge *) input [1:0] DIB,
  (* techmap_autopurge *) input [1:0] DIC,
  (* techmap_autopurge *) input [1:0] DID,
  (* techmap_autopurge *) input WCLK,
  (* techmap_autopurge *) input WE
);
  parameter [63:0] INIT_A = 64'h0000000000000000;
  parameter [63:0] INIT_B = 64'h0000000000000000;
  parameter [63:0] INIT_C = 64'h0000000000000000;
  parameter [63:0] INIT_D = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [1:0] $DOA, $DOB, $DOC, $DOD;
  RAM32M #(
    .INIT_A(INIT_A), .INIT_B(INIT_B), .INIT_C(INIT_C), .INIT_D(INIT_D),
    .IS_WCLK_INVERTED(IS_WCLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .DOA($DOA), .DOB($DOB), .DOC($DOC), .DOD($DOD),
    .WCLK(WCLK), .WE(WE),
    .ADDRA(ADDRA), .ADDRB(ADDRB), .ADDRC(ADDRC), .ADDRD(ADDRD),
    .DIA(DIA), .DIB(DIB), .DIC(DIC), .DID(DID)
  );
  $__ABC9_RAM6 doa0 (.A($DOA[0]), .S({1'b1, ADDRA}), .Y(DOA[0]));
  $__ABC9_RAM6 doa1 (.A($DOA[1]), .S({1'b1, ADDRA}), .Y(DOA[1]));
  $__ABC9_RAM6 dob0 (.A($DOB[0]), .S({1'b1, ADDRB}), .Y(DOB[0]));
  $__ABC9_RAM6 dob1 (.A($DOB[1]), .S({1'b1, ADDRB}), .Y(DOB[1]));
  $__ABC9_RAM6 doc0 (.A($DOC[0]), .S({1'b1, ADDRC}), .Y(DOC[0]));
  $__ABC9_RAM6 doc1 (.A($DOC[1]), .S({1'b1, ADDRC}), .Y(DOC[1]));
  $__ABC9_RAM6 dod0 (.A($DOD[0]), .S({1'b1, ADDRD}), .Y(DOD[0]));
  $__ABC9_RAM6 dod1 (.A($DOD[1]), .S({1'b1, ADDRD}), .Y(DOD[1]));
endmodule

module RAM64M (
  output DOA,
  output DOB,
  output DOC,
  output DOD,
  (* techmap_autopurge *) input [5:0] ADDRA,
  (* techmap_autopurge *) input [5:0] ADDRB,
  (* techmap_autopurge *) input [5:0] ADDRC,
  (* techmap_autopurge *) input [5:0] ADDRD,
  (* techmap_autopurge *) input DIA,
  (* techmap_autopurge *) input DIB,
  (* techmap_autopurge *) input DIC,
  (* techmap_autopurge *) input DID,
  (* techmap_autopurge *) input WCLK,
  (* techmap_autopurge *) input WE
);
  parameter [63:0] INIT_A = 64'h0000000000000000;
  parameter [63:0] INIT_B = 64'h0000000000000000;
  parameter [63:0] INIT_C = 64'h0000000000000000;
  parameter [63:0] INIT_D = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire $DOA, $DOB, $DOC, $DOD;
  RAM64M #(
    .INIT_A(INIT_A), .INIT_B(INIT_B), .INIT_C(INIT_C), .INIT_D(INIT_D),
    .IS_WCLK_INVERTED(IS_WCLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .DOA($DOA), .DOB($DOB), .DOC($DOC), .DOD($DOD),
    .WCLK(WCLK), .WE(WE),
    .ADDRA(ADDRA), .ADDRB(ADDRB), .ADDRC(ADDRC), .ADDRD(ADDRD),
    .DIA(DIA), .DIB(DIB), .DIC(DIC), .DID(DID)
  );
  $__ABC9_RAM6 doa (.A($DOA), .S(ADDRA), .Y(DOA));
  $__ABC9_RAM6 dob (.A($DOB), .S(ADDRB), .Y(DOB));
  $__ABC9_RAM6 doc (.A($DOC), .S(ADDRC), .Y(DOC));
  $__ABC9_RAM6 dod (.A($DOD), .S(ADDRD), .Y(DOD));
endmodule

module SRL16 (
  output Q,
  (* techmap_autopurge *) input A0, A1, A2, A3, CLK, D
);
  parameter [15:0] INIT = 16'h0000;
  wire $Q;
  SRL16 #(
    .INIT(INIT),
  ) _TECHMAP_REPLACE_ (
    .Q($Q),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .CLK(CLK), .D(D)
  );
  $__ABC9_RAM6 q (.A($Q), .S({1'b1, A3, A2, A1, A0, 1'b1}), .Y(Q));
endmodule

module SRL16E (
  output Q,
  (* techmap_autopurge *) input A0, A1, A2, A3, CE, CLK, D
);
  parameter [15:0] INIT = 16'h0000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;
  wire $Q;
  SRL16E #(
    .INIT(INIT), .IS_CLK_INVERTED(IS_CLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .Q($Q),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .CE(CE), .CLK(CLK), .D(D)
  );
  $__ABC9_RAM6 q (.A($Q), .S({1'b1, A3, A2, A1, A0, 1'b1}), .Y(Q));
endmodule

module SRLC16 (
  output Q, Q15,
  (* techmap_autopurge *) input A0, A1, A2, A3, CLK, D
);
  parameter [15:0] INIT = 16'h0000;
  wire $Q;
  SRLC16 #(
    .INIT(INIT),
  ) _TECHMAP_REPLACE_ (
    .Q($Q), .Q(Q15),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .CLK(CLK), .D(D)
  );
  $__ABC9_RAM6 q (.A($Q), .S({1'b1, A3, A2, A1, A0, 1'b1}), .Y(Q));
endmodule

module SRLC16E (
  output Q, Q15,
  (* techmap_autopurge *) input A0, A1, A2, A3, CE, CLK, D
);
  parameter [15:0] INIT = 16'h0000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;
  wire $Q;
  SRLC16E #(
    .INIT(INIT), .IS_CLK_INVERTED(IS_CLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .Q($Q), .Q(Q15),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .CE(CE), .CLK(CLK), .D(D)
  );
  $__ABC9_RAM6 q (.A($Q), .S({1'b1, A3, A2, A1, A0, 1'b1}), .Y(Q));
endmodule

module SRLC32E (
  output Q,
  output Q31,
  (* techmap_autopurge *) input [4:0] A,
  (* techmap_autopurge *) input CE, CLK, D
);
  parameter [31:0] INIT = 32'h00000000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;
  wire $Q;
  SRLC32E #(
    .INIT(INIT), .IS_CLK_INVERTED(IS_CLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .Q($Q), .Q31(Q31),
    .A(A), .CE(CE), .CLK(CLK), .D(D)
  );
  $__ABC9_RAM6 q (.A($Q), .S({1'b1, A}), .Y(Q));
endmodule

module DSP48E1 (
    (* techmap_autopurge *) output [29:0] ACOUT,
    (* techmap_autopurge *) output [17:0] BCOUT,
    (* techmap_autopurge *) output reg CARRYCASCOUT,
    (* techmap_autopurge *) output reg [3:0] CARRYOUT,
    (* techmap_autopurge *) output reg MULTSIGNOUT,
    (* techmap_autopurge *) output OVERFLOW,
    (* techmap_autopurge *) output reg signed [47:0] P,
    (* techmap_autopurge *) output PATTERNBDETECT,
    (* techmap_autopurge *) output PATTERNDETECT,
    (* techmap_autopurge *) output [47:0] PCOUT,
    (* techmap_autopurge *) output UNDERFLOW,
    (* techmap_autopurge *) input signed [29:0] A,
    (* techmap_autopurge *) input [29:0] ACIN,
    (* techmap_autopurge *) input [3:0] ALUMODE,
    (* techmap_autopurge *) input signed [17:0] B,
    (* techmap_autopurge *) input [17:0] BCIN,
    (* techmap_autopurge *) input [47:0] C,
    (* techmap_autopurge *) input CARRYCASCIN,
    (* techmap_autopurge *) input CARRYIN,
    (* techmap_autopurge *) input [2:0] CARRYINSEL,
    (* techmap_autopurge *) input CEA1,
    (* techmap_autopurge *) input CEA2,
    (* techmap_autopurge *) input CEAD,
    (* techmap_autopurge *) input CEALUMODE,
    (* techmap_autopurge *) input CEB1,
    (* techmap_autopurge *) input CEB2,
    (* techmap_autopurge *) input CEC,
    (* techmap_autopurge *) input CECARRYIN,
    (* techmap_autopurge *) input CECTRL,
    (* techmap_autopurge *) input CED,
    (* techmap_autopurge *) input CEINMODE,
    (* techmap_autopurge *) input CEM,
    (* techmap_autopurge *) input CEP,
    (* techmap_autopurge *) input CLK,
    (* techmap_autopurge *) input [24:0] D,
    (* techmap_autopurge *) input [4:0] INMODE,
    (* techmap_autopurge *) input MULTSIGNIN,
    (* techmap_autopurge *) input [6:0] OPMODE,
    (* techmap_autopurge *) input [47:0] PCIN,
    (* techmap_autopurge *) input RSTA,
    (* techmap_autopurge *) input RSTALLCARRYIN,
    (* techmap_autopurge *) input RSTALUMODE,
    (* techmap_autopurge *) input RSTB,
    (* techmap_autopurge *) input RSTC,
    (* techmap_autopurge *) input RSTCTRL,
    (* techmap_autopurge *) input RSTD,
    (* techmap_autopurge *) input RSTINMODE,
    (* techmap_autopurge *) input RSTM,
    (* techmap_autopurge *) input RSTP
);
    parameter integer ACASCREG = 1;
    parameter integer ADREG = 1;
    parameter integer ALUMODEREG = 1;
    parameter integer AREG = 1;
    parameter AUTORESET_PATDET = "NO_RESET";
    parameter A_INPUT = "DIRECT";
    parameter integer BCASCREG = 1;
    parameter integer BREG = 1;
    parameter B_INPUT = "DIRECT";
    parameter integer CARRYINREG = 1;
    parameter integer CARRYINSELREG = 1;
    parameter integer CREG = 1;
    parameter integer DREG = 1;
    parameter integer INMODEREG = 1;
    parameter integer MREG = 1;
    parameter integer OPMODEREG = 1;
    parameter integer PREG = 1;
    parameter SEL_MASK = "MASK";
    parameter SEL_PATTERN = "PATTERN";
    parameter USE_DPORT = "FALSE";
    parameter USE_MULT = "MULTIPLY";
    parameter USE_PATTERN_DETECT = "NO_PATDET";
    parameter USE_SIMD = "ONE48";
    parameter [47:0] MASK = 48'h3FFFFFFFFFFF;
    parameter [47:0] PATTERN = 48'h000000000000;
    parameter [3:0] IS_ALUMODE_INVERTED = 4'b0;
    parameter [0:0] IS_CARRYIN_INVERTED = 1'b0;
    parameter [0:0] IS_CLK_INVERTED = 1'b0;
    parameter [4:0] IS_INMODE_INVERTED = 5'b0;
    parameter [6:0] IS_OPMODE_INVERTED = 7'b0;

    wire [47:0] $P, $PCOUT;

    DSP48E1 #(
        .ACASCREG(ACASCREG),
        .ADREG(ADREG),
        .ALUMODEREG(ALUMODEREG),
        .AREG(AREG),
        .AUTORESET_PATDET(AUTORESET_PATDET),
        .A_INPUT(A_INPUT),
        .BCASCREG(BCASCREG),
        .BREG(BREG),
        .B_INPUT(B_INPUT),
        .CARRYINREG(CARRYINREG),
        .CARRYINSELREG(CARRYINSELREG),
        .CREG(CREG),
        .DREG(DREG),
        .INMODEREG(INMODEREG),
        .MREG(MREG),
        .OPMODEREG(OPMODEREG),
        .PREG(PREG),
        .SEL_MASK(SEL_MASK),
        .SEL_PATTERN(SEL_PATTERN),
        .USE_DPORT(USE_DPORT),
        .USE_MULT(USE_MULT),
        .USE_PATTERN_DETECT(USE_PATTERN_DETECT),
        .USE_SIMD(USE_SIMD),
        .MASK(MASK),
        .PATTERN(PATTERN),
        .IS_ALUMODE_INVERTED(IS_ALUMODE_INVERTED),
        .IS_CARRYIN_INVERTED(IS_CARRYIN_INVERTED),
        .IS_CLK_INVERTED(IS_CLK_INVERTED),
        .IS_INMODE_INVERTED(IS_INMODE_INVERTED),
        .IS_OPMODE_INVERTED(IS_OPMODE_INVERTED)
    ) _TECHMAP_REPLACE_ (
        .ACOUT(ACOUT),
        .BCOUT(BCOUT),
        .CARRYCASCOUT(CARRYCASCOUT),
        .CARRYOUT(CARRYOUT),
        .MULTSIGNOUT(MULTSIGNOUT),
        .OVERFLOW(OVERFLOW),
        .P($P),
        .PATTERNBDETECT(PATTERNBDETECT),
        .PATTERNDETECT(PATTERNDETECT),
        .PCOUT($PCOUT),
        .UNDERFLOW(UNDERFLOW),
        .A(A),
        .ACIN(ACIN),
        .ALUMODE(ALUMODE),
        .B(B),
        .BCIN(BCIN),
        .C(C),
        .CARRYCASCIN(CARRYCASCIN),
        .CARRYIN(CARRYIN),
        .CARRYINSEL(CARRYINSEL),
        .CEA1(CEA1),
        .CEA2(CEA2),
        .CEAD(CEAD),
        .CEALUMODE(CEALUMODE),
        .CEB1(CEB1),
        .CEB2(CEB2),
        .CEC(CEC),
        .CECARRYIN(CECARRYIN),
        .CECTRL(CECTRL),
        .CED(CED),
        .CEINMODE(CEINMODE),
        .CEM(CEM),
        .CEP(CEP),
        .CLK(CLK),
        .D(D),
        .INMODE(INMODE),
        .MULTSIGNIN(MULTSIGNIN),
        .OPMODE(OPMODE),
        .PCIN(PCIN),
        .RSTA(RSTA),
        .RSTALLCARRYIN(RSTALLCARRYIN),
        .RSTALUMODE(RSTALUMODE),
        .RSTB(RSTB),
        .RSTC(RSTC),
        .RSTCTRL(RSTCTRL),
        .RSTD(RSTD),
        .RSTINMODE(RSTINMODE),
        .RSTM(RSTM),
        .RSTP(RSTP)
    );
    $__ABC9_DSP48E1 #(
        .ADREG(ADREG),
        .AREG(AREG),
        .BREG(BREG),
        .CREG(CREG),
        .DREG(DREG),
        .MREG(MREG),
        .PREG(PREG),
        .USE_DPORT(USE_DPORT),
        .USE_MULT(USE_MULT)
    ) dsp_comb (
        .$A(A), .$B(B), .$C(C), .$D(D), .$P($P), .$PCIN(PCIN), .$PCOUT($PCOUT), .P(P), .PCOUT(PCOUT));
endmodule
