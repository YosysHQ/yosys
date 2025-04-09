/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

module \$__SHREG_ (input C, input D, input E, output Q);
  parameter DEPTH = 0;
  parameter [DEPTH-1:0] INIT = 0;
  parameter CLKPOL = 1;
  parameter ENPOL = 2;

  \$__XILINX_SHREG_ #(.DEPTH(DEPTH), .INIT(INIT), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) _TECHMAP_REPLACE_ (.C(C), .D(D), .L(DEPTH-1), .E(E), .Q(Q));
endmodule

module \$__XILINX_SHREG_ (input C, input D, input [31:0] L, input E, output Q, output SO);
  parameter DEPTH = 0;
  parameter [DEPTH-1:0] INIT = 0;
  parameter CLKPOL = 1;
  parameter ENPOL = 2;

  // shregmap's INIT parameter shifts out LSB first;
  // however Xilinx expects MSB first
  function [DEPTH-1:0] brev;
    input [DEPTH-1:0] din;
    integer i;
    begin
      for (i = 0; i < DEPTH; i=i+1)
        brev[i] = din[DEPTH-1-i];
    end
  endfunction
  localparam [DEPTH-1:0] INIT_R = brev(INIT);

  parameter _TECHMAP_CONSTMSK_L_ = 0;

  wire CE;
  generate
    if (ENPOL == 0)
      assign CE = ~E;
    else if (ENPOL == 1)
      assign CE = E;
    else
      assign CE = 1'b1;
    if (DEPTH == 1) begin
      if (CLKPOL)
          FDRE #(.INIT(INIT_R)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(CE), .R(1'b0));
      else
          FDRE_1 #(.INIT(INIT_R)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(CE), .R(1'b0));
    end else
    if (DEPTH <= 16) begin
      SRL16E #(.INIT(INIT_R), .IS_CLK_INVERTED(~CLKPOL[0])) _TECHMAP_REPLACE_ (.A0(L[0]), .A1(L[1]), .A2(L[2]), .A3(L[3]), .CE(CE), .CLK(C), .D(D), .Q(Q));
    end else
    if (DEPTH > 17 && DEPTH <= 32) begin
      SRLC32E #(.INIT(INIT_R), .IS_CLK_INVERTED(~CLKPOL[0])) _TECHMAP_REPLACE_ (.A(L[4:0]), .CE(CE), .CLK(C), .D(D), .Q(Q));
    end else
    if (DEPTH > 33 && DEPTH <= 64) begin
      wire T0, T1, T2;
      SRLC32E #(.INIT(INIT_R[32-1:0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D(D), .Q(T0), .Q31(T1));
      \$__XILINX_SHREG_ #(.DEPTH(DEPTH-32), .INIT(INIT[DEPTH-32-1:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_1 (.C(C), .D(T1), .L(L), .E(E), .Q(T2));
      if (&_TECHMAP_CONSTMSK_L_)
        assign Q = T2;
      else
        MUXF7 fpga_mux_0 (.O(Q), .I0(T0), .I1(T2), .S(L[5]));
    end else
    if (DEPTH > 65 && DEPTH <= 96) begin
      wire T0, T1, T2, T3, T4, T5, T6;
      SRLC32E #(.INIT(INIT_R[32-1: 0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D( D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT_R[64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      \$__XILINX_SHREG_ #(.DEPTH(DEPTH-64), .INIT(INIT[DEPTH-64-1:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_2 (.C(C), .D(T3), .L(L[4:0]), .E(E), .Q(T4));
      if (&_TECHMAP_CONSTMSK_L_)
        assign Q = T4;
      else
        \$__XILINX_MUXF78 fpga_hard_mux (.I0(T0), .I1(T2), .I2(T4), .I3(1'bx), .S0(L[5]), .S1(L[6]), .O(Q));
    end else
    if (DEPTH > 97 && DEPTH < 128) begin
      wire T0, T1, T2, T3, T4, T5, T6, T7, T8;
      SRLC32E #(.INIT(INIT_R[32-1: 0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D( D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT_R[64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      SRLC32E #(.INIT(INIT_R[96-1:64]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_2 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T3), .Q(T4), .Q31(T5));
      \$__XILINX_SHREG_ #(.DEPTH(DEPTH-96), .INIT(INIT[DEPTH-96-1:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_3 (.C(C), .D(T5), .L(L[4:0]), .E(E), .Q(T6));
      if (&_TECHMAP_CONSTMSK_L_)
        assign Q = T6;
      else
        \$__XILINX_MUXF78 fpga_hard_mux (.I0(T0), .I1(T2), .I2(T4), .I3(T6), .S0(L[5]), .S1(L[6]), .O(Q));
    end
    else if (DEPTH == 128) begin
      wire T0, T1, T2, T3, T4, T5, T6;
      SRLC32E #(.INIT(INIT_R[ 32-1: 0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D( D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT_R[ 64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      SRLC32E #(.INIT(INIT_R[ 96-1:64]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_2 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T3), .Q(T4), .Q31(T5));
      SRLC32E #(.INIT(INIT_R[128-1:96]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_3 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T5), .Q(T6), .Q31(SO));
      if (&_TECHMAP_CONSTMSK_L_)
        assign Q = T6;
      else
        \$__XILINX_MUXF78 fpga_hard_mux (.I0(T0), .I1(T2), .I2(T4), .I3(T6), .S0(L[5]), .S1(L[6]), .O(Q));
    end
    // For fixed length, if just 1 over a convenient value, decompose
    else if (DEPTH <= 129 && &_TECHMAP_CONSTMSK_L_) begin
      wire T;
      \$__XILINX_SHREG_ #(.DEPTH(DEPTH-1), .INIT(INIT[DEPTH-1:1]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl      (.C(C), .D(D), .L({32{1'b1}}), .E(E), .Q(T));
      \$__XILINX_SHREG_ #(.DEPTH(1),       .INIT(INIT[0]),         .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_last (.C(C), .D(T), .L(L), .E(E), .Q(Q));
    end
    // For variable length, if just 1 over a convenient value, then bump up one more
    else if (DEPTH < 129 && ~&_TECHMAP_CONSTMSK_L_)
      \$__XILINX_SHREG_ #(.DEPTH(DEPTH+1), .INIT({INIT,1'b0}), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) _TECHMAP_REPLACE_ (.C(C), .D(D), .L(L), .E(E), .Q(Q));
    else begin
      localparam depth0 = 128;
      localparam num_srl128 = DEPTH / depth0;
      localparam depthN = DEPTH % depth0;
      wire [num_srl128 + (depthN > 0 ? 1 : 0) - 1:0] T;
      wire [num_srl128 + (depthN > 0 ? 1 : 0) :0] S;
      assign S[0] = D;
      genvar i;
      for (i = 0; i < num_srl128; i++)
        \$__XILINX_SHREG_ #(.DEPTH(depth0), .INIT(INIT[DEPTH-1-i*depth0-:depth0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl      (.C(C), .D(S[i]),          .L(L[$clog2(depth0)-1:0]), .E(E), .Q(T[i]), .SO(S[i+1]));

      if (depthN > 0)
        \$__XILINX_SHREG_ #(.DEPTH(depthN), .INIT(INIT[depthN-1:0]),               .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_last (.C(C), .D(S[num_srl128]), .L(L[$clog2(depth0)-1:0]), .E(E), .Q(T[num_srl128]));

      if (&_TECHMAP_CONSTMSK_L_)
        assign Q = T[num_srl128 + (depthN > 0 ? 1 : 0) - 1];
      else
        assign Q = T[L[DEPTH-1:$clog2(depth0)]];
    end
  endgenerate
endmodule

`ifdef MIN_MUX_INPUTS
module \$__XILINX_SHIFTX (A, B, Y);
  parameter A_SIGNED = 0;
  parameter B_SIGNED = 0;
  parameter A_WIDTH = 1;
  parameter B_WIDTH = 1;
  parameter Y_WIDTH = 1;

  (* force_downto *)
  input [A_WIDTH-1:0] A;
  (* force_downto *)
  input [B_WIDTH-1:0] B;
  (* force_downto *)
  output [Y_WIDTH-1:0] Y;

  parameter [A_WIDTH-1:0] _TECHMAP_CONSTMSK_A_ = 0;
  parameter [A_WIDTH-1:0] _TECHMAP_CONSTVAL_A_ = 0;
  parameter [B_WIDTH-1:0] _TECHMAP_CONSTMSK_B_ = 0;
  parameter [B_WIDTH-1:0] _TECHMAP_CONSTVAL_B_ = 0;

  function integer A_WIDTH_trimmed;
    input integer start;
  begin
    A_WIDTH_trimmed = start;
    while (A_WIDTH_trimmed > 0 && _TECHMAP_CONSTMSK_A_[A_WIDTH_trimmed-1] && _TECHMAP_CONSTVAL_A_[A_WIDTH_trimmed-1] === 1'bx)
      A_WIDTH_trimmed = A_WIDTH_trimmed - 1;
  end
  endfunction

  generate
    genvar i, j;
    // Bit-blast
    if (Y_WIDTH > 1) begin
      for (i = 0; i < Y_WIDTH; i++)
        \$__XILINX_SHIFTX  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(A_WIDTH-Y_WIDTH+1), .B_WIDTH(B_WIDTH), .Y_WIDTH(1'd1)) bitblast (.A(A[A_WIDTH-Y_WIDTH+i:i]), .B(B), .Y(Y[i]));
    end
    // If the LSB of B is constant zero (and Y_WIDTH is 1) then
    //   we can optimise by removing every other entry from A
    //   and popping the constant zero from B
    else if (_TECHMAP_CONSTMSK_B_[0] && !_TECHMAP_CONSTVAL_B_[0]) begin
      wire [(A_WIDTH+1)/2-1:0] A_i;
      for (i = 0; i < (A_WIDTH+1)/2; i++)
        assign A_i[i] = A[i*2];
      \$__XILINX_SHIFTX  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH((A_WIDTH+1'd1)/2'd2), .B_WIDTH(B_WIDTH-1'd1), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A_i), .B(B[B_WIDTH-1:1]), .Y(Y));
    end
    // Trim off any leading 1'bx -es in A
    else if (_TECHMAP_CONSTMSK_A_[A_WIDTH-1] && _TECHMAP_CONSTVAL_A_[A_WIDTH-1] === 1'bx) begin
      localparam A_WIDTH_new = A_WIDTH_trimmed(A_WIDTH-1);
      if (A_WIDTH_new == 0)
        assign Y = 1'bx;
      else
        \$__XILINX_SHIFTX  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(A_WIDTH_new), .B_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A[A_WIDTH_new-1:0]), .B(B), .Y(Y));
    end
    else if (A_WIDTH < `MIN_MUX_INPUTS) begin
      wire _TECHMAP_FAIL_ = 1;
    end
    else if (A_WIDTH == 2) begin
      MUXF7 fpga_hard_mux (.I0(A[0]), .I1(A[1]), .S(B[0]), .O(Y));
    end
    else if (A_WIDTH <= 4) begin
      wire [4-1:0] Ax;
      if (A_WIDTH == 4)
        assign Ax = A;
      else
        // Rather than extend with 1'bx which gets flattened to 1'b0
        // causing the "don't care" status to get lost, extend with
        // the same driver of F7B.I0 so that we can optimise F7B away
        // later
        assign Ax = {A[1], A};
      \$__XILINX_MUXF78 fpga_hard_mux (.I0(Ax[0]), .I1(Ax[2]), .I2(Ax[1]), .I3(Ax[3]), .S0(B[1]), .S1(B[0]), .O(Y));
    end
    // Note that the following decompositions are 'backwards' in that
    // the LSBs are placed on the hard resources, and the soft resources
    // are used for MSBs.
    // This has the effect of more effectively utilising the hard mux;
    // take for example a 5:1 multiplexer, currently this would map as:
    //
    //     A[0] \___  __                             A[0] \__  __
    //     A[4] /   \|  \       whereas the more     A[1] /  \|  \
    //     A[1] _____|   |      obvious mapping      A[2] \___|   |
    //     A[2] _____|   |--    of MSBs to hard      A[3] /   |   |__
    //     A[3]______|   |      resources would      A[4] ____|   |
    //               |__/       lead to:             1'bx ____|   |
    //                ||                                      |__/
    //                ||                                       ||
    //              B[1:0]                                   B[1:2]
    //
    // Expectation would be that the 'forward' mapping (right) is more
    // area efficient (consider a 9:1 multiplexer using 2x4:1 multiplexers
    // on its I0 and I1 inputs, and A[8] and 1'bx on its I2 and I3 inputs)
    // but that the 'backwards' mapping (left) is more delay efficient
    // since smaller LUTs are faster than wider ones.
    else if (A_WIDTH <= 8) begin
      wire [8-1:0] Ax = {{{8-A_WIDTH}{1'bx}}, A};
      wire T0 = B[2] ? Ax[4] : Ax[0];
      wire T1 = B[2] ? Ax[5] : Ax[1];
      wire T2 = B[2] ? Ax[6] : Ax[2];
      wire T3 = B[2] ? Ax[7] : Ax[3];
      \$__XILINX_MUXF78 fpga_hard_mux (.I0(T0), .I1(T2), .I2(T1), .I3(T3), .S0(B[1]), .S1(B[0]), .O(Y));
    end
    else if (A_WIDTH <= 16) begin
      wire [16-1:0] Ax = {{{16-A_WIDTH}{1'bx}}, A};
      wire T0 = B[2] ? B[3] ? Ax[12] : Ax[4]
                     : B[3] ? Ax[ 8] : Ax[0];
      wire T1 = B[2] ? B[3] ? Ax[13] : Ax[5]
                     : B[3] ? Ax[ 9] : Ax[1];
      wire T2 = B[2] ? B[3] ? Ax[14] : Ax[6]
                     : B[3] ? Ax[10] : Ax[2];
      wire T3 = B[2] ? B[3] ? Ax[15] : Ax[7]
                     : B[3] ? Ax[11] : Ax[3];
      \$__XILINX_MUXF78 fpga_hard_mux (.I0(T0), .I1(T2), .I2(T1), .I3(T3), .S0(B[1]), .S1(B[0]), .O(Y));
    end
    else begin
      localparam num_mux16 = (A_WIDTH+15) / 16;
      localparam clog2_num_mux16 = $clog2(num_mux16);
      wire [num_mux16-1:0] T;
      wire [num_mux16*16-1:0] Ax = {{(num_mux16*16-A_WIDTH){1'bx}}, A};
      for (i = 0; i < num_mux16; i++)
        \$__XILINX_SHIFTX  #(
          .A_SIGNED(A_SIGNED),
          .B_SIGNED(B_SIGNED),
          .A_WIDTH(16),
          .B_WIDTH(4),
          .Y_WIDTH(Y_WIDTH)
        ) fpga_mux (
          .A(Ax[i*16+:16]),
          .B(B[3:0]),
          .Y(T[i])
        );
      \$__XILINX_SHIFTX  #(
          .A_SIGNED(A_SIGNED),
          .B_SIGNED(B_SIGNED),
          .A_WIDTH(num_mux16),
          .B_WIDTH(clog2_num_mux16),
          .Y_WIDTH(Y_WIDTH)
      ) _TECHMAP_REPLACE_ (
          .A(T),
          .B(B[B_WIDTH-1-:clog2_num_mux16]),
          .Y(Y));
    end
  endgenerate
endmodule

(* techmap_celltype = "$__XILINX_SHIFTX" *)
module _90__XILINX_SHIFTX (A, B, Y);
  parameter A_SIGNED = 0;
  parameter B_SIGNED = 0;
  parameter A_WIDTH = 1;
  parameter B_WIDTH = 1;
  parameter Y_WIDTH = 1;

  (* force_downto *)
  input [A_WIDTH-1:0] A;
  (* force_downto *)
  input [B_WIDTH-1:0] B;
  (* force_downto *)
  output [Y_WIDTH-1:0] Y;

  \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(A_WIDTH), .B_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A), .B(B), .Y(Y));
endmodule

module \$_MUX_ (A, B, S, Y);
  input A, B, S;
  output Y;
  generate
    if (`MIN_MUX_INPUTS == 2)
      \$__XILINX_SHIFTX  #(.A_SIGNED(0), .B_SIGNED(0), .A_WIDTH(2), .B_WIDTH(1), .Y_WIDTH(1)) _TECHMAP_REPLACE_ (.A({B,A}), .B(S), .Y(Y));
    else
      wire _TECHMAP_FAIL_ = 1;
  endgenerate
endmodule

module \$_MUX4_ (A, B, C, D, S, T, Y);
  input A, B, C, D, S, T;
  output Y;
  \$__XILINX_SHIFTX  #(.A_SIGNED(0), .B_SIGNED(0), .A_WIDTH(4), .B_WIDTH(2), .Y_WIDTH(1)) _TECHMAP_REPLACE_ (.A({D,C,B,A}), .B({T,S}), .Y(Y));
endmodule

module \$_MUX8_ (A, B, C, D, E, F, G, H, S, T, U, Y);
  input A, B, C, D, E, F, G, H, S, T, U;
  output Y;
  \$__XILINX_SHIFTX  #(.A_SIGNED(0), .B_SIGNED(0), .A_WIDTH(8), .B_WIDTH(3), .Y_WIDTH(1)) _TECHMAP_REPLACE_ (.A({H,G,F,E,D,C,B,A}), .B({U,T,S}), .Y(Y));
endmodule

module \$_MUX16_ (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, S, T, U, V, Y);
  input A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, S, T, U, V;
  output Y;
  \$__XILINX_SHIFTX  #(.A_SIGNED(0), .B_SIGNED(0), .A_WIDTH(16), .B_WIDTH(4), .Y_WIDTH(1)) _TECHMAP_REPLACE_ (.A({P,O,N,M,L,K,J,I,H,G,F,E,D,C,B,A}), .B({V,U,T,S}), .Y(Y));
endmodule
`endif

module \$__XILINX_MUXF78 (O, I0, I1, I2, I3, S0, S1);
  output O;
  input I0, I1, I2, I3, S0, S1;
  wire T0, T1;
  parameter _TECHMAP_BITS_CONNMAP_ = 0;
  parameter [_TECHMAP_BITS_CONNMAP_-1:0] _TECHMAP_CONNMAP_I0_ = 0;
  parameter [_TECHMAP_BITS_CONNMAP_-1:0] _TECHMAP_CONNMAP_I1_ = 0;
  parameter [_TECHMAP_BITS_CONNMAP_-1:0] _TECHMAP_CONNMAP_I2_ = 0;
  parameter [_TECHMAP_BITS_CONNMAP_-1:0] _TECHMAP_CONNMAP_I3_ = 0;
  parameter _TECHMAP_CONSTMSK_S0_ = 0;
  parameter _TECHMAP_CONSTVAL_S0_ = 0;
  parameter _TECHMAP_CONSTMSK_S1_ = 0;
  parameter _TECHMAP_CONSTVAL_S1_ = 0;
  if (_TECHMAP_CONSTMSK_S0_ && _TECHMAP_CONSTVAL_S0_ === 1'b1)
    assign T0 = I1;
  else if (_TECHMAP_CONSTMSK_S0_ || _TECHMAP_CONNMAP_I0_ === _TECHMAP_CONNMAP_I1_)
    assign T0 = I0;
  else
    MUXF7 mux7a (.I0(I0), .I1(I1), .S(S0), .O(T0));
  if (_TECHMAP_CONSTMSK_S0_ && _TECHMAP_CONSTVAL_S0_ === 1'b1)
    assign T1 = I3;
  else if (_TECHMAP_CONSTMSK_S0_ || _TECHMAP_CONNMAP_I2_ === _TECHMAP_CONNMAP_I3_)
    assign T1 = I2;
  else
    MUXF7 mux7b (.I0(I2), .I1(I3), .S(S0), .O(T1));
  if (_TECHMAP_CONSTMSK_S1_ && _TECHMAP_CONSTVAL_S1_ === 1'b1)
    assign O = T1;
  else if (_TECHMAP_CONSTMSK_S1_ || (_TECHMAP_CONNMAP_I0_ === _TECHMAP_CONNMAP_I1_ && _TECHMAP_CONNMAP_I1_ === _TECHMAP_CONNMAP_I2_ && _TECHMAP_CONNMAP_I2_ === _TECHMAP_CONNMAP_I3_))
    assign O = T0;
  else
    MUXF8 mux8 (.I0(T0), .I1(T1), .S(S1), .O(O));
endmodule
