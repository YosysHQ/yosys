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

// Convert negative-polarity reset to positive-polarity
(* techmap_celltype = "$_DFF_NN0_" *)
module _90_dff_nn0_to_np0 (input D, C, R, output Q); \$_DFF_NP0_  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(~R)); endmodule
(* techmap_celltype = "$_DFF_PN0_" *)
module _90_dff_pn0_to_pp0 (input D, C, R, output Q); \$_DFF_PP0_  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(~R)); endmodule
(* techmap_celltype = "$_DFF_NN1_" *)
module _90_dff_nn1_to_np1 (input D, C, R, output Q); \$_DFF_NP1   _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(~R)); endmodule
(* techmap_celltype = "$_DFF_PN1_" *)
module _90_dff_pn1_to_pp1 (input D, C, R, output Q); \$_DFF_PP1   _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(~R)); endmodule

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
  parameter _TECHMAP_CONSTVAL_L_ = 0;

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
      SRLC32E #(.INIT(INIT_R[32-1:0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D(D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT_R[64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      \$__XILINX_SHREG_ #(.DEPTH(DEPTH-64), .INIT(INIT[DEPTH-64-1:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_2 (.C(C), .D(T3), .L(L[4:0]), .E(E), .Q(T4));
      if (&_TECHMAP_CONSTMSK_L_)
        assign Q = T4;
      else begin
        MUXF7 fpga_mux_0 (.O(T5), .I0(T0), .I1(T2), .S(L[5]));
        MUXF7 fpga_mux_1 (.O(T6), .I0(T4), .I1(1'b0 /* unused */), .S(L[5]));
        MUXF8 fpga_mux_2 (.O(Q), .I0(T5), .I1(T6), .S(L[6]));
      end
    end else
    if (DEPTH > 97 && DEPTH < 128) begin
      wire T0, T1, T2, T3, T4, T5, T6, T7, T8;
      SRLC32E #(.INIT(INIT_R[32-1:0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D(D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT_R[64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      SRLC32E #(.INIT(INIT_R[96-1:64]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_2 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T3), .Q(T4), .Q31(T5));
      \$__XILINX_SHREG_ #(.DEPTH(DEPTH-96), .INIT(INIT[DEPTH-96-1:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_3 (.C(C), .D(T5), .L(L[4:0]), .E(E), .Q(T6));
      if (&_TECHMAP_CONSTMSK_L_)
        assign Q = T6;
      else begin
        MUXF7 fpga_mux_0 (.O(T7), .I0(T0), .I1(T2), .S(L[5]));
        MUXF7 fpga_mux_1 (.O(T8), .I0(T4), .I1(T6), .S(L[5]));
        MUXF8 fpga_mux_2 (.O(Q), .I0(T7), .I1(T8), .S(L[6]));
      end
    end
    else if (DEPTH == 128) begin
      wire T0, T1, T2, T3, T4, T5, T6;
      SRLC32E #(.INIT(INIT_R[32-1:0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D(D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT_R[64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      SRLC32E #(.INIT(INIT_R[96-1:64]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_2 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T3), .Q(T4), .Q31(T5));
      SRLC32E #(.INIT(INIT_R[128-1:96]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_3 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T5), .Q(T6), .Q31(SO));
      if (&_TECHMAP_CONSTMSK_L_)
        assign Q = T6;
      else begin
        wire T7, T8;
        MUXF7 fpga_mux_0 (.O(T7), .I0(T0), .I1(T2), .S(L[5]));
        MUXF7 fpga_mux_1 (.O(T8), .I0(T4), .I1(T6), .S(L[5]));
        MUXF8 fpga_mux_2 (.O(Q), .I0(T7), .I1(T8), .S(L[6]));
      end
    end
    else if (DEPTH <= 129 && ~&_TECHMAP_CONSTMSK_L_) begin
      // Handle cases where fixed-length depth is
      // just 1 over a convenient value
      \$__XILINX_SHREG_ #(.DEPTH(DEPTH+1), .INIT({INIT,1'b0}), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) _TECHMAP_REPLACE_ (.C(C), .D(D), .L(L), .E(E), .Q(Q));
    end
    else begin
      localparam lower_clog2 = $clog2((DEPTH+1)/2);
      localparam lower_depth = 2 ** lower_clog2;
      wire T0, T1, T2, T3;
      if (&_TECHMAP_CONSTMSK_L_) begin
        \$__XILINX_SHREG_ #(.DEPTH(lower_depth), .INIT(INIT[DEPTH-1:DEPTH-lower_depth]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_0 (.C(C), .D(D), .L(lower_depth-1), .E(E), .Q(T0));
        \$__XILINX_SHREG_ #(.DEPTH(DEPTH-lower_depth), .INIT(INIT[DEPTH-lower_depth-1:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_1 (.C(C), .D(T0), .L(DEPTH-lower_depth-1), .E(E), .Q(Q), .SO(T3));
      end
      else begin
        \$__XILINX_SHREG_ #(.DEPTH(lower_depth), .INIT(INIT[DEPTH-1:DEPTH-lower_depth]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_0 (.C(C), .D(D), .L(L[lower_clog2-1:0]), .E(E), .Q(T0), .SO(T1));
        \$__XILINX_SHREG_ #(.DEPTH(DEPTH-lower_depth), .INIT(INIT[DEPTH-lower_depth-1:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_1 (.C(C), .D(T1), .L(L[lower_clog2-1:0]), .E(E), .Q(T2), .SO(T3));
        assign Q = L[lower_clog2] ? T2 : T0;
      end
      if (DEPTH == 2 * lower_depth)
          assign SO = T3;
    end
  endgenerate
endmodule

`ifndef SRL_ONLY
`endif
