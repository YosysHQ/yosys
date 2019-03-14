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

module \$__SHREG_ (input C, input D, input E, output Q);
  parameter DEPTH = 0;
  parameter [DEPTH-1:0] INIT = 0;
  parameter CLKPOL = 1;
  parameter ENPOL = 2;
  wire CE;
  generate
    if (ENPOL == 0)
      assign CE = ~E;
    else if (ENPOL == 1)
      assign CE = E;
    else
      assign CE = 1'b1;
    if (DEPTH == 1) begin
        FDRE #(.INIT(INIT), .IS_C_INVERTED(~CLKPOL[0]), .IS_D_INVERTED(|0), .IS_R_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(CE), .R(1'b0));
    end else
    if (DEPTH <= 16) begin
      localparam [3:0] A = DEPTH - 1;
      SRL16E #(.INIT(INIT), .IS_CLK_INVERTED(~CLKPOL[0])) _TECHMAP_REPLACE_ (.A0(A[0]), .A1(A[1]), .A2(A[2]), .A3(A[3]), .CE(CE), .CLK(C), .D(D), .Q(Q));
    end else
    if (DEPTH > 17 && DEPTH <= 32) begin
      SRLC32E #(.INIT(INIT), .IS_CLK_INVERTED(~CLKPOL[0])) _TECHMAP_REPLACE_ (.A(DEPTH-1), .CE(CE), .CLK(C), .D(D), .Q(Q));
    end else
    if (DEPTH > 33 && DEPTH <= 64) begin
      wire T0, T1, T2;
      localparam [5:0] A = DEPTH-1;
      SRLC32E #(.INIT(INIT[32-1:0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(A[4:0]), .CE(CE), .CLK(C), .D(D), .Q(T0), .Q31(T1));
      \$__SHREG_ #(.DEPTH(DEPTH-32), .INIT(INIT[DEPTH-1:32]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_1 (.C(C), .D(T1), .E(E), .Q(T2));
      MUXF7 fpga_mux_0 (.O(Q), .I0(T0), .I1(T2), .S(A[5]));
    end else
    if (DEPTH > 65 && DEPTH <= 96) begin
      localparam [6:0] A = DEPTH-1;
      wire T0, T1, T2, T3, T4, T5, T6;
      SRLC32E #(.INIT(INIT[32-1:0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(A[4:0]), .CE(CE), .CLK(C), .D(D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT[64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(A[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      \$__SHREG_ #(.DEPTH(DEPTH-64), .INIT(INIT[DEPTH-1:64]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_2 (.C(C), .D(T3), .E(E), .Q(T4));
      MUXF7 fpga_mux_0 (.O(T5), .I0(T0), .I1(T2), .S(A[5]));
      MUXF7 fpga_mux_1 (.O(T6), .I0(T4), .I1(1'b0 /* unused */), .S(A[5]));
      MUXF8 fpga_mux_2 (.O(Q), .I0(T5), .I1(T6), .S(A[6]));
    end else
    if (DEPTH > 97 && DEPTH <= 128) begin
      localparam [6:0] A = DEPTH-1;
      wire T0, T1, T2, T3, T4, T5, T6, T7, T8;
      SRLC32E #(.INIT(INIT[32-1:0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(A[4:0]), .CE(CE), .CLK(C), .D(D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT[64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(A[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      SRLC32E #(.INIT(INIT[96-1:64]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_2 (.A(A[4:0]), .CE(CE), .CLK(C), .D(T3), .Q(T4), .Q31(T5));
      \$__SHREG_ #(.DEPTH(DEPTH-96), .INIT(INIT[DEPTH-1:96]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_3 (.C(C), .D(T5), .E(E), .Q(T6));
      MUXF7 fpga_mux_0 (.O(T7), .I0(T0), .I1(T2), .S(A[5]));
      MUXF7 fpga_mux_1 (.O(T8), .I0(T4), .I1(T6), .S(A[5]));
      MUXF8 fpga_mux_2 (.O(Q), .I0(T7), .I1(T8), .S(A[6]));
    end
    else if (DEPTH <= 129) begin
      // Handle cases where depth is just 1 over a convenient value,
      // in which case use the flop
      wire T0;
      \$__SHREG_ #(.DEPTH(DEPTH-1), .INIT(INIT[DEPTH-2:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_0 (.C(C), .D(D), .E(E), .Q(T0));
      \$__SHREG_ #(.DEPTH(1), .INIT(INIT[DEPTH-1]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_1 (.C(C), .D(T0), .E(E), .Q(Q));
    end else
    begin
      // UG474 (v1.8, p34) states that:
      //   "There are no direct connections between slices to form longer shift
      //    registers, nor is the MC31 output at LUT B/C/D available."
      wire T0;
      \$__SHREG_ #(.DEPTH(128), .INIT(INIT[128-1:0]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_0 (.C(C), .D(D), .E(E), .Q(T0));
      \$__SHREG_ #(.DEPTH(DEPTH-128), .INIT(INIT[DEPTH-1:128]), .CLKPOL(CLKPOL), .ENPOL(ENPOL)) fpga_srl_1 (.C(C), .D(T0), .E(E), .Q(Q));
    end
  endgenerate
endmodule
