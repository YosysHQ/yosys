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
      SRLC32E #(.INIT(INIT_R[32-1: 0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D( D), .Q(T0), .Q31(T1));
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
      SRLC32E #(.INIT(INIT_R[32-1: 0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D( D), .Q(T0), .Q31(T1));
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
      SRLC32E #(.INIT(INIT_R[ 32-1: 0]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_0 (.A(L[4:0]), .CE(CE), .CLK(C), .D( D), .Q(T0), .Q31(T1));
      SRLC32E #(.INIT(INIT_R[ 64-1:32]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_1 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T1), .Q(T2), .Q31(T3));
      SRLC32E #(.INIT(INIT_R[ 96-1:64]), .IS_CLK_INVERTED(~CLKPOL[0])) fpga_srl_2 (.A(L[4:0]), .CE(CE), .CLK(C), .D(T3), .Q(T4), .Q31(T5));
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

`ifndef NO_MUXFN
module \$shiftx (A, B, Y);
  parameter A_SIGNED = 0;
  parameter B_SIGNED = 0;
  parameter A_WIDTH = 1;
  parameter B_WIDTH = 1;
  parameter Y_WIDTH = 1;

  input [A_WIDTH-1:0] A;
  input [B_WIDTH-1:0] B;
  output [Y_WIDTH-1:0] Y;

  parameter [B_WIDTH-1:0] _TECHMAP_CONSTMSK_B_ = 0;
  parameter [B_WIDTH-1:0] _TECHMAP_CONSTVAL_B_ = 0;

  generate
    genvar i, j;
    if (B_SIGNED) begin
      if (_TECHMAP_CONSTMSK_B_[B_WIDTH-1] && _TECHMAP_CONSTVAL_B_[B_WIDTH-1] == 1'b0)
        // Optimisation to remove B_SIGNED if sign bit of B is constant-0
        \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(0), .A_WIDTH(A_WIDTH), .B_WIDTH(B_WIDTH-1'd1), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A), .B(B[B_WIDTH-2:0]), .Y(Y));
      else
        wire _TECHMAP_FAIL_ = 1;
    end
    else if (Y_WIDTH > 1) begin
      for (i = 0; i < Y_WIDTH; i++)
        \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(A_WIDTH-Y_WIDTH+1), .B_WIDTH(B_WIDTH), .Y_WIDTH(1'd1)) bitblast (.A(A[A_WIDTH-Y_WIDTH+i:i]), .B(B), .Y(Y[i]));
    end
    // If the LSB of B is constant zero (and Y_WIDTH is 1) then
    //   we can optimise by removing every other entry from A
    //   and popping the constant zero from B
    else if (_TECHMAP_CONSTMSK_B_[0] && !_TECHMAP_CONSTVAL_B_[0]) begin
      wire [(A_WIDTH+1)/2-1:0] A_i;
      for (i = 0; i < (A_WIDTH+1)/2; i++)
        assign A_i[i] = A[i*2];
      \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH((A_WIDTH+1'd1)/2'd2), .B_WIDTH(B_WIDTH-1'd1), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A_i), .B(B[B_WIDTH-1:1]), .Y(Y));
    end
    else if (B_WIDTH < 3 || A_WIDTH <= 4) begin
      wire _TECHMAP_FAIL_ = 1;
    end
    else if (B_WIDTH == 3) begin
      localparam a_width0 = 2 ** 2;
      localparam a_widthN = A_WIDTH - a_width0;
      wire T0, T1;
      \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_width0), .B_WIDTH(2),                .Y_WIDTH(Y_WIDTH)) fpga_shiftx      (.A(A[a_width0-1:0]),       .B(B[2-1:0]),                .Y(T0));
      \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_widthN), .B_WIDTH($clog2(a_widthN)), .Y_WIDTH(Y_WIDTH)) fpga_shiftx_last (.A(A[A_WIDTH-1:a_width0]), .B(B[$clog2(a_widthN)-1:0]), .Y(T1));
      MUXF7 fpga_mux (.I0(T0), .I1(T1), .S(B[B_WIDTH-1]), .O(Y));
    end
    else if (B_WIDTH == 4) begin
      localparam a_width0 = 2 ** 2;
      localparam num_mux8 = A_WIDTH / a_width0;
      localparam a_widthN = A_WIDTH - num_mux8*a_width0;
      wire [4-1:0] T;
      wire T0, T1;
      for (i = 0; i < 4; i++)
        if (i < num_mux8)
          \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_width0), .B_WIDTH(2),                .Y_WIDTH(Y_WIDTH)) fpga_shiftx      (.A(A[i*a_width0+:a_width0]), .B(B[2-1:0]),                .Y(T[i]));
        else if (i == num_mux8 && a_widthN > 0)
          \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_widthN), .B_WIDTH($clog2(a_widthN)), .Y_WIDTH(Y_WIDTH)) fpga_shiftx_last (.A(A[A_WIDTH-1:i*a_width0]), .B(B[$clog2(a_widthN)-1:0]), .Y(T[i]));
        else
          assign T[i] = 1'bx;
      MUXF7 fpga_mux_0 (.I0(T[0]), .I1(T[1]), .S(B[2]), .O(T0));
      MUXF7 fpga_mux_1 (.I0(T[2]), .I1(T[3]), .S(B[2]), .O(T1));
      MUXF8 fpga_mux_2 (.I0(T0),   .I1(T1),   .S(B[3]), .O(Y));
    end
    else begin
      localparam a_width0 = 2 ** 4;
      localparam num_mux16 = A_WIDTH / a_width0;
      localparam a_widthN = A_WIDTH - num_mux16*a_width0;
      wire [(2**(B_WIDTH-4))-1:0] T;
      for (i = 0; i < 2 ** (B_WIDTH-4); i++)
        if (i < num_mux16)
          \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_width0), .B_WIDTH(4),                .Y_WIDTH(Y_WIDTH)) fpga_shiftx      (.A(A[i*a_width0+:a_width0]), .B(B[4-1:0]),                .Y(T[i]));
        else if (i == num_mux16 && a_widthN > 0) begin
          \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_widthN), .B_WIDTH($clog2(a_widthN)), .Y_WIDTH(Y_WIDTH)) fpga_shiftx_last (.A(A[A_WIDTH-1:i*a_width0]), .B(B[$clog2(a_widthN)-1:0]), .Y(T[i]));
        end
        else
          assign T[i] = 1'bx;
      \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(2**(B_WIDTH-4)), .B_WIDTH(B_WIDTH-4), .Y_WIDTH(Y_WIDTH)) fpga_shiftx (.A(T), .B(B[B_WIDTH-1:4]), .Y(Y));
    end
  endgenerate
endmodule
`endif // NO_MUXFN
