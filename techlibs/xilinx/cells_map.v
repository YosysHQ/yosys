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
        \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(0), .A_WIDTH(A_WIDTH), .B_WIDTH(B_WIDTH-1), .Y_WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A), .B(B[B_WIDTH-2:0]), .Y(Y));
      else
        wire _TECHMAP_FAIL_ = 1;
    end
    else if (Y_WIDTH > 1) begin
      wire [$clog2(A_WIDTH/Y_WIDTH)-1:0] B_bitty = B/Y_WIDTH;
      for (i = 0; i < Y_WIDTH; i++) begin
        wire [A_WIDTH/Y_WIDTH-1:0] A_i;
        for (j = 0; j < A_WIDTH/Y_WIDTH; j++)
          assign A_i[j] = A[j*Y_WIDTH+i];
        \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(A_WIDTH/Y_WIDTH), .B_WIDTH($clog2(A_WIDTH/Y_WIDTH)), .Y_WIDTH(1)) bitblast (.A(A_i), .B(B_bitty), .Y(Y[i]));
      end
    end
    else if (B_WIDTH < 3) begin
      wire _TECHMAP_FAIL_ = 1;
    end
    else if (B_WIDTH == 3) begin
      localparam a_width0 = 2 ** 2;
      localparam a_widthN = A_WIDTH - a_width0;
      wire T0, T1;
      \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_width0), .B_WIDTH(B_WIDTH-1),        .Y_WIDTH(Y_WIDTH)) fpga_shiftx      (.A(A[a_width0-1:0]),       .B(B[B_WIDTH-2:0]), .Y(T0));
      \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_widthN), .B_WIDTH($clog2(a_widthN)), .Y_WIDTH(Y_WIDTH)) fpga_shiftx_last (.A(A[A_WIDTH-1:a_width0]), .B(B[$clog2(a_widthN)-1:0]), .Y(T1));
      MUXF7 fpga_mux (.I0(T0), .I1(T1), .S(B[B_WIDTH-1]), .O(Y));
    end
    else if (B_WIDTH == 4) begin
      localparam a_width0 = 2 ** 3;
      localparam num_mux8 = A_WIDTH / a_width0;
      localparam a_widthN = A_WIDTH - num_mux8*a_width0;
      wire [B_WIDTH-1:0] T;
      wire T0, T1;
      for (i = 0; i < B_WIDTH; i++)
        if (i < num_mux8)
          \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_width0), .B_WIDTH(B_WIDTH-2),        .Y_WIDTH(Y_WIDTH)) fpga_shiftx      (.A(A[i*a_width0+:a_width0]), .B(B[B_WIDTH-3:0]),          .Y(T[i]));
        else if (i == num_mux8 && a_widthN > 0)
          \$shiftx  #(.A_SIGNED(A_SIGNED), .B_SIGNED(B_SIGNED), .A_WIDTH(a_widthN), .B_WIDTH($clog2(a_widthN)), .Y_WIDTH(Y_WIDTH)) fpga_shiftx_last (.A(A[A_WIDTH-1:i*a_width0]), .B(B[$clog2(a_widthN)-1:0]), .Y(T[i]));
        else
          assign T[i] = 1'bx;
      MUXF7 fpga_mux_0 (.I0(T[0]), .I1(T[1]), .S(B[B_WIDTH-2]), .O(T0));
      MUXF7 fpga_mux_1 (.I0(T[2]), .I1(T[3]), .S(B[B_WIDTH-2]), .O(T1));
      MUXF8 fpga_mux_2 (.I0(T0),   .I1(T1),   .S(B[B_WIDTH-1]), .O(Y));
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
