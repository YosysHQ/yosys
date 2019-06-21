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

module \$shiftx (A, B, Y);
  parameter A_SIGNED = 0;
  parameter B_SIGNED = 0;
  parameter A_WIDTH = 1;
  parameter B_WIDTH = 1;
  parameter Y_WIDTH = 1;

  input [A_WIDTH-1:0] A;
  input [B_WIDTH-1:0] B;
  output [Y_WIDTH-1:0] Y;

  parameter [A_WIDTH-1:0] _TECHMAP_CONSTMSK_A_ = 0;
  parameter [A_WIDTH-1:0] _TECHMAP_CONSTVAL_A_ = 0;
  parameter [B_WIDTH-1:0] _TECHMAP_CONSTMSK_B_ = 0;
  parameter [B_WIDTH-1:0] _TECHMAP_CONSTVAL_B_ = 0;

  generate
    genvar i;
    wire [A_WIDTH-1:0] A_forward;
    assign A_backward[A_WIDTH-1] = A[A_WIDTH-1];
    for (i = A_WIDTH-2; i >= 0; i = i - 1)
      if (_TECHMAP_CONSTMSK_A_[i] && _TECHMAP_CONSTVAL_A_[i] === 1'bx)
        assign A_backward[i] = A_backward[i+1];
      else
        assign A_backward[i] = A[i];

    wire [A_WIDTH-1:0] A_without_x;
    assign A_without_x[0] = A_backward[0];
    for (i = 1; i < A_WIDTH; i = i + 1)
      if (_TECHMAP_CONSTMSK_A_[i] && _TECHMAP_CONSTVAL_A_[i] === 1'bx)
        assign A_without_x[i] = A_without_x[i-1];
      else
        assign A_without_x[i] = A[i];

    if (B_SIGNED) begin
      if (B_WIDTH < 4 || A_WIDTH <= 4)
        wire _TECHMAP_FAIL_ = 1;
      else if (_TECHMAP_CONSTMSK_B_[B_WIDTH-1] && (_TECHMAP_CONSTVAL_B_[B_WIDTH-1] == 1'b0 || _TECHMAP_CONSTVAL_B_[B_WIDTH-1] === 1'bx))
        // Optimisation to remove B_SIGNED if sign bit of B is constant-0
        \$__XILINX_SHIFTX #(
          .A_SIGNED(A_SIGNED),
          .B_SIGNED(0),
          .A_WIDTH(A_WIDTH),
          .B_WIDTH(B_WIDTH-1'd1),
          .Y_WIDTH(Y_WIDTH)
        ) _TECHMAP_REPLACE_ (
          .A(A_without_x), .B(B[B_WIDTH-2:0]), .Y(Y)
        );
      else
        wire _TECHMAP_FAIL_ = 1;
    end
    else begin
      if (B_WIDTH < 3 || A_WIDTH <= 4)
        wire _TECHMAP_FAIL_ = 1;
      else
        \$__XILINX_SHIFTX #(
          .A_SIGNED(A_SIGNED),
          .B_SIGNED(B_SIGNED),
          .A_WIDTH(A_WIDTH),
          .B_WIDTH(B_WIDTH),
          .Y_WIDTH(Y_WIDTH)
        ) _TECHMAP_REPLACE_ (
          .A(A_without_x), .B(B), .Y(Y)
        );
    end
  endgenerate
endmodule

module \$_MUX4_ (A, B, C, D, S, T, Y);
input A, B, C, D, S, T;
output Y;
assign Y = T ? (S ? D : C) :
               (S ? B : A);
endmodule
