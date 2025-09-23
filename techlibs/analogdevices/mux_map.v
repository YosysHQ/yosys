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

// The purpose of these mapping rules is to allow preserve all (sufficiently
// wide) $shiftx cells during 'techmap' so that they can be mapped to hard
// resources, rather than being bit-blasted to gates during 'techmap'
// execution

module \$shiftx (A, B, Y);
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

  parameter [B_WIDTH-1:0] _TECHMAP_CONSTMSK_B_ = 0;
  parameter [B_WIDTH-1:0] _TECHMAP_CONSTVAL_B_ = 0;

  generate
    if (B_SIGNED) begin
      if (_TECHMAP_CONSTMSK_B_[B_WIDTH-1] && (_TECHMAP_CONSTVAL_B_[B_WIDTH-1] == 1'b0 || _TECHMAP_CONSTVAL_B_[B_WIDTH-1] === 1'bx))
        // Optimisation to remove B_SIGNED if sign bit of B is constant-0
        \$shiftx #(
          .A_SIGNED(A_SIGNED),
          .B_SIGNED(0),
          .A_WIDTH(A_WIDTH),
          .B_WIDTH(B_WIDTH-1'd1),
          .Y_WIDTH(Y_WIDTH)
        ) _TECHMAP_REPLACE_ (
          .A(A), .B(B[B_WIDTH-2:0]), .Y(Y)
        );
      else
        wire _TECHMAP_FAIL_ = 1;
    end
    else begin
      if (((A_WIDTH + Y_WIDTH - 1) / Y_WIDTH) < `MIN_MUX_INPUTS)
        wire _TECHMAP_FAIL_ = 1;
      else
        \$__XILINX_SHIFTX #(
          .A_SIGNED(A_SIGNED),
          .B_SIGNED(B_SIGNED),
          .A_WIDTH(A_WIDTH),
          .B_WIDTH(B_WIDTH),
          .Y_WIDTH(Y_WIDTH)
        ) _TECHMAP_REPLACE_ (
          .A(A), .B(B), .Y(Y)
        );
    end
  endgenerate
endmodule
