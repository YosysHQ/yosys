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

// ============================================================================
// LUT mapping

`ifndef _NO_LUTS

module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      LUT1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]));
    end else
    if (WIDTH == 2) begin
      LUT2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]));
    end else
    if (WIDTH == 3) begin
      LUT3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]));
    end else
    if (WIDTH == 4) begin
      LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]));
    end else
    if (WIDTH == 5) begin
      LUT5 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]));
    end else
    if (WIDTH == 6) begin
      LUT6 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
    end else
    if (WIDTH == 7) begin
      wire T0, T1;
      LUT6 #(.INIT(LUT[63:0])) fpga_lut_0 (.O(T0),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
      LUT6 #(.INIT(LUT[127:64])) fpga_lut_1 (.O(T1),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
      MUXF7 fpga_mux_0 (.O(Y), .I0(T0), .I1(T1), .S(A[6]));
    end else
    if (WIDTH == 8) begin
      wire T0, T1, T2, T3, T4, T5;
      LUT6 #(.INIT(LUT[63:0])) fpga_lut_0 (.O(T0),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
      LUT6 #(.INIT(LUT[127:64])) fpga_lut_1 (.O(T1),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
      LUT6 #(.INIT(LUT[191:128])) fpga_lut_2 (.O(T2),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
      LUT6 #(.INIT(LUT[255:192])) fpga_lut_3 (.O(T3),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
      MUXF7 fpga_mux_0 (.O(T4), .I0(T0), .I1(T1), .S(A[6]));
      MUXF7 fpga_mux_1 (.O(T5), .I0(T2), .I1(T3), .S(A[6]));
      MUXF8 fpga_mux_2 (.O(Y), .I0(T4), .I1(T5), .S(A[7]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule

`endif

