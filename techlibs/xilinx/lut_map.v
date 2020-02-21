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
      if (LUT == 2'b01) begin
        INV _TECHMAP_REPLACE_ (.O(Y), .I(A[0]));
      end else begin
        LUT1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
          .I0(A[0]));
      end
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
    if (WIDTH == 5 && WIDTH <= `LUT_WIDTH) begin
      LUT5 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]));
    end else
    if (WIDTH == 6 && WIDTH <= `LUT_WIDTH) begin
      LUT6 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
    end else
    if (WIDTH == 5 && WIDTH > `LUT_WIDTH) begin
      wire f0, f1;
      \$lut #(.LUT(LUT[15: 0]), .WIDTH(4)) lut0 (.A(A[3:0]), .Y(f0));
      \$lut #(.LUT(LUT[31:16]), .WIDTH(4)) lut1 (.A(A[3:0]), .Y(f1));
      MUXF5 mux5(.I0(f0), .I1(f1), .S(A[4]), .O(Y));
    end else
    if (WIDTH == 6 && WIDTH > `LUT_WIDTH) begin
      wire f0, f1;
      \$lut #(.LUT(LUT[31: 0]), .WIDTH(5)) lut0 (.A(A[4:0]), .Y(f0));
      \$lut #(.LUT(LUT[63:32]), .WIDTH(5)) lut1 (.A(A[4:0]), .Y(f1));
      MUXF6 mux6(.I0(f0), .I1(f1), .S(A[5]), .O(Y));
    end else
    if (WIDTH == 7) begin
      wire f0, f1;
      \$lut #(.LUT(LUT[ 63: 0]), .WIDTH(6)) lut0 (.A(A[5:0]), .Y(f0));
      \$lut #(.LUT(LUT[127:64]), .WIDTH(6)) lut1 (.A(A[5:0]), .Y(f1));
      MUXF7 mux7(.I0(f0), .I1(f1), .S(A[6]), .O(Y));
    end else
    if (WIDTH == 8) begin
      wire f0, f1;
      \$lut #(.LUT(LUT[127:  0]), .WIDTH(7)) lut0 (.A(A[6:0]), .Y(f0));
      \$lut #(.LUT(LUT[255:128]), .WIDTH(7)) lut1 (.A(A[6:0]), .Y(f1));
      MUXF8 mux8(.I0(f0), .I1(f1), .S(A[7]), .O(Y));
    end else
    if (WIDTH == 9) begin
      wire f0, f1;
      \$lut #(.LUT(LUT[255:  0]), .WIDTH(8)) lut0 (.A(A[7:0]), .Y(f0));
      \$lut #(.LUT(LUT[511:256]), .WIDTH(8)) lut1 (.A(A[7:0]), .Y(f1));
      MUXF9 mux9(.I0(f0), .I1(f1), .S(A[8]), .O(Y));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule

`endif

