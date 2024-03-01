`default_nettype none

module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  (* force_downto *)
  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      localparam [15:0] INIT = {{8{LUT[1]}}, {8{LUT[0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(1'b0), .I2(1'b0), .I3(1'b0), .I4(A[0]));
    end else
    if (WIDTH == 2) begin
      localparam [15:0] INIT = {{4{LUT[3]}}, {4{LUT[2]}}, {4{LUT[1]}}, {4{LUT[0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(1'b0), .I2(1'b0), .I3(A[0]), .I4(A[1]));
    end else
    if (WIDTH == 3) begin
      localparam [15:0] INIT = {{2{LUT[7]}}, {2{LUT[6]}}, {2{LUT[5]}}, {2{LUT[4]}}, {2{LUT[3]}}, {2{LUT[2]}}, {2{LUT[1]}}, {2{LUT[0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(1'b0), .I2(A[0]), .I3(A[1]), .I4(A[2]));
    end else
    if (WIDTH == 4) begin
      NX_LUT #(.lut_table(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(A[1]), .I3(A[2]), .I4(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
