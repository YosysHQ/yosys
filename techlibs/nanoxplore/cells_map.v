`default_nettype none

module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  (* force_downto *)
  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      localparam [15:0] INIT = {{2{LUT[1:0]}}, {2{LUT[1:0]}}, {2{LUT[1:0]}}, {2{LUT[1:0]}},
                                {2{LUT[1:0]}}, {2{LUT[1:0]}}, {2{LUT[1:0]}}, {2{LUT[1:0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(1'b0), .I3(1'b0), .I4(1'b0));
    end else
    if (WIDTH == 2) begin
      localparam [15:0] INIT = {{4{LUT[3:0]}}, {4{LUT[3:0]}}, {4{LUT[3:0]}}, {4{LUT[3:0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(A[1]), .I3(1'b0), .I4(1'b0), );
    end else
    if (WIDTH == 3) begin
      localparam [15:0] INIT = {{8{LUT[7:0]}}, {8{LUT[7:0]}}};
      NX_LUT #(.lut_table(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(A[1]), .I3(A[2]), .I4(1'b0));
    end else
    if (WIDTH == 4) begin
      NX_LUT #(.lut_table(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I1(A[0]), .I2(A[1]), .I3(A[2]), .I4(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
