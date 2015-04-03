module  \$_DFF_P_ (input D, C, output Q);
  SB_DFF _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C));
endmodule

module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      SB_LUT4 #(.LUT_INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(1'b0), .I2(1'b0), .I3(1'b0));
    end else
    if (WIDTH == 2) begin
      SB_LUT4 #(.LUT_INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(1'b0), .I3(1'b0));
    end else
    if (WIDTH == 3) begin
      SB_LUT4 #(.LUT_INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(1'b0));
    end else
    if (WIDTH == 4) begin
      SB_LUT4 #(.LUT_INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
