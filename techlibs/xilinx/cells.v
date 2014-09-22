module  \$_DFF_P_ (D, C, Q);

  input D, C;
  output Q;

  FDRE fpga_dff (
  	.D(D), .Q(Q), .C(C),
  	.CE(1'b1), .R(1'b0)
  );

endmodule

module \$lut (A, Y);

  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin:lut1
      LUT1 #(.INIT(LUT)) fpga_lut (.O(Y),
        .I0(A[0]));
    end else
    if (WIDTH == 2) begin:lut2
      LUT2 #(.INIT(LUT)) fpga_lut (.O(Y),
        .I0(A[0]), .I1(A[1]));
    end else
    if (WIDTH == 3) begin:lut3
      LUT3 #(.INIT(LUT)) fpga_lut (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]));
    end else
    if (WIDTH == 4) begin:lut4
      LUT4 #(.INIT(LUT)) fpga_lut (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]));
    end else
    if (WIDTH == 5) begin:lut5
      LUT5 #(.INIT(LUT)) fpga_lut (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]));
    end else
    if (WIDTH == 6) begin:lut6
      LUT6 #(.INIT(LUT)) fpga_lut (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
    end else begin:error
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate

endmodule
