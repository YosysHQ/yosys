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
    end else
    if (WIDTH == 7) begin:lut7
      wire T0, T1;
      LUT6 #(.INIT(LUT[63:0])) fpga_lut_0 (.O(T0),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
      LUT6 #(.INIT(LUT[127:64])) fpga_lut_1 (.O(T1),
        .I0(A[0]), .I1(A[1]), .I2(A[2]),
        .I3(A[3]), .I4(A[4]), .I5(A[5]));
      MUXF7 fpga_mux_0 (.O(Y), .I0(T0), .I1(T1), .S(A[6]));
    end else
    if (WIDTH == 8) begin:lut8
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
    end else begin:error
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate

endmodule
