
module  \$_DFF_N_ (input D, C, output Q); FDRE #(.INIT(|0), .IS_C_INVERTED(|1), .IS_D_INVERTED(|0), .IS_R_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0)); endmodule
module  \$_DFF_P_ (input D, C, output Q); FDRE #(.INIT(|0), .IS_C_INVERTED(|0), .IS_D_INVERTED(|0), .IS_R_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .R(1'b0)); endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q); FDRE #(.INIT(|0), .IS_C_INVERTED(|1), .IS_D_INVERTED(|0), .IS_R_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R(1'b0)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); FDRE #(.INIT(|0), .IS_C_INVERTED(|0), .IS_D_INVERTED(|0), .IS_R_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(E), .R(1'b0)); endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q); FDCE #(.INIT(|0), .IS_C_INVERTED(|1), .IS_D_INVERTED(|0), .IS_CLR_INVERTED(|1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR(R)); endmodule
module  \$_DFF_NP0_ (input D, C, R, output Q); FDCE #(.INIT(|0), .IS_C_INVERTED(|1), .IS_D_INVERTED(|0), .IS_CLR_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR(R)); endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q); FDCE #(.INIT(|0), .IS_C_INVERTED(|0), .IS_D_INVERTED(|0), .IS_CLR_INVERTED(|1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR(R)); endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); FDCE #(.INIT(|0), .IS_C_INVERTED(|0), .IS_D_INVERTED(|0), .IS_CLR_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .CLR(R)); endmodule

module  \$_DFF_NN1_ (input D, C, R, output Q); FDPE #(.INIT(|0), .IS_C_INVERTED(|1), .IS_D_INVERTED(|0), .IS_PRE_INVERTED(|1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE(R)); endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); FDPE #(.INIT(|0), .IS_C_INVERTED(|1), .IS_D_INVERTED(|0), .IS_PRE_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE(R)); endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q); FDPE #(.INIT(|0), .IS_C_INVERTED(|0), .IS_D_INVERTED(|0), .IS_PRE_INVERTED(|1)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE(R)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); FDPE #(.INIT(|0), .IS_C_INVERTED(|0), .IS_D_INVERTED(|0), .IS_PRE_INVERTED(|0)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .CE(1'b1), .PRE(R)); endmodule

`ifndef NO_LUT
module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      LUT1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0]));
    end else
    if (WIDTH == 2) begin
      LUT2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0]),
        .I1(A[1]));
    end else
    if (WIDTH == 3) begin
      LUT3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]));
    end else
    if (WIDTH == 4) begin
      LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]));
    end else
    if (WIDTH == 5) begin
      LUT5 #(.INIT(LUT)) _TECHMAP_REPLACE_ (
        .O(Y),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
    end else
    if (WIDTH == 6) begin
      // LUT5+LUT5+MUXF6 == LUT6
      wire T0, T1;
      LUT5 #(.INIT(LUT[31:0])) fpga_lut_0 (
        .O(T0),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      LUT5 #(.INIT(LUT[63:32])) fpga_lut_1 (
        .O(T1),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      MUXF6 fpga_mux_0 (.O(Y), .I0(T0), .I1(T1), .S(A[5]));
    end else
    if (WIDTH == 7) begin
      wire T0, T1;

      // LUT5+LUT5+MUXF6 == LUT6
      wire T00, T01;
      LUT5 #(.INIT(LUT[31:0])) fpga_lut_00 (
        .O(T00),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      LUT5 #(.INIT(LUT[63:32])) fpga_lut_01 (
        .O(T01),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      MUXF6 fpga_mux_0 (.O(T0), .I0(T00), .I1(T01), .S(A[5]));

      // LUT5+LUT5+MUXF6 == LUT6
      wire T10, T11;
      LUT5 #(.INIT(LUT[95:64])) fpga_lut_10 (
        .O(T10),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      LUT5 #(.INIT(LUT[127:96])) fpga_lut_11 (
        .O(T11),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      MUXF6 fpga_mux_1 (.O(T1), .I0(T10), .I1(T11), .S(A[5]));

      // LUT6+LUT6+MUXF7 == LUT7
      MUXF7 fpga_mux_2 (.O(Y), .I0(T0), .I1(T1), .S(A[6]));
    end else
    if (WIDTH == 8) begin
      wire T0, T1, T2, T3;

      // LUT5+LUT5+MUXF6 == LUT6
      wire T00, T01;
      LUT5 #(.INIT(LUT[31:0])) fpga_lut_00 (
        .O(T00),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      LUT5 #(.INIT(LUT[63:32])) fpga_lut_01 (
        .O(T01),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      MUXF6 fpga_mux_0 (.O(T0), .I0(T00), .I1(T01), .S(A[5]));

      // LUT5+LUT5+MUXF6 == LUT6
      wire T10, T11;
      LUT5 #(.INIT(LUT[95:64])) fpga_lut_10 (
        .O(T10),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      LUT5 #(.INIT(LUT[127:96])) fpga_lut_11 (
        .O(T11),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      MUXF6 fpga_mux_1 (.O(T1), .I0(T10), .I1(T11), .S(A[5]));

      // LUT5+LUT5+MUXF6 == LUT6
      wire T20, T21;
      LUT5 #(.INIT(LUT[159:128])) fpga_lut_20 (
        .O(T20),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      LUT5 #(.INIT(LUT[191:160])) fpga_lut_21 (
        .O(T21),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      MUXF6 fpga_mux_2 (.O(T2), .I0(T20), .I1(T21), .S(A[5]));

      // LUT5+LUT5+MUXF6 == LUT6
      wire T30, T31;
      LUT5 #(.INIT(LUT[223:192])) fpga_lut_30 (
        .O(T30),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      LUT5 #(.INIT(LUT[255:224])) fpga_lut_31 (
        .O(T31),
        .I0(A[0]),
        .I1(A[1]),
        .I2(A[2]),
        .I3(A[3]),
        .I4(A[4]));
      MUXF6 fpga_mux_3 (.O(T3), .I0(T30), .I1(T31), .S(A[5]));

      // LUT6+LUT6+MUXF7 == LUT7
      wire T4, T5;
      MUXF7 fpga_mux_4 (.O(T4), .I0(T0), .I1(T1), .S(A[6]));
      MUXF7 fpga_mux_5 (.O(T5), .I0(T2), .I1(T3), .S(A[6]));

      // LUT7+LUT7+MUXF8 == LUT8
      MUXF8 fpga_mux_6 (.O(Y),  .I0(T4), .I1(T5), .S(A[7]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
`endif
