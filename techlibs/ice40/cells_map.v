module  \$_DFF_N_ (input D, C, output Q); SB_DFFN _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C)); endmodule
module  \$_DFF_P_ (input D, C, output Q); SB_DFF  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C)); endmodule

module  \$_DFFE_NN_ (input D, C, E, output Q); SB_DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(!E)); endmodule
module  \$_DFFE_PN_ (input D, C, E, output Q); SB_DFFE  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(!E)); endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q); SB_DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); SB_DFFE  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E)); endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q); SB_DFFNR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(!R)); endmodule
module  \$_DFF_NN1_ (input D, C, R, output Q); SB_DFFNS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .S(!R)); endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q); SB_DFFR  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(!R)); endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q); SB_DFFS  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .S(!R)); endmodule

module  \$_DFF_NP0_ (input D, C, R, output Q); SB_DFFNR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(R)); endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); SB_DFFNS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .S(R)); endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); SB_DFFR  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(R)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); SB_DFFS  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .S(R)); endmodule

module  \$__DFFE_NN0 (input D, C, E, R, output Q); SB_DFFNER _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(!R)); endmodule
module  \$__DFFE_NN1 (input D, C, E, R, output Q); SB_DFFNES _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(!R)); endmodule
module  \$__DFFE_PN0 (input D, C, E, R, output Q); SB_DFFER  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(!R)); endmodule
module  \$__DFFE_PN1 (input D, C, E, R, output Q); SB_DFFES  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(!R)); endmodule

module  \$__DFFE_NP0 (input D, C, E, R, output Q); SB_DFFNER _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(R)); endmodule
module  \$__DFFE_NP1 (input D, C, E, R, output Q); SB_DFFNES _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(R)); endmodule
module  \$__DFFE_PP0 (input D, C, E, R, output Q); SB_DFFER  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(R)); endmodule
module  \$__DFFE_PP1 (input D, C, E, R, output Q); SB_DFFES  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(R)); endmodule

`ifndef NO_LUT
module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      localparam [15:0] INIT = {{8{LUT[1]}}, {8{LUT[0]}}};
      SB_LUT4 #(.LUT_INIT(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(1'b0), .I1(1'b0), .I2(1'b0), .I3(A[0]));
    end else
    if (WIDTH == 2) begin
      localparam [15:0] INIT = {{4{LUT[3]}}, {4{LUT[2]}}, {4{LUT[1]}}, {4{LUT[0]}}};
      SB_LUT4 #(.LUT_INIT(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(1'b0), .I1(1'b0), .I2(A[0]), .I3(A[1]));
    end else
    if (WIDTH == 3) begin
      localparam [15:0] INIT = {{2{LUT[7]}}, {2{LUT[6]}}, {2{LUT[5]}}, {2{LUT[4]}}, {2{LUT[3]}}, {2{LUT[2]}}, {2{LUT[1]}}, {2{LUT[0]}}};
      SB_LUT4 #(.LUT_INIT(INIT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(1'b0), .I1(A[0]), .I2(A[1]), .I3(A[2]));
    end else
    if (WIDTH == 4) begin
      SB_LUT4 #(.LUT_INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
`endif
