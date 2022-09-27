module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      LUT1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]));

    end else
    if (WIDTH == 2) begin
      LUT2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]));

    end else
    if (WIDTH == 3) begin
      LUT3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(A[2]));

    end else
    if (WIDTH == 4) begin
      LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule

/* module  \$_DFF_P_ (input D, C, output Q); LUTFF _TECHMAP_REPLACE_ (.D(D), .O(Q), .CLK(C)); endmodule
module  \$_DFF_N_ (input D, C, output Q); SB_DFFN _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C)); endmodule
module  \$_DFF_P_ (input D, C, output Q); SB_DFF  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C)); endmodule

module  \$_DFFE_NP_ (input D, C, E, output Q); SB_DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); SB_DFFE  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E)); endmodule

module  \$_DFF_NP0_ (input D, C, R, output Q); SB_DFFNR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(R)); endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); SB_DFFNS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .S(R)); endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); SB_DFFR  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(R)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); SB_DFFS  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .S(R)); endmodule

module  \$_DFFE_NP0P_ (input D, C, E, R, output Q); SB_DFFNER _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(R)); endmodule
module  \$_DFFE_NP1P_ (input D, C, E, R, output Q); SB_DFFNES _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(R)); endmodule
module  \$_DFFE_PP0P_ (input D, C, E, R, output Q); SB_DFFER  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(R)); endmodule
module  \$_DFFE_PP1P_ (input D, C, E, R, output Q); SB_DFFES  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(R)); endmodule

module  \$_SDFF_NP0_ (input D, C, R, output Q); SB_DFFNSR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(R)); endmodule
module  \$_SDFF_NP1_ (input D, C, R, output Q); SB_DFFNSS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .S(R)); endmodule
module  \$_SDFF_PP0_ (input D, C, R, output Q); SB_DFFSR  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .R(R)); endmodule
module  \$_SDFF_PP1_ (input D, C, R, output Q); SB_DFFSS  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .S(R)); endmodule

module  \$_SDFFCE_NP0P_ (input D, C, E, R, output Q); SB_DFFNESR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(R)); endmodule
module  \$_SDFFCE_NP1P_ (input D, C, E, R, output Q); SB_DFFNESS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(R)); endmodule
module  \$_SDFFCE_PP0P_ (input D, C, E, R, output Q); SB_DFFESR  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(R)); endmodule
module  \$_SDFFCE_PP1P_ (input D, C, E, R, output Q); SB_DFFESS  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(R)); endmodule */