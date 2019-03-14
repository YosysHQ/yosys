module  \$_DFF_N_ (input D, C, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(!C), .EN(1'b1), .ALn(1'b1), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module  \$_DFF_P_ (input D, C, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(1'b1), .ALn(1'b1), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFF_NN0_ (input D, C, R, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(!C), .EN(1'b1), .ALn(R), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFF_NN1_ (input D, C, R, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(!C), .EN(1'b1), .ALn(R), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFF_NP0_ (input D, C, R, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(!C), .EN(1'b1), .ALn(!R), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFF_NP1_ (input D, C, R, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(!C), .EN(1'b1), .ALn(!R), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFF_PN0_ (input D, C, R, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(1'b1), .ALn(R), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFF_PN1_ (input D, C, R, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(1'b1), .ALn(R), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFF_PP0_ (input D, C, R, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(1'b1), .ALn(!R), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFF_PP1_ (input D, C, R, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(1'b1), .ALn(!R), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

// module  \$_DFFE_NN_ (input D, C, E, output Q); SB_DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(!E)); endmodule
// module  \$_DFFE_PN_ (input D, C, E, output Q); SB_DFFE  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(!E)); endmodule
//
// module  \$_DFFE_NP_ (input D, C, E, output Q); SB_DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E)); endmodule
// module  \$_DFFE_PP_ (input D, C, E, output Q); SB_DFFE  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E)); endmodule
//
// module  \$__DFFE_NN0 (input D, C, E, R, output Q); SB_DFFNER _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(!R)); endmodule
// module  \$__DFFE_NN1 (input D, C, E, R, output Q); SB_DFFNES _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(!R)); endmodule
// module  \$__DFFE_PN0 (input D, C, E, R, output Q); SB_DFFER  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(!R)); endmodule
// module  \$__DFFE_PN1 (input D, C, E, R, output Q); SB_DFFES  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(!R)); endmodule
//
// module  \$__DFFE_NP0 (input D, C, E, R, output Q); SB_DFFNER _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(R)); endmodule
// module  \$__DFFE_NP1 (input D, C, E, R, output Q); SB_DFFNES _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(R)); endmodule
// module  \$__DFFE_PP0 (input D, C, E, R, output Q); SB_DFFER  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .R(R)); endmodule
// module  \$__DFFE_PP1 (input D, C, E, R, output Q); SB_DFFES  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .C(C), .E(E), .S(R)); endmodule

`ifndef NO_LUT
module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      CFG1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Y(Y), .A(A[0]));
    end else
    if (WIDTH == 2) begin
      CFG2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Y(Y), .A(A[0]), .B(A[1]));
    end else
    if (WIDTH == 3) begin
      CFG3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Y(Y), .A(A[0]), .B(A[1]), .C(A[2]));
    end else
    if (WIDTH == 4) begin
      CFG4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.Y(Y), .A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
`endif
