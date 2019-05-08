module  \$_DFF_N_ (input D, C, output Q); DFFN _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C)); endmodule
module  \$_DFF_P_ #(parameter INIT = 1'b0) (input D, C, output Q); DFF  #(.INIT(INIT)) _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C)); endmodule

module  \$__DFFS_PN0_ (input D, C, R, output Q); DFFR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(!R)); endmodule
module  \$__DFFS_PP0_ (input D, C, R, output Q); DFFR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R)); endmodule
module  \$__DFFS_PP1_ (input D, C, R, output Q); DFFR  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R)); endmodule

module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      LUT1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.F(Y),
        .I0(A[0]));
    end else
    if (WIDTH == 2) begin
      LUT2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.F(Y),
        .I0(A[0]), .I1(A[1]));
    end else
    if (WIDTH == 3) begin
      LUT3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.F(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]));
    end else
    if (WIDTH == 4) begin
      LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.F(Y),
        .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
