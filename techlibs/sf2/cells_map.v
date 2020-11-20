module \$_DFFE_PN0P_ (input D, C, R, E, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(E), .ALn(R), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_DFFE_PN1P_ (input D, C, R, E, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(E), .ALn(R), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_SDFFCE_PN0P_ (input D, C, R, E, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(E), .ALn(1'b1), .ADn(1'b0), .SLn(R), .SD(1'b0), .LAT(1'b0), .Q(Q));
endmodule

module \$_SDFFCE_PN1P_ (input D, C, R, E, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(C), .EN(E), .ALn(1'b1), .ADn(1'b0), .SLn(R), .SD(1'b1), .LAT(1'b0), .Q(Q));
endmodule

module \$_DLATCH_PN0_ (input D, R, E, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(E), .EN(1'b1), .ALn(R), .ADn(1'b1), .SLn(1'b1), .SD(1'b0), .LAT(1'b1), .Q(Q));
endmodule

module \$_DLATCH_PN1_ (input D, R, E, output Q);
  SLE _TECHMAP_REPLACE_ (.D(D), .CLK(E), .EN(1'b1), .ALn(R), .ADn(1'b0), .SLn(1'b1), .SD(1'b0), .LAT(1'b1), .Q(Q));
endmodule

`ifndef NO_LUT
module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  (* force_downto *)
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
