module  \$_DFF_N_ (input D, C, output Q); EFX_FF #(.CLK_POLARITY(1'b0), .CE_POLARITY(1'b1), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b1), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(1'b0), .Q(Q)); endmodule
module  \$_DFF_P_ (input D, C, output Q); EFX_FF #(.CLK_POLARITY(1'b1), .CE_POLARITY(1'b1), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b1), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(1'b0), .Q(Q)); endmodule

module  \$_DFFE_NN_ (input D, C, E, output Q); EFX_FF #(.CLK_POLARITY(1'b0), .CE_POLARITY(1'b0), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b1), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(E), .CLK(C), .SR(1'b0), .Q(Q)); endmodule
module  \$_DFFE_NP_ (input D, C, E, output Q); EFX_FF #(.CLK_POLARITY(1'b0), .CE_POLARITY(1'b1), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b1), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(E), .CLK(C), .SR(1'b0), .Q(Q)); endmodule

module  \$_DFFE_PN_ (input D, C, E, output Q); EFX_FF #(.CLK_POLARITY(1'b1), .CE_POLARITY(1'b0), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b1), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(E), .CLK(C), .SR(1'b0), .Q(Q)); endmodule
module  \$_DFFE_PP_ (input D, C, E, output Q); EFX_FF #(.CLK_POLARITY(1'b1), .CE_POLARITY(1'b1), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b1), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(E), .CLK(C), .SR(1'b0), .Q(Q)); endmodule

module  \$_DFF_NN0_ (input D, C, R, output Q); EFX_FF #(.CLK_POLARITY(1'b0), .CE_POLARITY(1'b1), .SR_POLARITY(1'b0), .D_POLARITY(1'b1), .SR_SYNC(1'b0), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(R), .Q(Q)); endmodule
module  \$_DFF_NN1_ (input D, C, R, output Q); EFX_FF #(.CLK_POLARITY(1'b0), .CE_POLARITY(1'b1), .SR_POLARITY(1'b0), .D_POLARITY(1'b1), .SR_SYNC(1'b0), .SR_VALUE(1'b1), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(R), .Q(Q)); endmodule
module  \$_DFF_PN0_ (input D, C, R, output Q); EFX_FF #(.CLK_POLARITY(1'b1), .CE_POLARITY(1'b1), .SR_POLARITY(1'b0), .D_POLARITY(1'b1), .SR_SYNC(1'b0), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(R), .Q(Q)); endmodule
module  \$_DFF_PN1_ (input D, C, R, output Q); EFX_FF #(.CLK_POLARITY(1'b1), .CE_POLARITY(1'b1), .SR_POLARITY(1'b0), .D_POLARITY(1'b1), .SR_SYNC(1'b0), .SR_VALUE(1'b1), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(R), .Q(Q)); endmodule

module  \$_DFF_NP0_ (input D, C, R, output Q); EFX_FF #(.CLK_POLARITY(1'b0), .CE_POLARITY(1'b1), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b0), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(R), .Q(Q)); endmodule
module  \$_DFF_NP1_ (input D, C, R, output Q); EFX_FF #(.CLK_POLARITY(1'b0), .CE_POLARITY(1'b1), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b0), .SR_VALUE(1'b1), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(R), .Q(Q)); endmodule
module  \$_DFF_PP0_ (input D, C, R, output Q); EFX_FF #(.CLK_POLARITY(1'b1), .CE_POLARITY(1'b1), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b0), .SR_VALUE(1'b0), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(R), .Q(Q)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); EFX_FF #(.CLK_POLARITY(1'b1), .CE_POLARITY(1'b1), .SR_POLARITY(1'b1), .D_POLARITY(1'b1), .SR_SYNC(1'b0), .SR_VALUE(1'b1), .SR_SYNC_PRIORITY(1'b1)) _TECHMAP_REPLACE_ (.D(D), .CE(1'b1), .CLK(C), .SR(R), .Q(Q)); endmodule

module \$_DLATCH_N_ (E, D, Q);
  wire [1023:0] _TECHMAP_DO_ = "simplemap; opt";
  input E, D;
  output Q = !E ? D : Q;
endmodule

module \$_DLATCH_P_ (E, D, Q);
  wire [1023:0] _TECHMAP_DO_ = "simplemap; opt";
  input E, D;
  output Q = E ? D : Q;
endmodule

`ifndef NO_LUT
module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      EFX_LUT4 #(.LUTMASK(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(1'b0), .I2(1'b0), .I3(1'b0));
    end else
    if (WIDTH == 2) begin
      EFX_LUT4 #(.LUTMASK(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(1'b0), .I3(1'b0));
    end else
    if (WIDTH == 3) begin
      EFX_LUT4 #(.LUTMASK(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(1'b0));
    end else
    if (WIDTH == 4) begin
      EFX_LUT4 #(.LUTMASK(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
`endif
