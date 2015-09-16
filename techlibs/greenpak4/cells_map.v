module  \$_DFF_P_ (input D, C, output Q);
	DFF _TECHMAP_REPLACE_ (
		.D(D),
		.Q(Q),
		.CLK(C),
		.nRSTZ(1'b1),
		.nSETZ(1'b1)
	);
endmodule

module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
      LUT2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
      	.IN0(A[0]), .IN1(1'b0));
    end else
    if (WIDTH == 2) begin
      LUT2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
      	.IN0(A[0]), .IN1(A[1]));
    end else
    if (WIDTH == 3) begin
      LUT3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
      	.IN0(A[0]), .IN1(A[1]), .IN2(A[2]));
    end else
    if (WIDTH == 4) begin
      LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
      	.IN0(A[0]), .IN1(A[1]), .IN2(A[2]), .IN3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
