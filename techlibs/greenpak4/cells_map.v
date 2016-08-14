module GP_DFFS(input D, CLK, nSET, output reg Q);
	parameter [0:0] INIT = 1'bx;
	GP_DFFSR #(
		.INIT(INIT),
		.SRMODE(1'b1),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.CLK(CLK),
		.nSR(nSET),
		.Q(Q)
	);
endmodule

module GP_DFFR(input D, CLK, nRST, output reg Q);
	parameter [0:0] INIT = 1'bx;
	GP_DFFSR #(
		.INIT(INIT),
		.SRMODE(1'b0),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.CLK(CLK),
		.nSR(nRST),
		.Q(Q)
	);
endmodule

module GP_DFFSI(input D, CLK, nSET, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	GP_DFFSRI #(
		.INIT(INIT),
		.SRMODE(1'b1),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.CLK(CLK),
		.nSR(nSET),
		.nQ(nQ)
	);
endmodule

module GP_DFFRI(input D, CLK, nRST, output reg nQ);
	parameter [0:0] INIT = 1'bx;
	GP_DFFSRI #(
		.INIT(INIT),
		.SRMODE(1'b0),
	) _TECHMAP_REPLACE_ (
		.D(D),
		.CLK(CLK),
		.nSR(nRST),
		.nQ(nQ)
	);
endmodule

module GP_OBUFT(input IN, input OE, output OUT);
	GP_IOBUF _TECHMAP_REPLACE_ (
		.IN(IN),
		.OE(OE),
		.IO(OUT),
		.OUT()
	);
endmodule

module \$lut (A, Y);
  parameter WIDTH = 0;
  parameter LUT = 0;

  input [WIDTH-1:0] A;
  output Y;

  generate
    if (WIDTH == 1) begin
		if(LUT == 2'b01) begin
			GP_INV _TECHMAP_REPLACE_ (.OUT(Y), .IN(A[0]) );
		end
		else begin
			GP_2LUT #(.INIT({2'b00, LUT})) _TECHMAP_REPLACE_ (.OUT(Y),
				.IN0(A[0]), .IN1(1'b0));
		end
    end else
    if (WIDTH == 2) begin
      GP_2LUT #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
      	.IN0(A[0]), .IN1(A[1]));
    end else
    if (WIDTH == 3) begin
      GP_3LUT #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
      	.IN0(A[0]), .IN1(A[1]), .IN2(A[2]));
    end else
    if (WIDTH == 4) begin
      GP_4LUT #(.INIT(LUT)) _TECHMAP_REPLACE_ (.OUT(Y),
      	.IN0(A[0]), .IN1(A[1]), .IN2(A[2]), .IN3(A[3]));
    end else begin
      wire _TECHMAP_FAIL_ = 1;
    end
  endgenerate
endmodule
