module \$__MUL9X9 (input [8:0] A, input [8:0] B, output [17:0] Y);
	parameter A_WIDTH = 9;
	parameter B_WIDTH = 9;
	parameter Y_WIDTH = 18;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;

	wire [8:0] soa;
	wire [8:0] sob;

	MULT9X9 _TECHMAP_REPLACE_ (
		.A(A),
		.B(B),
		.SIA(8'b0),
		.SIB(8'b0),
		.ASIGN(A_SIGNED),
		.BSIGN(B_SIGNED),
		.ASEL(1'b0),
		.BSEL(1'b0),
		.SOA(soa),
		.SOB(sob),
		.DOUT(Y)
	);
endmodule

module \$__MUL18X18 (input [17:0] A, input [17:0] B, output [35:0] Y);
	parameter A_WIDTH = 18;
	parameter B_WIDTH = 18;
	parameter Y_WIDTH = 36;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;

	wire [17:0] soa;
	wire [17:0] sob;

	MULT18X18 _TECHMAP_REPLACE_ (
		.A(A),
		.B(B),
		.SIA(18'b0),
		.SIB(18'b0),
		.ASIGN(A_SIGNED),
		.BSIGN(B_SIGNED),
		.ASEL(1'b0),
		.BSEL(1'b0),
		.SOA(soa),
		.SOB(sob),
		.DOUT(Y)
	);
endmodule

module \$__MUL36X36 (input [35:0] A, input [35:0] B, output [71:0] Y);
	parameter A_WIDTH = 36;
	parameter B_WIDTH = 36;
	parameter Y_WIDTH = 72;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;

	MULT36X36 _TECHMAP_REPLACE_ (
		.A(A),
		.B(B),
		.ASIGN(A_SIGNED),
		.BSIGN(B_SIGNED),
		.DOUT(Y)
	);
endmodule
