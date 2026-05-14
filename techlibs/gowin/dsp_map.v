module \$__MUL9X9 (input [8:0] A, input [8:0] B, output [17:0] Y);

    parameter A_WIDTH = 9;
    parameter B_WIDTH = 9;
    parameter Y_WIDTH = 18;
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;

	MULT9X9 __TECHMAP_REPLACE__ (
		.CLK(1'b0),
		.CE(1'b0),
		.RESET(1'b0),
		.A(A),
		.SIA({A_WIDTH{1'b0}}),
		.ASEL(1'b0),
		.ASIGN(A_SIGNED ? 1'b1 : 1'b0),
		.B(B),
		.SIB({B_WIDTH{1'b0}}),
		.BSEL(1'b0),
		.BSIGN(B_SIGNED ? 1'b1 : 1'b0),
		.DOUT(Y)
	);

endmodule

module \$__MUL18X18 (input [17:0] A, input [17:0] B, output [35:0] Y);

    parameter A_WIDTH = 18;
    parameter B_WIDTH = 18;
    parameter Y_WIDTH = 36;
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;

	MULT18X18 __TECHMAP_REPLACE__ (
		.CLK(1'b0),
		.CE(1'b0),
		.RESET(1'b0),
		.A(A),
		.SIA({A_WIDTH{1'b0}}),
		.ASEL(1'b0),
		.ASIGN(A_SIGNED ? 1'b1 : 1'b0),
		.B(B),
		.SIB({B_WIDTH{1'b0}}),
		.BSEL(1'b0),
		.BSIGN(B_SIGNED ? 1'b1 : 1'b0),
		.DOUT(Y)
	);

endmodule

module \$__MUL36X36 (input [35:0] A, input [35:0] B, output [71:0] Y);

    parameter A_WIDTH = 36;
    parameter B_WIDTH = 36;
    parameter Y_WIDTH = 72;
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;

	MULT36X36 __TECHMAP_REPLACE__ (
		.CLK(1'b0),
		.RESET(1'b0),
		.CE(1'b0),
		.A(A),
		.ASIGN(A_SIGNED ? 1'b1 : 1'b0),
		.B(B),
		.BSIGN(B_SIGNED ? 1'b1 : 1'b0),
		.DOUT(Y)
	);

endmodule
