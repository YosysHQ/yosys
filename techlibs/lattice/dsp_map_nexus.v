module \$__NX_MUL36X36 (input [35:0] A, input [35:0] B, output [71:0] Y);

	parameter A_WIDTH = 36;
	parameter B_WIDTH = 36;
	parameter Y_WIDTH = 72;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;

	MULT36X36 #(
		.REGINPUTA("BYPASS"),
		.REGINPUTB("BYPASS"),
		.REGOUTPUT("BYPASS")
	) _TECHMAP_REPLACE_ (
		.A(A), .B(B),
		.SIGNEDA(A_SIGNED ? 1'b1 : 1'b0),
		.SIGNEDB(B_SIGNED ? 1'b1 : 1'b0),
		.Z(Y)
	);
endmodule

module \$__NX_MUL36X18 (input [35:0] A, input [17:0] B, output [53:0] Y);

	parameter A_WIDTH = 36;
	parameter B_WIDTH = 18;
	parameter Y_WIDTH = 54;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;

	MULT18X36 #(
		.REGINPUTA("BYPASS"),
		.REGINPUTB("BYPASS"),
		.REGOUTPUT("BYPASS")
	) _TECHMAP_REPLACE_ (
		.A(B), .B(A),
		.SIGNEDA(B_SIGNED ? 1'b1 : 1'b0),
		.SIGNEDB(A_SIGNED ? 1'b1 : 1'b0),
		.Z(Y)
	);
endmodule

module \$__NX_MUL18X18 (input [17:0] A, input [17:0] B, output [35:0] Y);

	parameter A_WIDTH = 18;
	parameter B_WIDTH = 18;
	parameter Y_WIDTH = 36;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;

	MULT18X18 #(
		.REGINPUTA("BYPASS"),
		.REGINPUTB("BYPASS"),
		.REGOUTPUT("BYPASS")
	) _TECHMAP_REPLACE_ (
		.A(A), .B(B),
		.SIGNEDA(A_SIGNED ? 1'b1 : 1'b0),
		.SIGNEDB(B_SIGNED ? 1'b1 : 1'b0),
		.Z(Y)
	);
endmodule

module \$__NX_MUL9X9 (input [8:0] A, input [8:0] B, output [17:0] Y);

	parameter A_WIDTH = 9;
	parameter B_WIDTH = 9;
	parameter Y_WIDTH = 18;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;

	MULT9X9 #(
		.REGINPUTA("BYPASS"),
		.REGINPUTB("BYPASS"),
		.REGOUTPUT("BYPASS")
	) _TECHMAP_REPLACE_ (
		.A(A), .B(B),
		.SIGNEDA(A_SIGNED ? 1'b1 : 1'b0),
		.SIGNEDB(B_SIGNED ? 1'b1 : 1'b0),
		.Z(Y)
	);
endmodule
