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

module \$__NX_MAC18X18 (input [17:0] A, input [17:0] B, input [47:0] C, output [53:0] Y);

	parameter A_WIDTH = 18;
	parameter B_WIDTH = 18;
	parameter C_WIDTH = 48;
	parameter Y_WIDTH = 48;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter SUBTRACT = 0;

	MULTADDSUB18X18 #(
		.REGINPUTA("BYPASS"),
		.REGINPUTB("BYPASS"),
		.REGINPUTC("BYPASS"),
		.REGOUTPUT("BYPASS")
	) _TECHMAP_REPLACE_ (
		.A(A), 
		.B(B), 
		.C({6'b0, C}),
		.SIGNED(A_SIGNED ? 1'b1 : 1'b0), 
		.ADDSUB(SUBTRACT ? 1'b1 : 1'b0),
		.Z(Y)
	);
endmodule

module \$__NX_PREADD18X18 (input [17:0] A, input [17:0] B, input [17:0] C, input CLK, output [35:0] Y);

	parameter PIPELINED = 0;
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter C_SIGNED = 0;

	MULTPREADD18X18 #(
		.REGINPUTA("BYPASS"),
		.REGINPUTB("BYPASS"),
		.REGINPUTC("BYPASS"),
		.REGOUTPUT(PIPELINED ? "REGISTER" : "BYPASS")
	) _TECHMAP_REPLACE_ (
		.A(A),
		.B(B),
		.C(C),
		.CLK(CLK),
		.SIGNEDA(A_SIGNED ? 1'b1 : 1'b0),
		.SIGNEDB(B_SIGNED ? 1'b1 : 1'b0),
		.SIGNEDC(C_SIGNED ? 1'b1 : 1'b0),
		.Z(Y)
	);
endmodule

module \$__NX_MAC9X9WIDE_4LANE (input [8:0] A0, B0, A1, B1, A2, B2, A3, B3, output [53:0] Y);

	parameter SIGNED = 0;

	MULTADDSUB9X9WIDE #(
		.REGINPUTAB0("BYPASS"),
		.REGINPUTAB1("BYPASS"),
		.REGINPUTAB2("BYPASS"),
		.REGINPUTAB3("BYPASS"),
		.REGINPUTC("BYPASS"),
		.REGOUTPUT("BYPASS")
	) _TECHMAP_REPLACE_ (
		.A0(A0), .B0(B0),
		.A1(A1), .B1(B1),
		.A2(A2), .B2(B2),
		.A3(A3), .B3(B3),
		.C(54'b0),
		.SIGNED(SIGNED ? 1'b1 : 1'b0),
		.ADDSUB(4'b0000),
		.Z(Y)
	);
endmodule
