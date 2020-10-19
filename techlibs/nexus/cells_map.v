// Flipflop intermediate map level
module \$__FF_NOLSR (input D, C, E, output Q);
	parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
	wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
	generate
		if (_TECHMAP_WIREINIT_Q_ === 1'b1)
			FD1P3JX #(.GSR("DISABLED")) _TECHMAP_REPLACE_ (.D(D), .CK(C), .SP(E), .PD(1'b0), .Q(Q));
		else
			FD1P3IX #(.GSR("DISABLED")) _TECHMAP_REPLACE_ (.D(D), .CK(C), .SP(E), .CD(1'b0), .Q(Q));
	endgenerate
endmodule

module \$__FF_SYNCLSR (input D, C, E, R, output Q);
	parameter SR_VAL = 1'b0;
	parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
	wire _TECHMAP_REMOVEINIT_Q_ = 1'b1;
	wire Ci, Ei, Ri, Rg, Dd;
	generate
		if (SR_VAL)
			FD1P3JX #(.GSR("DISABLED")) _TECHMAP_REPLACE_ (.D(D), .CK(C), .SP(E), .PD(R), .Q(Q));
		else
			FD1P3IX #(.GSR("DISABLED")) _TECHMAP_REPLACE_ (.D(D), .CK(C), .SP(E), .CD(R), .Q(Q));
	endgenerate
endmodule

module \$__FF_ASYNCLSR (input D, C, E, R, output Q);
	parameter SR_VAL = 1'b0;
	parameter _TECHMAP_WIREINIT_Q_ = 1'bx;
	wire _TECHMAP_REMOVEINIT_Q_ = (_TECHMAP_WIREINIT_Q_ === 1'bx || _TECHMAP_WIREINIT_Q_ === SR_VAL);
	wire Ci, Ei, Ri, Rg, Dd;
	generate
		if (SR_VAL)
			FD1P3BX #(.GSR("DISABLED")) _TECHMAP_REPLACE_ (.D(D), .CK(C), .SP(E), .PD(R), .Q(Q));
		else
			FD1P3DX #(.GSR("DISABLED")) _TECHMAP_REPLACE_ (.D(D), .CK(C), .SP(E), .CD(R), .Q(Q));
	endgenerate
endmodule


module  \$_DFF_P_ (input D, C, output Q); \$__FF_NOLSR _TECHMAP_REPLACE_ (.D(D), .C(C), .E(1'b1), .Q(Q)); endmodule

module  \$_DFFE_PP_ (input D, C, E, output Q); \$__FF_NOLSR _TECHMAP_REPLACE_ (.D(D), .C(C), .E(E), .Q(Q)); endmodule

module  \$_DFF_PP0_ (input D, C, R, output Q); \$__FF_ASYNCLSR #(0)  _TECHMAP_REPLACE_ (.D(D), .C(C), .R(R), .E(1'b1), .Q(Q)); endmodule
module  \$_DFF_PP1_ (input D, C, R, output Q); \$__FF_ASYNCLSR #(1)  _TECHMAP_REPLACE_ (.D(D), .C(C), .R(R), .E(1'b1), .Q(Q)); endmodule

module  \$_SDFF_PP0_ (input D, C, R, output Q); \$__FF_SYNCLSR #(0)  _TECHMAP_REPLACE_ (.D(D), .C(C), .R(R), .E(1'b1), .Q(Q)); endmodule
module  \$_SDFF_PP1_ (input D, C, R, output Q); \$__FF_SYNCLSR #(1)  _TECHMAP_REPLACE_ (.D(D), .C(C), .R(R), .E(1'b1), .Q(Q)); endmodule

module  \$_DFFE_PP0P_ (input D, C, E, R, output Q); \$__FF_ASYNCLSR #(0)  _TECHMAP_REPLACE_ (.D(D), .C(C), .R(R), .E(E), .Q(Q)); endmodule
module  \$_DFFE_PP1P_ (input D, C, E, R, output Q); \$__FF_ASYNCLSR #(1)  _TECHMAP_REPLACE_ (.D(D), .C(C), .R(R), .E(E), .Q(Q)); endmodule

module  \$_SDFFE_PP0P_ (input D, C, E, R, output Q); \$__FF_SYNCLSR #(0)  _TECHMAP_REPLACE_ (.D(D), .C(C), .R(R), .E(E), .Q(Q)); endmodule
module  \$_SDFFE_PP1P_ (input D, C, E, R, output Q); \$__FF_SYNCLSR #(1)  _TECHMAP_REPLACE_ (.D(D), .C(C), .R(R), .E(E), .Q(Q)); endmodule

module \$__NX_TINOUTPAD (input I, OE, output O, inout B);
	BB _TECHMAP_REPLACE_ (.I(I), .O(O), .T(~OE), .B(B));
endmodule

module \$__NX_TOUTPAD (input I, OE, output O);
	OBZ _TECHMAP_REPLACE_ (.I(I), .O(), .T(~OE), .O(O));
endmodule

`ifndef NO_LUT
module \$lut (A, Y);
	parameter WIDTH = 0;
	parameter LUT = 0;

	input [WIDTH-1:0] A;
	output Y;

	generate
		if (WIDTH == 1) begin
			if (LUT == 2'b01)
				INV _TECHMAP_REPLACE_ (.A(A[0]), .Z(Y));
			else
				LUT4 #(.INIT($sformatf("0x%04x", {{8{LUT[1]}}, {8{LUT[0]}}}))) _TECHMAP_REPLACE_ (.Z(Y),
					.D(A[0]));
		end else
		if (WIDTH == 2) begin
			localparam [15:0] INIT = {{4{LUT[3]}}, {4{LUT[2]}}, {4{LUT[1]}}, {4{LUT[0]}}};
			LUT4 #(.INIT($sformatf("0x%04x",  INIT))) _TECHMAP_REPLACE_ (.Z(Y),
				.C(A[0]), .D(A[1]));
		end else
		if (WIDTH == 3) begin
			localparam [15:0] INIT = {{2{LUT[7]}}, {2{LUT[6]}}, {2{LUT[5]}}, {2{LUT[4]}}, {2{LUT[3]}}, {2{LUT[2]}}, {2{LUT[1]}}, {2{LUT[0]}}};
			LUT4 #(.INIT($sformatf("0x%04x", INIT))) _TECHMAP_REPLACE_ (.Z(Y),
				.B(A[0]), .C(A[1]), .D(A[2]));
		end else
		if (WIDTH == 4) begin
			LUT4 #(.INIT($sformatf("0x%04x", LUT))) _TECHMAP_REPLACE_ (.Z(Y),
				.A(A[0]), .B(A[1]), .C(A[2]), .D(A[3]));
		end else
		if (WIDTH == 5) begin
			WIDEFN9 #(
				.INIT0($sformatf("0x%04x", LUT[15:0 ])),
				.INIT1($sformatf("0x%04x", LUT[31:16])),
			) _TECHMAP_REPLACE_ (
				.A0(A[0]), .B0(A[1]), .C0(A[2]), .D0(A[3]),
				.A1(A[0]), .B1(A[1]), .C1(A[2]), .D1(A[3]),
				.SEL(A[4]), .Z(Y)
			);
		end
	endgenerate
endmodule
`endif
