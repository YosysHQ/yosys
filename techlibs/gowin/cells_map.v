`default_nettype none
//All DFF* have INIT, but the hardware is always initialised to the reset
//value regardless. The parameter is ignored.

// DFFN			 D Flip-Flop with Negative-Edge Clock
module	\$_DFF_N_ (input D, C, output Q);
	DFFN _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFF			 D Flip-Flop
module	\$_DFF_P_ (input D, C, output Q);
	DFF _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFE			 D Flip-Flop with Clock Enable
module	\$_DFFE_PP_ (input D, C, E, output Q);
	DFFE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNE		 D Flip-Flop with Negative-Edge Clock and Clock Enable
module	\$_DFFE_NP_ (input D, C, E, output Q);
	DFFNE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFR			 D Flip-Flop with Synchronous Reset
module	\$_SDFF_PP0_ (input D, C, R, output Q);
	DFFR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNR		 D Flip-Flop with Negative-Edge Clock and Synchronous Reset
module	\$_SDFF_NP0_ (input D, C, R, output Q);
	DFFNR _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFRE		 D Flip-Flop with Clock Enable and Synchronous Reset
module	\$_SDFFE_PP0P_ (input D, C, R, E, output Q);
	DFFRE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNRE		 D Flip-Flop with Negative-Edge Clock,Clock Enable, and Synchronous Reset
module	\$_SDFFE_NP0P_ (input D, C, R, E, output Q);
	DFFNRE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .RESET(R), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFS			 D Flip-Flop with Synchronous Set
module	\$_SDFF_PP1_ (input D, C, R, output Q);
	DFFS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNS		 D Flip-Flop with Negative-Edge Clock and Synchronous Set
module	\$_SDFF_NP1_ (input D, C, R, output Q);
	DFFNS _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFSE		 D Flip-Flop with Clock Enable and Synchronous Set
module	\$_SDFFE_PP1P_ (input D, C, R, E, output Q);
	DFFSE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(R), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNSE		 D Flip-Flop with Negative-Edge Clock,Clock Enable,and Synchronous Set
module	\$_SDFFE_NP1P_ (input D, C, R, E, output Q);
	DFFNSE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .SET(R), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFP			 D Flip-Flop with Asynchronous Preset
module	\$_DFF_PP1_ (input D, C, R, output Q);
	DFFP _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNP		 D Flip-Flop with Negative-Edge Clock and Asynchronous Preset
module	\$_DFF_NP1_ (input D, C, R, output Q);
	DFFNP _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFC			 D Flip-Flop with Asynchronous Clear
module	\$_DFF_PP0_ (input D, C, R, output Q);
	DFFC _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNC		 D Flip-Flop with Negative-Edge Clock and Asynchronous Clear
module	\$_DFF_NP0_ (input D, C, R, output Q);
	DFFNC _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(R));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFPE		 D Flip-Flop with Clock Enable and Asynchronous Preset
module	\$_DFFE_PP1P_ (input D, C, R, E, output Q);
	DFFPE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(R), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNPE		 D Flip-Flop with Negative-Edge Clock,Clock Enable, and Asynchronous Preset
module	\$_DFFE_NP1P_ (input D, C, R, E, output Q);
	DFFNPE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .PRESET(R), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFCE		 D Flip-Flop with Clock Enable and Asynchronous Clear
module	\$_DFFE_PP0P_ (input D, C, R, E, output Q);
	DFFCE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(R), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

// DFFNCE		 D Flip-Flop with Negative-Edge Clock,Clock Enable and Asynchronous Clear
module	\$_DFFE_NP0P_ (input D, C, R, E, output Q);
	DFFNCE _TECHMAP_REPLACE_ (.D(D), .Q(Q), .CLK(C), .CLEAR(R), .CE(E));
	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule


module \$lut (A, Y);
	parameter WIDTH = 0;
	parameter LUT = 0;

	(* force_downto *)
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
		end else
		if (WIDTH == 5) begin
			wire f0, f1;
			\$lut #(.LUT(LUT[15: 0]), .WIDTH(4)) lut0 (.A(A[3:0]), .Y(f0));
			\$lut #(.LUT(LUT[31:16]), .WIDTH(4)) lut1 (.A(A[3:0]), .Y(f1));
			MUX2_LUT5 mux5(.I0(f0), .I1(f1), .S0(A[4]), .O(Y));
		end else
		if (WIDTH == 6) begin
			wire f0, f1;
			\$lut #(.LUT(LUT[31: 0]), .WIDTH(5)) lut0 (.A(A[4:0]), .Y(f0));
			\$lut #(.LUT(LUT[63:32]), .WIDTH(5)) lut1 (.A(A[4:0]), .Y(f1));
			MUX2_LUT6 mux6(.I0(f0), .I1(f1), .S0(A[5]), .O(Y));
		end else
		if (WIDTH == 7) begin
			wire f0, f1;
			\$lut #(.LUT(LUT[63: 0]), .WIDTH(6)) lut0 (.A(A[5:0]), .Y(f0));
			\$lut #(.LUT(LUT[127:64]), .WIDTH(6)) lut1 (.A(A[5:0]), .Y(f1));
			MUX2_LUT7 mux7(.I0(f0), .I1(f1), .S0(A[6]), .O(Y));
		end else
		if (WIDTH == 8) begin
			wire f0, f1;
			\$lut #(.LUT(LUT[127: 0]), .WIDTH(7)) lut0 (.A(A[6:0]), .Y(f0));
			\$lut #(.LUT(LUT[255:128]), .WIDTH(7)) lut1 (.A(A[6:0]), .Y(f1));
			MUX2_LUT8 mux8(.I0(f0), .I1(f1), .S0(A[7]), .O(Y));
		end else begin
			wire _TECHMAP_FAIL_ = 1;
		end
	endgenerate
endmodule
