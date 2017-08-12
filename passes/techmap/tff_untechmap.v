module __TFF_PP0_ALWAYS (C, R, Q);
	input C, R;
	output wire Q;

	wire invout;

	$_NOT_ inv (
		.A(Q),
		.Y(invout),
	);

	$_DFF_PP0_ dff (
		.C(C),
		.D(invout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFF_PP0_ALWAYS_CINV (C, R, Q);
	input C, R;
	output wire Q;

	wire ffout;

	$_NOT_ inv (
		.A(ffout),
		.Y(Q),
	);

	$_DFF_PP0_ dff (
		.C(C),
		.D(D),
		.Q(ffout),
		.R(R),
	);
endmodule

module __TFF_P_ALWAYS_ (C, Q);
	input C;
	output wire Q;

	wire notout;

	$_NOT_ notgate (
		.A(Q),
		.Y(notout),
	);

	$_DFF_P_ dff (
		.C(C),
		.D(notout),
		.Q(Q),
	);
endmodule

module __TFF_N_ALWAYS_ (C, Q);
	input C;
	output wire Q;

	wire notout;

	$_NOT_ notgate (
		.A(Q),
		.Y(notout),
	);

	$_DFF_N_ dff (
		.C(C),
		.D(notout),
		.Q(Q),
	);
endmodule

module __TFF_N_ (T, C, Q);
	input T, C;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_N_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
	);
endmodule

module __TFF_P_ (T, C, Q);
	input T, C;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_P_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
	);
endmodule

module __TFFE_NN_ (T, C, E, Q);
	input T, C, E;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFE_NN_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.E(E),
	);
endmodule

module __TFFE_NP_ (T, C, E, Q);
	input T, C, E;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFE_NP_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.E(E),
	);
endmodule

module __TFFE_PN_ (T, C, E, Q);
	input T, C, E;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFE_PN_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.E(E),
	);
endmodule

module __TFFE_PP_ (T, C, E, Q);
	input T, C, E;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFE_PP_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.E(E),
	);
endmodule

module __TFF_NN0_ (T, C, R, Q);
	input T, C, R;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_NN0_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFF_NN1_ (T, C, R, Q);
	input T, C, R;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_NN1_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFF_NP0_ (T, C, R, Q);
	input T, C, R;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_NP0_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFF_NP1_ (T, C, R, Q);
	input T, C, R;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_NP1_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFF_PN0_ (T, C, R, Q);
	input T, C, R;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_PN0_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFF_PN1_ (T, C, R, Q);
	input T, C, R;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_PN1_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFF_PP0_ (T, C, R, Q);
	input T, C, R;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_PP0_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFF_PP1_ (T, C, R, Q);
	input T, C, R;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFF_PP1_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.R(R),
	);
endmodule

module __TFFSR_NNN_ (C, S, R, T, Q);
	input C, S, R, T;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFSR_NNN_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.S(S),
		.R(R),
	);
endmodule

module __TFFSR_NNP_ (C, S, R, T, Q);
	input C, S, R, T;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFSR_NNP_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.S(S),
		.R(R),
	);
endmodule

module __TFFSR_NPN_ (C, S, R, T, Q);
	input C, S, R, T;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFSR_NPN_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.S(S),
		.R(R),
	);
endmodule

module __TFFSR_NPP_ (C, S, R, T, Q);
	input C, S, R, T;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFSR_NPP_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.S(S),
		.R(R),
	);
endmodule

module __TFFSR_PNN_ (C, S, R, T, Q);
	input C, S, R, T;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFSR_PNN_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.S(S),
		.R(R),
	);
endmodule

module __TFFSR_PNP_ (C, S, R, T, Q);
	input C, S, R, T;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFSR_PNP_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.S(S),
		.R(R),
	);
endmodule

module __TFFSR_PPN_ (C, S, R, T, Q);
	input C, S, R, T;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFSR_PPN_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.S(S),
		.R(R),
	);
endmodule

module __TFFSR_PPP_ (C, S, R, T, Q);
	input C, S, R, T;
	output wire Q;

	wire xorout;

	$_XOR_ xorgate (
		.A(T),
		.B(Q),
		.Y(xorout),
	);

	$_DFFSR_PPP_ dff (
		.C(C),
		.D(xorout),
		.Q(Q),
		.S(S),
		.R(R),
	);
endmodule
