module FTCP (C, PRE, CLR, T, Q);
	input C, PRE, CLR, T;
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
		.S(PRE),
		.R(CLR),
	);
endmodule

module FTCP_N (C, PRE, CLR, T, Q);
	input C, PRE, CLR, T;
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
		.S(PRE),
		.R(CLR),
	);
endmodule
