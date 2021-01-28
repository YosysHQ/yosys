module top(
	IDENT_V_,
	IDENT_W_,
	IDENT_X_,
	IDENT_Y_,
	IDENT_Z_,
	IDENT_A_,
	IDENT_B_,
	IDENT_C_
);
	`define MACRO(dummy, x) IDENT_``x``_
	output wire IDENT_V_;
	output wire `MACRO(_,W);
	output wire `MACRO(_, X);
	output wire `MACRO(_,Y );
	output wire `MACRO(_, Z );
	output wire `MACRO(_,	 A);
	output wire `MACRO(_,B	 );
	output wire `MACRO(_, C	);
endmodule
