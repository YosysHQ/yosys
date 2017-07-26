module $_DLATCH_P_(input E, input D, output Q);
	GP_DLATCH _TECHMAP_REPLACE_ (
		.D(D),
		.nCLK(!E),
		.Q(Q)
		);
endmodule

module $_DLATCH_N_(input E, input D, output Q);
	GP_DLATCH _TECHMAP_REPLACE_ (
		.D(D),
		.nCLK(E),
		.Q(Q)
		);
endmodule
