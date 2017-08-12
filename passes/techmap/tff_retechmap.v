module __TFF_PP0_ALWAYS (C, R, Q);
	input C, R;
	output wire Q;

	__TFF_PP0_ TECHMAP_REPLACE_(
		.C(C),
		.R(R),
		.Q(Q),
		.T(1'b1)
	);

endmodule

module __TFF_PP0_ALWAYS_CINV (C, R, Q);
	input C, R;
	output wire Q;

	__TFF_PP0_ TECHMAP_REPLACE_(
		.C(C),
		.R(R),
		.Q(Q),
		.T(1'b1)
	);

endmodule
