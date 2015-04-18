module test(D, C, E, R, Q);
	parameter [0:0] CLKPOL = 0;
	parameter [0:0] ENABLE_EN = 0;
	parameter [0:0] RESET_EN = 0;
	parameter [0:0] RESET_VAL = 0;
	parameter [0:0] RESET_SYN = 0;

	(* gentb_clock *)
	input D, C, E, R;

	output Q;

	wire gated_reset = R & RESET_EN;
	wire gated_enable = E | ~ENABLE_EN;
	reg posedge_q, negedge_q, posedge_sq, negedge_sq;

	always @(posedge C, posedge gated_reset)
		if (gated_reset)
			posedge_q <= RESET_VAL;
		else if (gated_enable)
			posedge_q <= D;

	always @(negedge C, posedge gated_reset)
		if (gated_reset)
			negedge_q <= RESET_VAL;
		else if (gated_enable)
			negedge_q <= D;

	always @(posedge C)
		if (gated_reset)
			posedge_sq <= RESET_VAL;
		else if (gated_enable)
			posedge_sq <= D;

	always @(negedge C)
		if (gated_reset)
			negedge_sq <= RESET_VAL;
		else if (gated_enable)
			negedge_sq <= D;

	assign Q = RESET_SYN ? (CLKPOL ? posedge_sq : negedge_sq) : (CLKPOL ? posedge_q : negedge_q);
endmodule
