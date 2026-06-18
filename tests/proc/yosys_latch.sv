module yosys_latch (
	input logic dlatch_p_d, input logic dlatch_p_g, output logic dlatch_p_q,
	input logic dlatch_n_d, input logic dlatch_n_gn, output logic dlatch_n_q,
	input logic dlatch_pn0_d, input logic dlatch_pn0_rn, input logic dlatch_pn0_g, output logic dlatch_pn0_q,
	input logic dlatch_nn0_d, input logic dlatch_nn0_rn, input logic dlatch_nn0_gn, output logic dlatch_nn0_q
);
	always_latch if (dlatch_p_g) dlatch_p_q <= dlatch_p_d;
	always_latch if (~dlatch_n_gn) dlatch_n_q <= dlatch_n_d;
	always_latch if (~dlatch_pn0_rn) dlatch_pn0_q <= 1'b0; else if (dlatch_pn0_g) dlatch_pn0_q <= dlatch_pn0_d;
	always @* if (dlatch_nn0_rn == 1'b0) dlatch_nn0_q <= 1'b0; else if (dlatch_nn0_gn == 1'b0) dlatch_nn0_q <= dlatch_nn0_d;
endmodule
