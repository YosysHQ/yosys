`default_nettype none
// MUXes do not have separate inputs so you cannot wire from one LUT to two MUX inputs.
// equal mux inputs
module MUX2_LUT5_A_A(
	output wire O,
	input wire I,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(I),
		.I1(I),
		.O(O),
		.S0(S0));
endmodule


