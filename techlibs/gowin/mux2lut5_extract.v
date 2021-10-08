`default_nettype none
// Both of the mux inputs is constant 0 or 1
// hw MUXes do not have their own inputs, you need a LUT. 
// Making pass-through LUTs for VCC and GND is not very economical: 
// it wastes resources on routing, so here such nets are identified 
// and saved to be replaced by initialized LUTs in the future.

// I0 == I1 == 0
module MUX2_LUT5_ZERO_ZERO(
	output wire O,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(1'b0),
		.I1(1'b0),
		.O(O),
		.S0(S0));
endmodule

// I0 == 0 I1 == 1
module MUX2_LUT5_ZERO_ONE(
	output wire O,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(1'b0),
		.I1(1'b1),
		.O(O),
		.S0(S0));
endmodule

// I0 == 1 I1 == 0
module MUX2_LUT5_ONE_ZERO(
	output wire O,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(1'b1),
		.I1(1'b0),
		.O(O),
		.S0(S0));
endmodule

// I0 == I1 == 1
module MUX2_LUT5_ONE_ONE(
	output wire O,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(1'b1),
		.I1(1'b1),
		.O(O),
		.S0(S0));
endmodule

