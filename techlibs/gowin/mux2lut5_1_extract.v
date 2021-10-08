`default_nettype none

// One of the mux inputs is constant 0 or 1
// hw MUXes do not have their own inputs, you need a LUT. 
// Making pass-through LUTs for VCC and GND is not very economical: 
// it wastes resources on routing, so here such nets are identified 
// and saved to be replaced by initialized LUTs in the future.
// MUX2 with I0 == 0
module MUX2_LUT5_ZERO_0(
	input wire I1,
	output wire O,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(1'b0),
		.I1(I1),
		.O(O),
		.S0(S0));
endmodule

// MUX2 with I1 == 0
module MUX2_LUT5_ZERO_1(
	input wire I0,
	output wire O,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(I0),
		.I1(1'b0),
		.O(O),
		.S0(S0));
endmodule

// MUX2 with I0 == 1
module MUX2_LUT5_ONE_0(
	input wire I1,
	output wire O,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(1'b1),
		.I1(I1),
		.O(O),
		.S0(S0));
endmodule

// MUX2 with I1 == 1
module MUX2_LUT5_ONE_1(
	input wire I0,
	output wire O,
	input wire S0);

	MUX2_LUT5 mux(
		.I0(I0),
		.I1(1'b1),
		.O(O),
		.S0(S0));
endmodule

