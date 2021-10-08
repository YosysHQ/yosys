// turn 0 and 1 into LUTs

// Form the initialized LUTs and keep them.
module MUX2_LUT5_ZERO_0(
	input wire I1,
	output wire O,
	input wire S0);

	wire luxout;

	MUX2_LUT5 int_mux(
		.I0(luxout),
		.I1(I1),
		.O(O),
		.S0(S0));

	(* keep *)
	LUT4 #(.INIT(16'h0)) int_lut (
		.F(luxout));
endmodule

module MUX2_LUT5_ZERO_1(
	input wire I0,
	output wire O,
	input wire S0);

	wire luxout;

	MUX2_LUT5 int_mux(
		.I0(I0),
		.I1(luxout),
		.O(O),
		.S0(S0));

	(* keep *)
	LUT4 #(.INIT(16'h0)) int_lut (
		.F(luxout));
endmodule

module MUX2_LUT5_ONE_0(
	input wire I1,
	output wire O,
	input wire S0);

	wire luxout;

	MUX2_LUT5 int_mux(
		.I0(luxout),
		.I1(I1),
		.O(O),
		.S0(S0));

	(* keep *)
	LUT4 #(.INIT(16'hffff)) int_lut (
		.F(luxout));
endmodule

module MUX2_LUT5_ONE_1(
	input wire I0,
	output wire O,
	input wire S0);

	wire luxout;

	MUX2_LUT5 int_mux(
		.I0(I0),
		.I1(luxout),
		.O(O),
		.S0(S0));

	(* keep *)
	LUT4 #(.INIT(16'hffff)) int_lut (
		.F(luxout));
endmodule


// When duplicating inputs we use only one LUT and 
// use the fact that by default S0 == 1, so we free up the second input LUT.
module MUX2_LUT5_ZERO_ZERO(
	output wire O,
	input wire S0);

	wire luxout;

	(* SINGLE_INPUT_MUX *)
	MUX2_LUT5 int_mux(
		.I1(luxout),
		.O(O));

	(* keep *)
	LUT4 #(.INIT(16'h0)) int_lut (
		.F(luxout));
endmodule

module MUX2_LUT5_ONE_ONE(
	output wire O,
	input wire S0);

	wire luxout;

	(* SINGLE_INPUT_MUX *)
	MUX2_LUT5 int_mux(
		.I1(luxout),
		.O(O));

	(* keep *)
	LUT4 #(.INIT(16'hffff)) int_lut (
		.F(luxout));
endmodule

module MUX2_LUT5_A_A(
	input wire I,
	output wire O);

	wire luxout;

	(* SINGLE_INPUT_MUX *)
	MUX2_LUT5 int_mux(
		.I1(I),
		.O(O));
endmodule
