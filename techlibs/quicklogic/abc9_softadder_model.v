(* abc9_box, lib_whitebox *)
module soft_adder (
	(* abc9_carry *)
	output CO,
	output O,
	input A, B,
	(* abc9_carry *)
	input CI,
	input I2, I3
);
	parameter LUT = 0;
	parameter I2_IS_CI = 0;
	wire I2_OR_CI = I2_IS_CI ? CI : I2;
	carry_follower carry (
		.A(A),
		.B(B),
		.CI(CI),
		.CO(CO)
	);
	LUT4 #(
		.INIT(LUT)
	) adder (
		.I0(A),
		.I1(B),
		.I2(I2_OR_CI),
		.I3(I3),
		.O(O)
	);
endmodule
