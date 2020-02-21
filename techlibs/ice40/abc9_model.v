(* abc9_box_id = 1, lib_whitebox *)
module \$__ICE40_CARRY_WRAPPER (
	(* abc9_carry *)
	output CO,
	output O,
	input A, B,
	(* abc9_carry *)
	input CI,
	input I0, I3
);
	parameter LUT = 0;
	parameter I3_IS_CI = 0;
	wire I3_OR_CI = I3_IS_CI ? CI : I3;
	SB_CARRY carry (
		.I0(A),
		.I1(B),
		.CI(CI),
		.CO(CO)
	);
	SB_LUT4 #(
		.LUT_INIT(LUT)
	) adder (
		.I0(I0),
		.I1(A),
		.I2(B),
		.I3(I3_OR_CI),
		.O(O)
	);
endmodule
