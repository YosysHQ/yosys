(* abc9_box, lib_whitebox *)
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
`ifdef ICE40_HX
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L79
		(CI => CO) = (126, 105);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L80
		(I0 => O) = (449, 386);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L82
		(A => CO) = (259, 245);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L83
		(A => O) = (400, 379);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L85
		(B => CO) = (231, 133);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L86
		(B => O) = (379, 351);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_hx1k.txt#L88
		(I3 => O) = (316, 288);
		(CI => O) = (316, 288);
	endspecify
`endif
`ifdef ICE40_LP
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L79
		(CI => CO) = (186, 155);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L80
		(I0 => O) = (662, 569);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L82
		(A => CO) = (382, 362);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L83
		(A => O) = (589, 558);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L85
		(B => CO) = (341, 196);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L86
		(B => O) = (558, 517);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_lp1k.txt#L88
		(I3 => O) = (465, 423);
		(CI => O) = (465, 423);
	endspecify
`endif
`ifdef ICE40_U
	specify
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L91
		(CI => CO) = (278, 278);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L92
		(I0 => O) = (1245, 1285);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L94
		(A => CO) = (675, 662);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L95
		(A => O) = (1179, 1232);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L97
		(B => CO) = (609, 358);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L98
		(B => O) = (1179, 1205);
		// https://github.com/YosysHQ/icestorm/blob/be0bca0230d6fe1102e0a360b953fbb0d273a39f/icefuzz/timings_up5k.txt#L100
		(I3 => O) = (861, 874);
		(CI => O) = (861, 874);
	endspecify
`endif
endmodule
