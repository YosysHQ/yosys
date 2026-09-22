`ifndef CMP_VALUE
`define CMP_VALUE {(LUT_WIDTH/2){2'b10}}
`endif

module top(...);
	parameter LUT_WIDTH = 4; // Multiples of 2 only

	input [LUT_WIDTH-1:0] a;

	output o1_1 = $unsigned(`CMP_VALUE) <= $unsigned(a);
	output o1_2 = $unsigned(`CMP_VALUE) <  $unsigned(a);
	output o1_3 = $unsigned(`CMP_VALUE) >= $unsigned(a);
	output o1_4 = $unsigned(`CMP_VALUE) >  $unsigned(a);
	output o1_5 = $unsigned(`CMP_VALUE) == $unsigned(a);
	output o1_6 = $unsigned(`CMP_VALUE) != $unsigned(a);

	output o2_1 = $unsigned(a) <= $unsigned(`CMP_VALUE);
	output o2_2 = $unsigned(a) <  $unsigned(`CMP_VALUE);
	output o2_3 = $unsigned(a) >= $unsigned(`CMP_VALUE);
	output o2_4 = $unsigned(a) >  $unsigned(`CMP_VALUE);
	output o2_5 = $unsigned(a) == $unsigned(`CMP_VALUE);
	output o2_6 = $unsigned(a) != $unsigned(`CMP_VALUE);

	// ########################

	output o3_1 = $signed(`CMP_VALUE) <= $unsigned(a);
	output o3_2 = $signed(`CMP_VALUE) <  $unsigned(a);
	output o3_3 = $signed(`CMP_VALUE) >= $unsigned(a);
	output o3_4 = $signed(`CMP_VALUE) >  $unsigned(a);
	output o3_5 = $signed(`CMP_VALUE) == $unsigned(a);
	output o3_6 = $signed(`CMP_VALUE) != $unsigned(a);

	output o4_1 = $unsigned(a) <= $signed(`CMP_VALUE);
	output o4_2 = $unsigned(a) <  $signed(`CMP_VALUE);
	output o4_3 = $unsigned(a) >= $signed(`CMP_VALUE);
	output o4_4 = $unsigned(a) >  $signed(`CMP_VALUE);
	output o4_5 = $unsigned(a) == $signed(`CMP_VALUE);
	output o4_6 = $unsigned(a) != $signed(`CMP_VALUE);

	// ########################

	output o5_1 = $unsigned(`CMP_VALUE) <= $signed(a);
	output o5_2 = $unsigned(`CMP_VALUE) <  $signed(a);
	output o5_3 = $unsigned(`CMP_VALUE) >= $signed(a);
	output o5_4 = $unsigned(`CMP_VALUE) >  $signed(a);
	output o5_5 = $unsigned(`CMP_VALUE) == $signed(a);
	output o5_6 = $unsigned(`CMP_VALUE) != $signed(a);

	output o6_1 = $signed(a) <= $unsigned(`CMP_VALUE);
	output o6_2 = $signed(a) <  $unsigned(`CMP_VALUE);
	output o6_3 = $signed(a) >= $unsigned(`CMP_VALUE);
	output o6_4 = $signed(a) >  $unsigned(`CMP_VALUE);
	output o6_5 = $signed(a) == $unsigned(`CMP_VALUE);
	output o6_6 = $signed(a) != $unsigned(`CMP_VALUE);

	// ########################

	output o7_1 = $signed(`CMP_VALUE) <= $signed(a);
	output o7_2 = $signed(`CMP_VALUE) <  $signed(a);
	output o7_3 = $signed(`CMP_VALUE) >= $signed(a);
	output o7_4 = $signed(`CMP_VALUE) >  $signed(a);
	output o7_5 = $signed(`CMP_VALUE) == $signed(a);
	output o7_6 = $signed(`CMP_VALUE) != $signed(a);

	output o8_1 = $signed(a) <= $signed(`CMP_VALUE);
	output o8_2 = $signed(a) <  $signed(`CMP_VALUE);
	output o8_3 = $signed(a) >= $signed(`CMP_VALUE);
	output o8_4 = $signed(a) >  $signed(`CMP_VALUE);
	output o8_5 = $signed(a) == $signed(`CMP_VALUE);
	output o8_6 = $signed(a) != $signed(`CMP_VALUE);
endmodule
