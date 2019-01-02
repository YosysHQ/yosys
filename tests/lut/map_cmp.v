module top(...);
	input [3:0] a;

	output o1_1 = 4'b1010 <= a;
	output o1_2 = 4'b1010 <  a;
	output o1_3 = 4'b1010 >= a;
	output o1_4 = 4'b1010 >  a;
	output o1_5 = 4'b1010 == a;
	output o1_6 = 4'b1010 != a;

	output o2_1 = a <= 4'b1010;
	output o2_2 = a <  4'b1010;
	output o2_3 = a >= 4'b1010;
	output o2_4 = a >  4'b1010;
	output o2_5 = a == 4'b1010;
	output o2_6 = a != 4'b1010;

	output o3_1 = 4'sb0101 <= $signed(a);
	output o3_2 = 4'sb0101 <  $signed(a);
	output o3_3 = 4'sb0101 >= $signed(a);
	output o3_4 = 4'sb0101 >  $signed(a);
	output o3_5 = 4'sb0101 == $signed(a);
	output o3_6 = 4'sb0101 != $signed(a);

	output o4_1 = $signed(a) <= 4'sb0000;
	output o4_2 = $signed(a) <  4'sb0000;
	output o4_3 = $signed(a) >= 4'sb0000;
	output o4_4 = $signed(a) >  4'sb0000;
endmodule
