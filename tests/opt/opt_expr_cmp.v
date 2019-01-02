module top(...);
  input [3:0] a;

  output o1_1 = 4'b0000 >  a;
  output o1_2 = 4'b0000 <= a;
  output o1_3 = 4'b1111 <  a;
  output o1_4 = 4'b1111 >= a;
  output o1_5 = a <  4'b0000;
  output o1_6 = a >= 4'b0000;
  output o1_7 = a >  4'b1111;
  output o1_8 = a <= 4'b1111;

  output o2_1 = 4'sb0000 >  $signed(a);
  output o2_2 = 4'sb0000 <= $signed(a);
  output o2_3 = $signed(a) <  4'sb0000;
  output o2_4 = $signed(a) >= 4'sb0000;

  output o3_1 = 4'b0100 >  a;
  output o3_2 = 4'b0100 <= a;
  output o3_3 = a <  4'b0100;
  output o3_4 = a >= 4'b0100;

  output o4_1 = 5'b10000 >  a;
  output o4_2 = 5'b10000 >= a;
  output o4_3 = 5'b10000 <  a;
  output o4_4 = 5'b10000 <= a;
  output o4_5 = a <  5'b10000;
  output o4_6 = a <= 5'b10000;
  output o4_7 = a >  5'b10000;
  output o4_8 = a >= 5'b10000;

  output o5_1 = 5'b10100 >  a;
  output o5_2 = 5'b10100 >= a;
  output o5_3 = 5'b10100 <  a;
  output o5_4 = 5'b10100 <= a;
  output o5_5 = a <  5'b10100;
  output o5_6 = a <= 5'b10100;
  output o5_7 = a >  5'b10100;
  output o5_8 = a >= 5'b10100;
endmodule
