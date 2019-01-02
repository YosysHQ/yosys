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
endmodule
