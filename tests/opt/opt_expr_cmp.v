module top(...);
  input [3:0] a;
  output o1 = 4'b0000 >  a;
  output o2 = 4'b0000 <= a;
  output o3 = 4'b1111 <  a;
  output o4 = 4'b1111 >= a;
  output o5 = a <  4'b0000;
  output o6 = a >= 4'b0000;
  output o7 = a >  4'b1111;
  output o8 = a <= 4'b1111;
endmodule
